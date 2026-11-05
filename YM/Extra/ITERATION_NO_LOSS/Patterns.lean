import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Work.F03.Transport

/-!
# Linear curvature readings with slot differences, before channel averaging
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Lattice Wilson RG Exterior Precision Function
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {k : ℕ}

/-- Components in the real counting color basis. -/
abbrev Flux (G : Gauge) (n : Side) := PlaqAxes → G.ColorIndex → Site n → ℝ

def flux (a : Bid.Dir G n) : Flux G n := fun b j x => Work.F03.faceCurl (x,b) a j

def grad (i : Axis) (f : Site n → ℝ) (x : Site n) := f (x+step i) - f x

def read (i : Option Axis) (f : Site n → ℝ) := i.elim f (fun a => grad a f)

structure Pattern (G : Gauge) (k : ℕ) where
  op : Fin k → Option Axis
  atom : Atom G k

def plain (a : Atom G k) : Pattern G k := ⟨fun _ => none,a⟩
def both (a : Pattern G 2) := ∀ i, (a.op i).isSome

def Pattern.sample (a : Pattern G k) (V : Flux G n) (x : Site n) := ∑ b, a.atom.coeff b *
    ∏ i, read (a.op i) (V (a.atom.leg i).plaq (b i)) (x + wrap n (a.atom.leg i).offset)

variable {ι : Type*}
def total (E : ι → Pattern G k) (V : Flux G n) := ∑' e, ∑ x, (E e).sample V x

lemma sample_est {σ C : ℝ} (E : ι → Pattern G k) (V : Flux G n) (hs : 0 ≤ σ) (hE : Charged (fun i => (E i).atom) σ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, SumBudget (fun i => |(E i).sample V x|) B := by
  let D := ∑ j : PlaqAxes, ∑ b : G.ColorIndex, ∑ x : Site n, |V j b x|
  have hv j b x : |V j b x| ≤ D := calc
    _ ≤ ∑ x,|V j b x| := Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
    _ ≤ ∑ b,∑ x, |V j b x| := Finset.single_le_sum (f:=fun b => ∑ x : Site n, |V j b x|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    _ ≤ _ := Finset.single_le_sum (f:=fun j => ∑ b : G.ColorIndex,∑ x : Site n, |V j b x|) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hd : 0 ≤ D := Finset.sum_nonneg fun _ _ => by positivity
  have hw (i : Option Axis) j b x : |read i (V j b) x| ≤ D+D := by
    cases i with
    | none => exact (hv j b x).trans (le_add_of_nonneg_right hd)
    | some c => exact (abs_sub _ _).trans (add_le_add (hv j b _) (hv j b x))
  have he (i x) : |(E i).sample V x| ≤ (E i).atom.magnitude * (D+D)^k := by
    unfold Pattern.sample Atom.magnitude; rw [Finset.sum_mul]; apply le_trans (Finset.abs_sum_le_sum_abs ..)
    refine Finset.sum_le_sum fun b _ => ?_
    rw [abs_mul, Finset.abs_prod]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa using Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hw _ _ (b i) _)
  have hk : SumBudget (fun i => (E i).atom.magnitude) C := by simpa [Charged,Atom.budget] using hE.mono hs le_rfl
  have ht := Cost.scale' hk ((D+D)^k) (by positivity)
  exact ⟨_,Cost.nonneg ht,fun x => Cost.mono ht (fun i => abs_nonneg _) (fun i => he i x)⟩

lemma sample_summable {σ C : ℝ} (E : ι → Pattern G k) (V : Flux G n) (hs : 0 ≤ σ)
    (hE : Charged (fun i => (E i).atom) σ C) (x : Site n) : Summable (fun i => (E i).sample V x) :=
  .of_abs ((sample_est E V hs hE).choose_spec.2 x).2.1
lemma net_summable {σ C : ℝ} (E : ι → Pattern G k) (V : Flux G n) (hs : 0 ≤ σ)
    (hE : Charged (fun i => (E i).atom) σ C) : Summable (fun i => ∑ x, (E i).sample V x) :=
  summable_sum fun x _ => sample_summable E V hs hE x

lemma plain_flux (a : Atom G k) (v : Bid.Dir G n) (x : Site n) : (plain a).sample (flux v) x =
    a.poly (fun j => Work.F03.faceCurl (Work.F03.slotFace (a.leg j) x) v) := by
  simp_rw [Pattern.sample,Atom.poly,read,plain,Option.elim,flux,Work.F03.slotFace,add_comm x]

lemma total_flux (a : ℕ → Atom G k) (v : Bid.Dir G n) {σ C : ℝ} (hs : 0 ≤ σ) (h : Charged a σ C) :
    total (fun i => plain (a i)) (flux v) = ∑ x : Site n, ∑' i, (a i).poly
      (fun j => Work.F03.faceCurl (Work.F03.slotFace ((a i).leg j) x) v) := by
  unfold total
  rw [Summable.tsum_finsetSum (fun x _ => sample_summable _ _ hs (show Charged (fun i => (plain (a i)).atom) σ C from h) x)]
  simp only [plain_flux]



/-- Always enumerable, even if there are no terms. Paths retained; extra addresses can still matter downstream. -/
def padded [Countable ι] (a : ι → Atom G k) : ℕ → Atom G k := Sum.elim a (fun _ : ℕ => blank G k) ∘ numbering _
lemma padded_cost [Countable ι] {a : ι → Atom G k} {σ C : ℝ} (h : Charged a σ C) : Charged (padded a) σ C := by
  have he := Cost.equiv (numbering (ι ⊕ ℕ)) (Cost.sum (f:=fun i => ((Sum.elim a (fun _ => blank G k)) i).budget σ)
    h (blank_cost σ))
  rw [add_zero] at he; exact he
lemma padded_silent [Countable ι] {a : ι → Atom G 2} (h : Silent a) : Silent (padded a) := by
  intro i b
  let f := Sum.elim a (fun _ : ℕ => blank G 2)
  let e := numbering (ι ⊕ ℕ)
  have h0 := HasSum.sum (f:=fun p => charge (f p) i b) (h i b).1 (blank_silent i b).1
  have h1 (l : Axis) := HasSum.sum (f:=fun p => charge (f p) i b * delta (f p) l) ((h i b).2 l) ((blank_silent i b).2 l)
  simp only [zero_add] at h0 h1
  exact ⟨(e.hasSum_iff (f:=fun p => charge (f p) i b)).2 h0,fun l =>
    (e.hasSum_iff (f:=fun p => charge (f p) i b * delta (f p) l)).2 (h1 l)⟩
lemma padded_sym [Countable ι] {a : ι → Atom G k} (ha : SymmetricAtoms a) : SymmetricAtoms (padded a) := by
  intro i; unfold padded comp; cases numbering (ι ⊕ ℕ) i <;> [apply ha; exact blank_sym]
lemma total_padded [Countable ι] {a : ι → Atom G k} {σ C : ℝ} (h : Charged a σ C) (hs : 0 ≤ σ) (V : Flux G n) :
    total (plain ∘ padded a) V = total (plain ∘ a) V := by
  let f (i : ι ⊕ ℕ) := ∑ x, (plain (Sum.elim a (fun _ => blank G k) i)).sample V x
  calc
    _ = ∑' i, f i := (numbering _).tsum_eq f
    _ = total (plain ∘ a) V + ∑' i : ℕ, f (.inr i) := Summable.tsum_sum (f:=f) (net_summable (plain ∘ a) _ hs h)
      (net_summable (fun _ => plain (blank G k)) _ hs (blank_cost _))
    _ = _ := by simp [f,Pattern.sample,plain,blank]
end YM.Extra.Iteration
