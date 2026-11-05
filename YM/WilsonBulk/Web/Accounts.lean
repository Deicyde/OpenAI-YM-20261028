import YM.Pert.Bulk.UseRows
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered coefficient tables, rooted size on the *original* mesh

We use `Fin n` for leg labels, including both possible orientations/colors in the
point type only if the application dictates. This allows mixed fine (residue, link)
and coarse variables at a single conditioning mesh. Coefficient (tensor)
normalization is *without* applying derivatives here; spectra and curvature adapters
will use the leading scalar coefficients. Symmetry means just invariance under
leg permutations for now. Budget realized via ENNReal, with conversion to the
full `SumBudget` and the accepted `Pert.Bulk.Folded`.

No budget on rank zero: going to cover discards the scalar unmarked vacuum
explicitly, and insertions at rank zero in *field* use also their insertion slot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical ENNReal BigOperators Topology
open Function Equiv Lattice Pert.Bulk

variable {X Y Z α β γ : Type} {k n m : ℕ} {σ θ p q b : ℝ}

abbrev Legs (X : Type) (n : ℕ) := Fin n → X
abbrev Page (X : Type) (n : ℕ) := Legs X n → ℝ
abbrev Text (α : Type) (n : ℕ) := Page (Market α) n

section tuples

-- lean off-diagonal arithmetic throughout these interfaces
abbrev hitch (x : X) (v : Legs X n) : Legs X (n+1) := Fin.cons x v
abbrev crop (v : Legs X (n+1)) : Legs X n := fun i => v i.succ
abbrev snip (k m : ℕ) (v : Legs X (k+m)) : Legs X k := v ∘ (Fin.castAdd m)
abbrev keep (k m : ℕ) (v : Legs X (k+m)) : Legs X m := v ∘ (Fin.natAdd k)
abbrev two (x y : X) : Legs X 2 := hitch x (fun _=> y)
abbrev pair (f : X→ X→ℝ) : Page X 2 := fun v=> f (v 0) (v 1)

@[simp] theorem hitch_zero (x : X) (v : Legs X n) : hitch x v 0=x := Fin.cons_zero ..
@[simp] theorem hitch_succ (x : X) (v : Legs X n) (i : Fin n) : hitch x v i.succ=v i := Fin.cons_succ ..
@[simp] theorem hitch_crop (v : Legs X (n+1)) : hitch (v 0) (crop v)=v := Fin.cons_self_tail v
@[simp] theorem crop_hitch (x : X) (v : Legs X n) : crop (hitch x v)=v := funext fun _=> hitch_succ ..
@[simp] theorem snip_append (a : Legs X k) (b : Legs X m) : snip k m (Fin.append a b)=a := funext fun _=> Fin.append_left ..
@[simp] theorem keep_append (a : Legs X k) (b : Legs X m) : keep k m (Fin.append a b)=b := funext fun _=> Fin.append_right ..
@[simp] theorem append_back (v : Legs X (k+m)) : Fin.append (snip k m v) (keep k m v) = v := by
  ext1 i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · rw [Fin.append_left]; rfl
  rw [Fin.append_right]; rfl

@[simp] theorem hitch_comp (f : X→Y) (x : X) (v : Legs X n) : f ∘ hitch x v = hitch (f x) (f ∘ v) := by
  funext i; cases i using Fin.cases <;> simp
@[simp] theorem crop_comp (f : X→Y) (v : Legs X (n+1)) : crop (f ∘ v) = f ∘ crop v := rfl
@[simp] theorem snip_comp (f : X→Y) (v : Legs X (k+m)) : snip k m (f ∘ v) = f ∘ snip k m v := rfl
@[simp] theorem keep_comp (f : X→Y) (v : Legs X (k+m)) : keep k m (f ∘ v) = f ∘ keep k m v := rfl
@[simp] theorem append_comp (f : X→Y) (a : Legs X k) (b : Legs X m) : f ∘ Fin.append a b = Fin.append (f ∘ a) (f ∘ b) := by
  ext1 i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp

theorem leg1 (v : Legs X 1) : v = fun _=> v 0 := funext fun i=> by rw [Fin.fin_one_eq_zero i]
theorem legs_succ (Q : Legs X (n+1) → Prop) (h : ∀ x v, Q (hitch x v)) : ∀ v,Q v := fun v => hitch_crop v ▸ h _ _
theorem legs_plus (Q : Legs X (k+n) → Prop) (h : ∀ a : Legs X k, ∀ b : Legs X n, Q (Fin.append a b)) : ∀ v,Q v := fun v => append_back v ▸ h _ _

def hitchEquiv (X : Type) (n : ℕ) : X × Legs X n ≃ Legs X (n+1) where
  toFun v := hitch v.1 v.2
  invFun v := (v 0,crop v)
  left_inv _ := by simp
  right_inv := hitch_crop

def halves (X : Type) (k m : ℕ) : (Legs X k × Legs X m) ≃ Legs X (k+m) where
  toFun v := Fin.append v.1 v.2
  invFun v := (snip k m v, keep k m v)
  left_inv _ := by simp
  right_inv := append_back

lemma ts_hitch (f : Legs X (n+1) → ℝ≥0∞) : ∑' v, f v = ∑' x,∑' v : Legs X n, f (hitch x v) :=
  ((hitchEquiv X n).tsum_eq f).symm.trans (ENNReal.tsum_prod (f:=fun x v=> f (hitch x v)))
lemma ts_plus (f : Legs X (k+n) → ℝ≥0∞) : ∑' v, f v = ∑' a : Legs X k,∑' b : Legs X n, f (Fin.append a b) :=
  ((halves X k n).tsum_eq f).symm.trans (ENNReal.tsum_prod (f:=fun (a : Legs X k) (b : Legs X n)=> f (Fin.append a b)))

def escort (e : Fin m ≃ Fin n) (u : Page X m) : Page X n := fun v => u (v ∘ (e:Fin m→Fin n))
def casesEquiv (e : Fin m ≃ Fin n) (u : X ≃ Y) : Legs X m ≃ Legs Y n := Equiv.arrowCongr e u
theorem casesEquiv_apply (e : Fin m≃Fin n) (u : X≃Y) (v : Legs X m) : casesEquiv e u v= u ∘ v ∘ e.symm := rfl

@[simp] lemma escort_zero (e : Fin m≃Fin n) : escort e (0:Page X m)=0 := rfl
@[simp] lemma escort_plus (e : Fin m ≃ Fin n) (a b : Page X m) : escort e (a+b)= escort e a + escort e b := rfl
@[simp] lemma escort_minus (e : Fin m ≃ Fin n) (a b : Page X m) : escort e (a-b)= escort e a - escort e b := rfl
@[simp] lemma escort_neg (e : Fin m ≃ Fin n) (a : Page X m) : escort e (-a)= -escort e a := rfl
@[simp] lemma escort_scale (e : Fin m ≃ Fin n) (r : ℝ) (a : Page X m) : escort e (r • a)= r • escort e a := rfl
lemma escort_escort (e : Fin m ≃ Fin k) (f : Fin k ≃ Fin n) (a : Page X m) : escort f (escort e a) = escort (e.trans f) a := rfl
lemma escort_sum {T : Type} (s : Finset T) (a : T→Page X m) (e : Fin m≃Fin n) :
    escort e (∑ x ∈ s,a x)= ∑ x∈s,escort e (a x) := by ext1 v; simp [escort]

end tuples

/-- One pseudometric shared by the finite coordinate alphabets. -/
structure Rule (X : Type) where
  cost : X→ X→ℝ
  self (x : X) : cost x x=0
  nonneg (x y : X) : 0 ≤ cost x y
  swap (x y : X) : cost x y=cost y x
  tri (x y z : X) : cost x z ≤ cost x y + cost y z

def lawn (α : Type) : Rule (Market α) where
  cost x y := sep x.1 y.1
  self _ := sep_self _
  nonneg _ _ := sep_nonneg ..
  swap _ _ := sep_comm ..
  tri _ _ _ := sep_triangle ..

def run (D : Rule X) (x : X) (v : Legs X n) := ∑ i, D.cost x (v i)
lemma run_nonneg (D : Rule X) (x : X) (v : Legs X n) : 0≤run D x v := Finset.sum_nonneg (fun _ _ => D.nonneg ..)
lemma run_zero (D : Rule X) (x : X) (v : Legs X 0) : run D x v=0 := by simp [run]
lemma run_pair (D : Rule X) (x y z : X) : run D x (two y z)=D.cost x y+D.cost x z := by
  simp [run,two,Fin.sum_univ_succ]
lemma run_left (D : Rule X) (x : X) (v : Legs X n) (a : Fin n) : D.cost x (v a) ≤ run D x v :=
  Finset.single_le_sum (f:=fun i=> D.cost x (v i)) (fun _ _=> D.nonneg ..) (Finset.mem_univ a)
lemma run_escort (D : Rule X) (e : Fin m≃ Fin n) (x : X) (v : Legs X n) :
    run D x (v ∘ (e:Fin m→Fin n))= run D x v := Equiv.sum_comp e (fun i=> D.cost x (v i))
lemma run_joint (D : Rule X) (x : X) (a : Legs X k) (b : Legs X m) : run D x (Fin.append a b)=run D x a+run D x b := by
  simp only [run,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
lemma run_some (D : Rule X) (x y : X) (v : Legs X n) : run D x (hitch y v)=D.cost x y+run D x v := by simp only [run,Fin.sum_univ_succ,hitch_zero,hitch_succ]
lemma run_move (D : Rule X) (x y : X) (v : Legs X n) : run D x v ≤ (n:ℝ)*D.cost x y + run D y v := by
  unfold run
  calc _ ≤ ∑ i, (D.cost x y+D.cost y (v i)) := Finset.sum_le_sum (fun _ _ => D.tri ..)
       _ = _ := by simp [Finset.sum_add_distrib,nsmul_eq_mul]

/-- Raw per-root charge realization. Height includes nonnegative budget
(converting from an ENNReal inequality alone doesn't). Width positivity is
imposed separately only at operations that use it. -/
def rent (D : Rule X) (σ : ℝ) (u : Page X n) (i : Fin n) (x : X) :=
    ∑' v, if v i=x then bill (u v) (σ*run D x v) else 0
-- not collide with Stationary.rent. All users have namespace.
def Within (D : Rule X) (σ : ℝ) (p : ℝ) (u : Page X n) : Prop :=
    0 ≤ p ∧ ∀ i x,rent D σ u i x ≤ ENNReal.ofReal p

variable {D : Rule X} {u v w : Page X n}

def fee (D : Rule X) (σ : ℝ) (u : Page X n) (i : Fin n) (x : X) : Legs X n → ℝ := fun v =>
    if v i=x then |u v| * Real.exp (σ*run D x v) else 0
lemma fee_nonneg (v : Legs X n) (i : Fin n) (x : X) : 0 ≤ fee D σ u i x v := by unfold fee; split <;> positivity
lemma lease_eq (v : Legs X n) (i : Fin n) (x : X) :
    ENNReal.ofReal (fee D σ u i x v) = if v i=x then bill (u v) (σ*run D x v) else 0 := by unfold fee; split <;> simp [bill]
theorem within_budget (hp : 0≤p) : Within D σ p u ↔ ∀ i x, RG.SumBudget (fee D σ u i x) p := by
  have e i x : (∑' v, ENNReal.ofReal (fee D σ u i x v)) = rent D σ u i x := tsum_congr fun v => lease_eq v i x
  constructor
  · intro h i x
    have hh : (∑' v, ENNReal.ofReal (fee D σ u i x v)) ≤ ENNReal.ofReal p := (e i x).le.trans (h.2 i x)
    have ht : Summable (fee D σ u i x) := (ENNReal.summable_toReal (ne_top_of_le_ne_top (by finiteness) hh)).congr (fun v => ENNReal.toReal_ofReal (fee_nonneg v i x))
    exact ⟨(fee_nonneg · i x), ht, ENNReal.ofReal_le_ofReal_iff hp |>.1 ((ENNReal.ofReal_tsum_of_nonneg (fee_nonneg · i x) ht).le.trans hh)⟩
  intro h; refine ⟨hp,fun i x => ?_⟩
  exact (e i x).ge.trans ((ENNReal.ofReal_tsum_of_nonneg (h i x).1 (h i x).2.1).ge.trans (by exact ENNReal.ofReal_le_ofReal (h i x).2.2))

theorem within_entry' (h : Within D σ p u) (i : Fin n) (v : Legs X n) :
    |u v| * Real.exp (σ*run D (v i) v) ≤ p := by
  have he := (within_budget h.1).1 h i (v i)
  have hk := ((he.2.1).le_tsum v (fun w _=> fee_nonneg w i (v i))).trans he.2.2
  simpa only [fee,↓reduceIte] using hk

theorem within_total {n : ℕ} {u : Page X n} (h : Within D σ p u) (he : 0 ≤ σ) (i : Fin n) (x : X) :
    Summable (fun v : Legs X n => if v i=x then u v else 0) := by
  apply Summable.of_norm_bounded ((within_budget h.1).1 h i x).2.1
  intro v; unfold fee; split_ifs
  · exact (Real.norm_eq_abs _).le.trans (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg he (run_nonneg ..))))
  simp

theorem within_entry (h : Within D σ p u) (he : 0 ≤ σ) (hn : n ≠ 0) (v : Legs X n) : |u v| ≤ p :=
  (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg he (run_nonneg ..)))).trans (within_entry' h (⟨0,by omega⟩) v)

namespace Within

variable (h : Within D σ p u)
include h
lemma mono (ha : θ ≤ σ) (hb : p ≤ q) : Within D θ q u := by
  refine ⟨h.1.trans hb,fun i x=>?_⟩
  refine LE.le.trans (b:=rent D σ u i x) (ENNReal.tsum_le_tsum (fun a=>?_)) ((h.2 i x).trans (by gcongr))
  split
  · exact bill_mono le_rfl (mul_le_mul_of_nonneg_right ha (run_nonneg ..))
  exact le_rfl
lemma scale (r : ℝ) : Within D σ (|r| * p) (r • u) := by
  refine ⟨mul_nonneg (abs_nonneg _) h.1,fun i x=>?_⟩
  unfold rent
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  calc
    _ = ∑' v, ENNReal.ofReal |r| * (if v i=x then bill (u v) (σ*run D x v) else 0) := by
        apply tsum_congr; intro v; dsimp only [Pi.smul_apply,smul_eq_mul]; split_ifs with H
        · rw [bill_eq, bill_eq, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc];
        exact (mul_zero _).symm
    _ ≤ _ := by rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right (h.2 i x) _
lemma neg : Within D σ p (-u) := by simpa using h.scale (-1)
lemma by_abs {v : Page X n} (h' : ∀ x, |v x| ≤ |u x|) : Within D σ p v := by
  refine ⟨h.1,fun i x=>?_⟩
  refine LE.le.trans ?_ (h.2 i x)
  refine ENNReal.tsum_le_tsum fun a=>?_
  split
  · exact bill_mono (h' _) le_rfl
  exact le_rfl
lemma sub (h' : Within D σ q v) : Within D σ (p+q) (u-v) := by
  refine ⟨add_nonneg h.1 h'.1,fun i x=>?_⟩
  rw [ENNReal.ofReal_add h.1 h'.1]
  apply LE.le.trans ?_ (add_le_add (h.2 i x) (h'.2 i x))
  unfold rent
  rw [← ENNReal.tsum_add]; refine ENNReal.tsum_le_tsum (fun a=>?_)
  split_ifs
  · exact bill_sub ..
  exact (zero_add _).ge
lemma add (h' : Within D σ q v) : Within D σ (p+q) (u+v) := by simpa using h.sub h'.neg
omit h
lemma zero (hp : 0≤p) : Within D σ p (0:Page X n) := ⟨hp, fun i x=> by simp [rent,bill]⟩
lemma sum {T : Type} (s : Finset T) {a : T→Page X n} {p : T→ℝ} (h : ∀ i∈s,Within D σ (p i) (a i)) : Within D σ (∑ i∈s,p i) (∑ i∈s,a i) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact zero le_rfl
  | insert a s h' ih => simpa only [Finset.sum_insert h'] using (h a (Finset.mem_insert_self ..)).add (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
include h
lemma reindex (e : Fin n≃ Fin m) : Within D σ p (escort e u) := by
  refine ⟨h.1,fun j x=>?_⟩
  refine LE.le.trans (Eq.le ?_) (h.2 (e.symm j) x)
  unfold rent; rw [← (casesEquiv e (.refl X)).tsum_eq _]; apply tsum_congr
  intro a
  have hv : escort e u (casesEquiv e (.refl X) a)=u a := by simp [escort,casesEquiv_apply, Function.comp_assoc]
  have ht : run D x (casesEquiv e (.refl X) a) = run D x a := by simpa only [casesEquiv_apply, Equiv.coe_refl,id_comp] using run_escort D e.symm x a
  simp only [hv,ht]; rfl
end Within

lemma rent_head (u : Page X (n+1)) (x : X) : rent D σ u 0 x = ∑' v : Legs X n, bill (u (hitch x v)) (σ*run D x v) := by
  unfold rent; rw [ts_hitch]; simp only [hitch_zero,run_some]; rw [tsum_eq_single x]; simp [D.self]
  intro y hy; simp [hy]
lemma rent_tail (u : Page X (n+1)) (i : Fin n) (x : X) : rent D σ u i.succ x = ∑' y,∑' v : Legs X n, if v i=x then bill (u (hitch y v)) (σ*run D x (hitch y v)) else 0 := by
  unfold rent; rw [ts_hitch]; simp only [hitch_succ]
lemma within_home {v : Text α (n+1)} (h : Within (lawn α) σ p v) : Folded σ (fun x u=>v (hitch x u)) p := by
  intro x
  have hz := h.2 (0:Fin (n+1)) x
  rw [rent_head] at hz
  exact hz

end YM.WilsonBulk.Sheet
