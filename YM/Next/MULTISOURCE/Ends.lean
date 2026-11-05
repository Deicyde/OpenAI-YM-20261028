import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.GradeHelp

/-! one support test making arbitrary wrap-spanning jets. Norm DOES pay all that space here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice MeasureTheory Marker Filter Function Finset Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {P : BudgetPoint} {G : Gauge} {n : Side}

structure SimpleBound (P : BudgetPoint) (ℓ b : ℝ) (F : Config G n → ℂ) : Prop where
  hom : Continuous F
  sym : GaugeInvariant F
  bounded : uniform P ℓ b F

section
variable {P : BudgetPoint} {ℓ a b : ℝ} {F H : Config G n → ℂ}
lemma SimpleBound.expand (h : SimpleBound P ℓ a F) (hx : a ≤ b) : SimpleBound P ℓ b F :=
  ⟨h.hom,h.sym,enlarged h.bounded hx⟩
lemma SimpleBound.const (P : BudgetPoint) (ℓ : ℝ) (x : ℂ) : SimpleBound P ℓ ‖x‖ (fun _ : Config G n => x) :=
  ⟨continuous_const,fun _ _ => rfl, LeftBound.const zero_le_one _⟩
lemma SimpleBound.sub (h : SimpleBound P ℓ a F) (he : SimpleBound P ℓ b H) :
    SimpleBound P ℓ (a+(2^P.order * ‖(-1:ℂ)‖ * b)) (fun x => F x-H x) := by
  have hv : (fun x => F x-H x)=(fun x => F x + (-1)*H x) := by ext; simp [sub_eq_add_neg]
  rw [hv]; exact ⟨by have := h.hom; have := he.hom; fun_prop,fun i U => by rw [h.sym,he.sym],
    h.bounded.add ((LeftBound.const (k:=P.order) zero_le_one _).mul he.bounded zero_le_one)⟩
lemma SimpleBound.add (h : SimpleBound P ℓ a F) (he : SimpleBound P ℓ b H) : SimpleBound P ℓ (a+b) (fun x => F x+H x) :=
    ⟨h.hom.add he.hom, fun j U => by rw [h.sym,he.sym], h.bounded.add he.bounded⟩
lemma SimpleBound.mul (h : SimpleBound P ℓ a F) (he : SimpleBound P ℓ b H) :
    SimpleBound P ℓ (2^P.order*a*b) (fun x => F x*H x) :=
    ⟨h.hom.mul he.hom,fun i U => by rw [h.sym,he.sym], h.bounded.mul he.bounded zero_le_one⟩
lemma prods (P : BudgetPoint) (ℓ b : ℝ) {J : Type*} (s : Finset J) : ∃ c,∀ f : J → Config G n → ℂ,
    (∀ i,SimpleBound P ℓ b (f i)) → SimpleBound P ℓ c (fun x => ∏ i∈s,f i x) := by
  induction s using Finset.induction with
  | empty => refine ⟨‖(1:ℂ)‖,fun _ _ => ?_⟩; simp only [Finset.prod_empty]; exact SimpleBound.const ..
  | insert i s hi ih =>
    obtain ⟨a,ha⟩ := ih; refine ⟨2^P.order*b*a,fun f hv => ?_⟩; simp only [prod_insert hi]; exact (hv i).mul (ha _ hv)
lemma sums (P : BudgetPoint) (ℓ : ℝ) {J : Type*} (s : Finset J) (f : J → Config G n→ℂ) {g : J→ℝ}
    (h : ∀ i,SimpleBound P ℓ (g i) (f i)) : SimpleBound P ℓ (∑ i∈s,g i) (fun x => ∑ i∈s,f i x) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; simpa using SimpleBound.const P ℓ (n:=n) (G:=G) 0
  | insert i s hi ih => simp only [Finset.sum_insert hi]; exact (h i).add ih
end

def recept (P : BudgetPoint) (F U : Config G n→ℂ) := ∀ x, flags P.threshold x=∅ → F x=U x

lemma haloed (P : BudgetPoint) : ∃ ℓ, 0 ≤ ℓ ∧ ∀ x (d : Directions G n),P.dirBound x d → ‖d‖≤ℓ := by
  let q (x : Site n) (e : Edge (Site n)) := P.threshold * (1+(separation e.1 x:ℝ))^P.power
  let v := ∑ x : Site n,∑ e : Edge (Site n), |q x e|
  have hv : 0 ≤ v := by unfold v; positivity
  refine ⟨v,hv,fun x d hd => (pi_norm_le_iff_of_nonneg hv).mpr fun e => ?_⟩
  exact (hd e).trans ((le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (q x i))
    (mem_univ e)).trans (Finset.single_le_sum (fun x _ => (Finset.sum_nonneg (s:=univ) (fun i _ => abs_nonneg (q x i)))) (mem_univ x))))

lemma simple_all {V : Type} [Fintype V] [DecidableEq V] (R : Census V) (P : Rep G n) (D : V → Pulse G n) (U : Config G n)
    (h : flags P.p.threshold U=∅) (t : R.Mode) : jet P R D t U=(P.eval U:ℂ)*∏ i∈t.val,(D i).1 U := by
  have he : Pack.clears (flags P.p.threshold U)={∅} := by
    ext i; simp only [Pack.clears,h,mem_filter,mem_univ,true_and,mem_singleton]; constructor
    · intro ⟨_,hp⟩; by_contra hi
      obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hi
      obtain ⟨a,ha⟩ := j.property.1
      exact notMem_empty _ (hp ▸ mem_biUnion.mpr ⟨j,hj,ha⟩)
    rintro rfl; simp
  unfold jet polar composeAt Rep.eval; rw [he, sum_singleton, prod_empty, mul_one, P.activities.gas_one _ h,
    mul_one, Poly.part_smul, lambda]
  have he := pass_sum_send (R:=R) univ (Hot.one R) (fun i => (D i).1 U)
  simp only [Hot.one] at he; rw [he,polynomial]
end YM.Multi.Step
