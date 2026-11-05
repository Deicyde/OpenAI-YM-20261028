import Mathlib.RingTheory.Nilpotent.Exp
import YM.Push.CORRECTED_COLUMNS.Program
/-!
# Coefficientwise absolute profiles for inflation

In particular pay the number of coefficients, not just a bound on
weighted price at a *common* U. Used when building new K witnesses
after inserting h_i failed-mask factors on the same configuration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Width
open MeasureTheory Function Set Filter Marker
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {V : Type*} [DecidableEq V] {R : Census V}

-- y majorant lives in the same poly type (nonnegative real entries).
def Covered (x y : Poly R) := ∀ i : R.Mode, (‖x.part i‖:ℝ) ≤ (y.part i).re ∧ (y.part i).im=0


lemma Covered.norm {x y : Poly R} (h : Covered x y) (i) : ‖y.part i‖=(y.part i).re := by
  have hq : (↑(y.part i).re:ℂ)=y.part i := Complex.ext rfl (h i).2.symm
  rw [←hq,Complex.norm_real,Real.norm_of_nonneg ((norm_nonneg _).trans (h i).1),Complex.ofReal_re]
lemma Covered.reprice {x y : Poly R} (h : Covered x y) (w : V → ℝ) (hw : ∀ i, 0 < w i) : Poly.price w x≤Poly.price w y :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((h i).1.trans_eq (h.norm i).symm) (Poly.worth hw i).le
lemma Covered.zero {x y : Poly R} (h : Covered x y) : Covered 0 y :=
    fun i => ⟨by simp only [Poly.part_nil,norm_zero]; exact (norm_nonneg _).trans (h i).1,(h i).2⟩
def up (x : Poly R) := Poly.inject fun i => (‖x.part i‖:ℂ)
lemma shelter (x : Poly R) : Covered x (up x) := fun _ => ⟨le_rfl,rfl⟩
lemma shelter_same (x : Poly R) (w : V → ℝ) : Poly.price w (up x) = Poly.price w x :=
  Finset.sum_congr rfl (fun i _ => congr_arg (fun y => Poly.toll w i * y) (by
    change ‖(‖x.part i‖:ℂ)‖=‖x.part i‖; simp))

lemma Covered.multiply {F G X Y : Poly R} (h : Covered F X) (t : Covered G Y) : Covered (F*G) (X*Y) := by
  intro s; simp only [Poly.part_mul,Complex.re_sum,Complex.im_sum]
  constructor
  · apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro j _
    split
    · simp only [norm_mul, Complex.mul_re, (h _).2,(t _).2,zero_mul,sub_zero];
      exact mul_le_mul (h i).1 (t j).1 (norm_nonneg _) ((norm_nonneg _).trans (h i).1)
    rw [norm_zero]; exact le_rfl
  apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
  split
  · simp only [Complex.mul_im,(h _).2,(t _).2,mul_zero,zero_mul,add_zero]
  rfl

lemma bulk {ι : Type*} (s : Finset ι) {F H : ι → Poly R} (h : ∀ i ∈ s, Covered (F i) (H i)) :
    Covered (∏ i ∈ s, F i) (∏ i∈s,H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; intro i; simp only [Poly.one_part]; split <;> simp
  | insert i s hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).multiply (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

open Lattice Wilson RG
variable {G : Gauge} {n : Side}

/-- With actual nonempty supports. Rooted via full final flags, at every
nonconstant marker. -/
structure LocalCharge (p : BudgetPoint) (a : V → Site n) (X : Support n) (F : Config G n → Poly R) : Prop where
    gauge : GaugeInvariant F
    borel : Measurable F
    reads : UsesFinal p.threshold X F
    carry (U i) : (F U).part i ≠ 0 → ∀ v∈i.val, a v∈ X

section
variable {p : BudgetPoint} {a : V → Site n} {X Y : Support n} {F H : Config G n → Poly R}

lemma LocalCharge.widen (h : LocalCharge p a X F) (H : X⊆Y) : LocalCharge p a Y F where
  gauge := h.gauge
  borel := h.borel
  reads U W ht hv := h.reads U W (agrees_mono ht H) (by
    classical
    calc X∩flags p.threshold U = X∩(Y∩flags p.threshold U) := by rw [←Finset.inter_assoc,Finset.inter_eq_left.mpr H]
         _ = X∩(Y∩flags p.threshold W) := by rw [hv]
         _ = X∩flags p.threshold W := by rw [←Finset.inter_assoc,Finset.inter_eq_left.mpr H])
  carry U i he v hh := H (h.carry _ _ he _ hh)

lemma LocalCharge.mulCharges (h : LocalCharge p a X F) (t : LocalCharge p a X H) : LocalCharge p a X (F*H) where
  gauge θ U := congr_arg₂ HMul.hMul (h.gauge θ U) (t.gauge θ U)
  borel := h.borel.mul t.borel
  reads U Y hv hx := congr_arg₂ HMul.hMul (h.reads U Y hv hx) (t.reads U Y hv hx)
  carry U i hv v hV := by
    rw [Pi.mul_apply,Poly.part_mul] at hv
    by_contra ht; apply hv; apply Finset.sum_eq_zero; intro x _; refine Finset.sum_eq_zero fun y _ => ?_
    split
    · rename_i he; rw [← he.2] at hV
      rcases Finset.mem_union.mp hV with hP|hP
      · rw [show (F U).part x=0 from by_contra fun w => ht (h.carry _ _ w _ hP),zero_mul]
      rw [show (H U).part y=0 from by_contra fun w => ht (t.carry _ _ w _ hP),mul_zero]
    rfl

lemma product_local {ι} (s : Finset ι) (f : ι → Config G n → Poly R) (h : ∀ i∈s, LocalCharge p a X (f i)) :
    LocalCharge p a X (fun U => ∏ i∈s,f i U) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    refine ⟨fun _ _ => rfl, measurable_const, fun _ _ _ _ => rfl, ?_⟩
    intro U i hi v hv
    by_cases h : i=R.quiet
    · subst i; exact absurd hv (by simp [Census.quiet])
    exact False.elim (hi (by simp only [Poly.one_part,if_neg h]))
  | insert i s hi ih => simp_rw [Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).mulCharges (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))
end
end YM.Push.Corrected.Width
