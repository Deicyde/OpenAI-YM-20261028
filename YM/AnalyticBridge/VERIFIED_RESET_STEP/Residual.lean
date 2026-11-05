import YM.AnalyticBridge.VERIFIED_RESET_STEP.Lines
import YM.Next.FREE_KERNELS.Amend
import YM.Push.STRESS_FLUX.Orbits


/-! E:eq:qiFi. Actual operations on each HRGv term and support including
failed indicator discrepancy; no flat subtraction through a `K` boundary. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux UVNext.PricedKernels Next.Scheduling 
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X Y : Support n}

lemma healthy_image (s : Signed) (b : Site n) (t : ℝ) (U : Config G n) :
    Healthy t (X.image (affine s b)) U ↔ Healthy t X (pull s b U) := by
  unfold Healthy; rw [← Work.H03.flags_send s b t U]; exact Finset.disjoint_image (f:=affine s b) (fun _ _ h => s.act_injective (add_right_cancel h))
lemma healthy_mono (h : X ⊆ Y) {t : ℝ} {U : Config G n} (hh : Healthy t Y U) : Healthy t X U := Finset.disjoint_of_subset_left h hh
lemma healthy_reads (t : ℝ) (X Y : Support n) (h : X ⊆ Y) : UsesFinal t Y (Healthy t X (G:=G)) :=
  Work.H03.reads_larger h (fun _ _ _ he => by rw [Healthy, Healthy, Finset.disjoint_iff_inter_eq_empty, he,Finset.disjoint_iff_inter_eq_empty])
lemma uses_of_regular {f : Pot G n} (h : p.Regular X f) : UsesFinal p.threshold X f := fun U V ha _ => h.sites U V ha
lemma pull_one_field (s : Signed) (b : Site n) : pull s b (1:Config G n) = 1 := by funext i; simp [pull,Step.read]

namespace Residual
variable (d : RegularAddress n) (f : Pot G n) (t : ℝ)

def payout := counter (projection d f) d.site (G:=G)
def rebate : Pot G n := (f - fun _ => f 1) - payout d f
def fault (U : Config G n) : ℝ := if Healthy t (expand d) U then 0 else
    f 1 + (if Healthy t {d.site} U then payout d f U else 0) - if Healthy t d.support U then f U else 0

def multiplier (G : Gauge) (p : BudgetPoint) := (2:ℝ)⁻¹ * Fintype.card PlaqAxes * Fintype.card PlaqAxes * (3 * pairBill G p)
lemma multiplier_nonneg (G : Gauge) (p : BudgetPoint) : 0 ≤ multiplier G p := by unfold multiplier; have := pair_nonneg G p; positivity

def resetLoss (G : Gauge) (p : BudgetPoint) := 2 + multiplier G p
lemma loss_pos (G : Gauge) (p : BudgetPoint) : 0 < resetLoss G p := by unfold resetLoss; linarith [multiplier_nonneg G p]

section
variable {f} (hG : G.Simple) (hf : p.Regular d.support f)
include hf
set_option linter.unusedSectionVars false in
lemma payout_regular : p.Regular (expand d) (payout d f) := reg_larger (counter_regular _ _ _) Finset.subset_union_right
include hG in
lemma payout_bill {c : ℝ} (h : p.supBounds d.site d.support f c) : Bill p d.site (Healthy p.threshold {d.site}) (multiplier G p*c)
    (payout d f) := by
  refine Bill.le (counter_bill d.site _ p) ?_
  have he (a b : PlaqAxes) : |projection d f a b| * (pairBill G p*p.threshold^2) ≤ 3*c * pairBill G p := by
    linarith only [mul_le_mul_of_nonneg_right (projection_bound d hG hf h a b) (pair_nonneg G p)]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a (_ : a∈Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b∈Finset.univ) => he a b) (by norm_num)); simp [multiplier]; apply le_of_eq; ring
lemma rebate_regular : p.Regular (expand d) (rebate d f) :=
    reg_sub (reg_sub (reg_larger hf Finset.subset_union_left) (reg_const _)) (payout_regular d hf)
omit hf in
@[simp] lemma rebate_one : rebate d f 1 = 0 := by simp [rebate,payout,counter,quad]
include hG in
lemma rebate_vanish (h : Nonwrapping (expand d) d.site) (hn : 20 < n.val) : ∀ x y, IsAffineDirection d.site x →
    IsAffineDirection d.site y → logHessian (rebate d f) x y = 0 := by
  apply affine_zero (rebate_regular d hf); intro v
  unfold rebate
  have hl := LinearJet.hessian_curl hG hf (o:=d.site) (fun x hx => h x (Finset.mem_union_left _ hx)) (by omega : 4 ≤ n.val)
    (positive_primitive v.positive) (positive_primitive v.positive)
  rw [hessian_sub (reg_sub (reg_larger hf Finset.subset_union_left) (reg_const _)) (payout_regular d hf),
    hessian_sub hf (reg_const _),hessian_zero,sub_zero,payout,counter_diag hG p d.site hn,projection_eq hG hf h,hl,sub_self]

include hG in
lemma rebate_sup {c : ℝ} (h : p.supBounds d.site d.support f c) : p.supBounds d.site (expand d) (rebate d f) (resetLoss G p*c) := by
  have he : |f 1| ≤ c := h.2 1 (flat_ok ..) [] (by simp) (by simp)
  refine sup_le (sup_sub (reg_sub (reg_larger hf Finset.subset_union_left) (reg_const _)) (payout_regular d hf)
    (sup_larger (sup_sub hf (reg_const _) h (sup_const _)) Finset.subset_union_left)
    (Bill.sup (payout_bill d hG hf h) (fun _ => healthy_mono (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ d.anchor))))) ?_
  unfold resetLoss; linarith

omit hf in
lemma visits {U : Config G n} (h : fault d f t U ≠ 0) : ¬ Healthy t (expand d) U := fun he => h (if_pos he)
lemma fault_meas : Measurable (fault d f t) :=
    Measurable.ite (healthy_closed ..).measurableSet measurable_const ((measurable_const.add (Measurable.ite (healthy_closed ..).measurableSet
      (payout_regular d hf).borel measurable_const)).sub (Measurable.ite (healthy_closed ..).measurableSet hf.borel measurable_const))
lemma fault_gauge : GaugeInvariant (fault d f t) := by
  intro k U; rw [fault,fault]; simp only [Healthy,gauge_flags,(payout_regular d hf).symmetry k U, hf.symmetry k U]
  congr!
lemma fault_reads : UsesFinal t (expand d) (fault d f t) := by
  intro U V ha he
  have h := healthy_reads (G:=G) t _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_union_left (halo 2 {d.site}) d.anchor)) U V ha he
  rw [fault,fault,healthy_reads t _ _ (Finset.Subset.refl _) U V ha he,healthy_reads t _ _ Finset.subset_union_left U V ha he, h,
    (payout_regular d hf).sites U V ha,hf.sites U V (agrees_mono ha (Finset.coe_subset.mpr Finset.subset_union_left))]

lemma counter_moves {s : Signed} {b : Site n} (hn : 4 ≤ n.val) {e : RegularAddress n} (hm : e.support = d.support.image (affine s b))
    (h : e.site = affine s b d.site) {g : Pot G n} (hG : G.Simple) (hg : p.Regular e.support g) (he : g = f ∘ pull s b) (U : Config G n) :
    payout e g U = payout d f (pull s b U) := by
  unfold payout counter; rw [petals_moves,quad_moves _ _ hn hm h hG hf hg he,h]
lemma label_moves {s : Signed} {b : Site n} (hn : 4 ≤ n.val) {e : RegularAddress n} (hm : e.support = d.support.image (affine s b))
    (h : e.site = affine s b d.site) {g : Pot G n} (hG : G.Simple) (hg : p.Regular e.support g) (he : g = f ∘ pull s b) (U : Config G n) :
    rebate e g U = rebate d f (pull s b U) ∧ fault e g t U = fault d f t (pull s b U) := by
  have ht := counter_moves d hf hn hm h hG hg he U
  have hv : Healthy t {e.site} U ↔ Healthy t {d.site} (pull s b U) := by
    rw [h,← Finset.image_singleton]; exact healthy_image ..
  simp only [rebate,Pi.sub_apply,fault,expand_moves d e _ _ hm h,hm,healthy_image,hv,ht]
  simp only [he,comp_apply,pull_one_field,and_self]

include hG in
lemma fault_sup {c : ℝ} (h : p.supBounds d.site d.support f c) (U) : ‖fault d f p.threshold U‖ ≤ resetLoss G p*c := by
  have he := h.2 1 (flat_ok ..) [] (by simp) (by simp)
  have hQ := payout_bill d hG hf h
  unfold fault; split
  · rw [norm_zero]; exact mul_nonneg (loss_pos ..).le h.1
  refine (norm_sub_le ..).trans ((add_le_add (b:=c+multiplier G p*c) (d:=c) ((norm_add_le ..).trans (add_le_add he ?_)) ?_).trans_eq (by unfold resetLoss; ring))
  · split
    next h => exact Bill.norm hQ (l:=[]) (by simp) (by simp) h
    rw [norm_zero]; exact hQ.nonneg
  split
  next he => exact h.2 U he [] (by simp) (by simp)
  rw [norm_zero]; exact h.1
end
lemma splits (U : Config G n) : f 1 + masked t {d.site} (payout d f) U - fault d f t U + masked t (expand d) (rebate d f) U =
    masked t d.support f U := by
  by_cases hh : Healthy t (expand d) U
  · have h := healthy_mono (Finset.subset_union_left (s₂:=halo 2 {d.site})) hh; rw [masked_eq _ _ _ _ hh,masked_eq _ _ _ _ h,
      masked_eq _ _ _ _ (healthy_mono (Finset.singleton_subset_iff.mpr d.anchor) h), fault,if_pos hh]; dsimp only [rebate,Pi.sub_apply]; abel
  rw [fault,if_neg hh,masked_ne _ _ _ _ hh]; split_ifs with h h' h' <;>
    simp [masked_eq,masked_ne,h,h']
lemma label_sub (g : Pot G n) (p : BudgetPoint) (h : p.Regular d.support f) (h' : p.Regular d.support g) :
    rebate d (f-g) = rebate d f - rebate d g ∧ fault d (f-g) t = fault d f t - fault d g t := by
  have he : projection d (f-g) = projection d f - projection d g := funext fun i => funext (projection_sub d h h' i)
  have hL : payout d (f-g) = payout d f - payout d g := by rw [payout,he,← counter_sub]; rfl
  refine ⟨funext fun U => ?_,funext fun U => ?_⟩ <;> simp only [rebate,fault,Pi.sub_apply,hL]; swap
  · split_ifs <;> abel
  abel
end Residual
end YM.AnalyticBridge.VerifiedReset
