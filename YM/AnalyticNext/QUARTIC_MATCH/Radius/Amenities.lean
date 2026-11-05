import YM.AnalyticNext.QUARTIC_MATCH.Radius.Colors

/-!
# Full flesh of the unmasked prescription in the analytic neighborhood

Retain tiles for derivative estimates; don't claim *per tile* lower-order agreement.
May budget all after the L's and a Quote before the delay heights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model Warp Raised Orbit
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Aisle

open Green (address wt)
open Managed
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio) (p : Clip) {R : PathData G}
variable {F : Site f → ChartVars H G → ℝ} {Q : Purchase} {η : ℝ} (hp : Q.Applies H p R F) (hr : 0 < η) (hh : PriceGap H p R η)
variable {χ : Dir G c → AxisChart G H} (hk : Reaches Q η S H p R χ) {x : Dir G c} (he : ‖x‖ < Orbit.berth Q G η)
local notation "L" => (S.patch.L.val:ℝ)
include hp hr hh hk he

omit hp hr hh hk he in
def marked (Q : Purchase) (G : Gauge) (η : ℝ) (m) := Polish.stamped m (Q.fees m) (Managed.bought Q G η m m)
omit hp hr hh hk he in
lemma marked_ge (Q : Purchase) (G : Gauge) (η : ℝ) (m) : 1≤marked Q G η m := Polish.stamp_pos ..


omit hp hr hh hk he in
lemma close (b : Site c) (i : Site S.patch.L) : separation (S.ratio.assemble (b,i)) (S.ratio.embed b) ≤ S.patch.L.val := by
  have hp := Corona.near S.ratio (S.ratio.assemble (b,i)); rw [Ratio.assemble_parent] at hp
  change 2 * separation _ _ ≤ S.patch.L.val at hp; dsimp only at hp; omega
omit hp hr hh hk he in
lemma along (b : Site c) {i : Site S.patch.L} {d : Dir G c} (t : ℝ) (he : 0 ≤ t) (C : ℝ) (h : 0≤C) (hp : Fetch.trials G (t*L) b d C) :
    outer S G t (S.ratio.assemble (b,i)) d (C*Real.exp (t*L)) := by
  have hh (x y : Site c) : wt (t*L) x y=wt t (S.ratio.embed x) (S.ratio.embed y) := by
    have ht := Evoke.accrual S y x (t*L)
    rw [show t*L/(S.ratio.count.val:ℝ) = t from by rw [show S.ratio.count=S.patch.L from rfl]; field_simp] at ht
    exact ht.symm
  have ht : outer S G t (S.ratio.embed b) d C := fun i=> by
    dsimp only [Function.comp_apply]; rw [← hh]; exact hp i
  apply Amount.elevate (Amount.origin ht (S.ratio.assemble (b,i)) he h)
  apply mul_le_mul_of_nonneg_left _ h; apply Real.exp_monotone; gcongr; exact close S b i
omit hp hr hh hk he in
def residence (F : Site f → ChartVars H G → ℝ) (χ : Dir G c → AxisChart G H) (b : Site c) (x : Dir G c) :=
    ∑ i : Site S.patch.L,F (S.ratio.assemble (b,i)) (x,χ x)
omit hp hr hh hk he in
def presented (l : Side) (t : ℝ) (m : ℕ) (C : ℝ) := Fintype.card (Site l) * (C* Real.exp (t*l.val)^m)
omit hp hr hh hk he in
lemma enough (l : Side) {t C : ℝ} (h : 0≤t) (m : ℕ) (he : 1≤C) : 1≤presented l t m C := by
  have hh := Fintype.card_pos (α:=Site l)
  have hp : 1 ≤ Real.exp (t*l.val)^m := one_le_pow₀ (Real.one_le_exp (by positivity))
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hh) (one_le_mul_of_one_le_of_one_le he hp)

omit hr hh in
lemma readsOn (θ : S.Choices) : (∑ i : Site c, residence S H F χ i x) = Joint.value H θ p R χ x := by
  rw [show Joint.value H θ p R χ x=_ from hp.formula ((inside_r S H p R hk he).trans (Orbit.room ..)) θ]
  rw [← Equiv.sum_comp S.ratio.splitSites.symm (fun i => F i (x,χ x)), Fintype.sum_prod_type]; rfl
omit hr hh in
lemma arcLeaf (i : Site f) : ContDiffAt ℝ ω (F i ∘ arc χ) x :=
    (hp.smooth ((inside_r S H p R hk he).trans (Orbit.room ..)) i).comp (f:=arc χ) x (contDiffAt_id.prodMk (hk.smooth _ he))
omit hr hh in
lemma leaf (b : Site c) : ContDiffAt ℝ ω (residence S H F χ b) x := ContDiffAt.sum fun _ _=> arcLeaf S H p hp hk he _


end Aisle
end YM.AnalyticNext.QuarticMatch.Radius
