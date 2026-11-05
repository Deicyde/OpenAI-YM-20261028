import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Posts
import YM.Progress.JOINT_CALENDAR.Issue

/-! Inflation for area tags at the weak rank temperature. `t` a
post-L coefficient. See Opacity for the paid estimates and imports of the
physical layouts. `theta` for Drow accounting on the cut crown. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Wax
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Paint Filter Finset Precision Tree Next.SectorChange
open Pressure.Tube Pressure.Teller Pressure.Stores YM.Bid Work Push.SectorMeasure
    YM.SectorNext.Remainder Oriented MeasureTheory Next.Fluctuations.Sector AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Local Display Display.Docking
open _root_.YM.SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {X : Lantern G S} {x t β δ r y z m w σ a : ℝ} {n o g : ℕ}
local notation "τ"=>retime x
local notation "ξ"=>betaF G x S.patch.L
local notation "η"=>hot (betaF G x S.patch.L)
def theta (p : PathData G) (c : Clip) (R : ℕ) (x t : ℝ) (U : Config G f):= averaged fun s=>∑ i,crown p c (till x) R t (pull s 0 U) i
open Next.Rank.Thirst Next.Rank.Flux

lemma flint (v : Purse) (L : Side) {t : ℝ} (ht : 0<t) (h : 2*v.era.coast.a ≤ t): ∀ᶠ s in atTop,∀ x∈ Set.Icc (s/2) s,
    max (acres v x (betaF G x L)) (Line v.era v.goal 0 s) ≤ Real.exp (t*hot (betaF G x L)^2):= by
  filter_upwards [Perch.half.eventually_ge_atTop (Real.exp 1), Perch.force ht (v.goal:ℝ) 0 le_rfl (Nat.cast_nonneg _)] with s hs ht' x hx
  let a:= v.era.coast.a; let y:=betaF G x L
  have hz := v.era.coast.posA; have he:x≤y:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hb := pow_le_pow_left₀ (show 0≤ hot x from (Real.exp_pos _).le) (hot_mono (hs.trans hx.1) he) 2; let G₀:= hot y ^ 2
  refine max_le_iff.mpr ⟨max_le_iff.mpr ⟨?_,?_⟩,?_⟩
  · change (Real.exp _ ^ 2)⁻¹ ≤ _; rw [← Real.exp_nat_mul, ← Real.exp_neg]; push_cast;apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_right h (sq_nonneg (hot x)),mul_le_mul_of_nonneg_left hb ht.le]
  · change (Real.exp _)⁻¹ ≤ _; rw [← Real.exp_neg]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_right (show v.era.coast.a ≤t by linarith only [h,hz]) (sq_nonneg (hot (betaF G x L)))]
  unfold Line fareP firstN; rw [mul_zero,zero_add]; apply max_le_iff.mpr; unfold Perch.bill; rw [← Real.exp_sub]
  refine ⟨Real.one_le_exp (mul_nonneg ht.le (sq_nonneg _)),Real.exp_monotone ?_⟩
  linarith only [ht' x hx,Perch.boil_pos s,mul_le_mul_of_nonneg_left hb ht.le]
end YM.PhysicalNext.InteractingRank.Wax
