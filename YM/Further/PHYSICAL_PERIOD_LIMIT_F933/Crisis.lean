import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import YM.Extra.MULTISOURCE_BOUNDS.Trajectory
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.SOURCE_HISTORIES.Pads
import YM.Extra.WILSON_STARTUP.ExtraCover
import YM.Extra.WILSON_STARTUP.Fast
import YM.Next.SCHEDULE.Blocks
import YM.Progress.DIRECTED_RECIPE.Economy




/-!
# An incompatibility between the fused-address vaccine and λ supplier;
repair and genuine stronger startup price

There IS no Histories.Shelf on the
packed start presentations of two plausible recipes here.

Even if there
are sufficiently many dormant slots (not viz zero #), the *test*
required by that API is incompatible with the fused condition.

Cannot just combine those suppliers on their common vacuum.

Use the
existing `Pads.jolt` solution PRIOR to fusing with any source methods:
same beta and raw vacuum and same Kin, but the new history and recipe
with more labels is the realizing one.

Preserve also the stronger top
K price for MIX; `.Thick` here isn't the weaker unit cost.

Another
potential fix not pursued here: relax Shelf to only require test at
flag condition and reissue uses of the Birth interface under that
sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Crisis
open Function Filter Lattice RG Supply Wilson Ovens Ovens.Pipes Bid
  Extra.Histories WilsonStartup Start
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} (b : BudgetPoint) {N p : ℕ}









/-- Stronger K envelope sufficient for Thick. Purchased before bar. -/
structure Early (a : Levels G) (N : ℕ) : Prop where
  allows : Start.Allows a N
  expand : ∃ σ κ γ, Start.Loan (Start.expand (a.budget N)) (a.clock.hatBeta N/2) σ κ γ ∧
      Bid.quote κ (Real.exp γ-1) ≤ a.clock.forcedAllowance N

lemma stronger (G : Gauge) (A : Stage) (h : A.clip.direct ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ a : Levels G, ∀ N, a.params N = A → a.clock.hatBeta N = x → Early a N := by
  filter_upwards [Timing.enough G A h,Real.tendsto_log_atTop.eventually (Timing.loan (A.supportExponent+8)),
    eventually_gt_atTop (0:ℝ)] with x ht hl he a N hu hw
  refine ⟨ht a N hu hw,?_⟩
  let q := Real.log x; let P := Start.expand (a.budget N)
  have hx : a.clock.hatCoupling N = Real.exp (-(q/2)) := by
    unfold Calendar.hatCoupling; rw [hw,Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos he]; unfold q; ring_nf
  obtain ⟨hh,h⟩ := hl P (by
    dsimp only [P,Start.expand,Levels.budget, Calendar.threshold,Calendar.monitor,Timing.temp]
    rw [hx,Real.exp_add]; unfold q; rw [hw]) (congr_arg (fun x => Timing.balls (Real.log x)) hw) (congr_arg (fun p : Stage => p.supportExponent+8) hu)
  rw [Real.exp_log he] at hh
  nth_rw 1 [← hw] at hh
  refine ⟨_,_,_,hh,h.trans_eq ?_⟩
  unfold Timing.normK Calendar.forcedAllowance Calendar.monitor; rw [hw,← Real.exp_mul]; congr 3; ring

/-- Have this menu ready even if increasing the betaEntry after further
requests (true scheduling for these particular asks). Note profile/clip
must be the ACTUAL one. -/
structure Equipped (p : RG.Supply.Sheet G) (f : ℕ → ℝ) : Prop where
  pay j : p.first ≤ j → ∀ β : ℝ, f j ≤ β → ∀ a : Levels G, ∀ N, a.params N=p.profile j → a.clock.hatBeta N=β → Early a N

lemma prebuy (G : Gauge) (p : RG.Supply.Sheet G) (h : ∀ j ≥ p.first,(p.profile j).clip.direct ≤ 1) :
    ∃ f : ℕ → ℝ, ∀ g : ℕ → ℝ, f ≤ g → Equipped p g := by
  have hq j : ∀ᶠ (t : ℝ) in atTop, p.first ≤ j → ∀ (a : Levels G) (N : ℕ), a.params N=p.profile j → a.clock.hatBeta N=t → Early a N := by
    by_cases hp : p.first ≤ j
    · exact (stronger G (p.profile _) (h _ hp)).mono fun _ hi _ => hi
    exact Eventually.of_forall fun _ ht => (hp ht).elim
  choose f hf using fun j => eventually_atTop.mp (hq j)
  exact ⟨f,fun g hg => ⟨fun j h β he => hf j β ((hg j).trans he) h⟩⟩

lemma paid {s : RG.Supply.Sheet G} {D : Rolls s} {P : Protection D} {W : RG.Supply.Delays P}
    {Y : Bar W} {U : Wait Y} {a : Levels G} (hp : Paid U a) (h : Equipped s W.betaEntry) (hG : G.Simple) (N : ℕ) : Early a N := by
  apply h.pay (a.clock.J N) (hp.firstZero ▸ a.fits.mono (Nat.zero_le N)) (a.clock.hatBeta N) _ a N (congr_fun hp.stage _) rfl
  cases N with
  | zero => simpa only [Calendar.hatBeta,Schedule.scale_zero,mul_zero,add_zero,hp.firstZero,hp.bar] using Y.ready
  | succ i => exact (hp.pays i).trans (Timing.hat_mono a (Gauge.slopeConstant_pos hG).le i.le_succ)

lemma kBound {a : Levels G} (h : Early a N) {β : ℝ} (hb : β ∈ Shoot.band a N) :
    (layout a N p β).activities.KBound (Start.expand (a.budget N)) (a.clock.forcedAllowance N) := by
  obtain ⟨hc,σ,κ,γ,h,hg⟩ := h
  exact Start.expandK hc.clip hc.radius h hb.1 hg

lemma kHit (A : Activities G n) {γ w : ℝ} (h : A.KBound b w) (hv : γ ≤ b.supportExponent) :
    ∃ k : ℕ → ℝ, (∀ i, 0≤k i ∧ ∀ U, ‖A.K i U‖ ≤ k i) ∧ Ac.Hit (fun i => (A.forced i).support) b.B k γ w := by
  obtain ⟨f,hf,H⟩ := h
  refine ⟨f,hf,fun x => ?_⟩
  let g (a : ℝ) (i) := if x∈(A.forced i).support then f i*Real.exp (a*coverNumber b.B (A.forced i).support) else 0
  have hG i : 0 ≤ g γ i := by unfold g; split; exact mul_nonneg (hf _).1 (Real.exp_pos _).le; exact le_rfl
  have ht i : g γ i ≤ g b.supportExponent i := by
    unfold g; split
    · gcongr; apply (hf i).1
    exact le_rfl
  have hh : SumBudget (g b.supportExponent) w := by simpa only [BudgetPoint.mass,g,mul_comm (f _)] using (H x)
  exact ⟨hG,hh.2.1.of_nonneg_of_le hG ht,((hh.2.1.of_nonneg_of_le hG ht).tsum_le_tsum ht hh.2.1).trans hh.2.2⟩

/-- On the NEW realizing history; can discard the original version
before doing any shape estimates for Eq/C columns. -/
lemma pad_thick {C : Family G} (h : Early C.path.levels N)
    (hE : C.path.rep N p N = Extra.Histories.Pads.bulk (layout C.path.levels N p (C.beta N p)))
    (hB : C.beta N p ∈ Shoot.band C.path.levels N) : Extra.Multi.Thick C N p := by
  have hb := Extra.Histories.Pads.zeros _ _ _ (kBound (p:=p) h hB)
  unfold Extra.Multi.Thick; rw [hE]
  apply kHit _ _ hb
  change (C.path.levels.budget N).supportExponent+1 ≤ _+8; linarith
end YM.Further.PhysicalPeriodLimitF933.Crisis
