import YM.Analytic.Real
import YM.AnalyticBridge.RESET_INCOME_PORT.Stages
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Pelf
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Pier
import YM.Planned.ATOM_REGULAR_ESTIMATE.Reopen
import YM.UVNext.PRICED_KERNELS.Gaps

/-!
# Local Δ integrands are compact-argument, uniform-in-y neighborhood

Weights for Bore comparisons deferred (no absolute drift factor for Gaussian
volume). Local smooth dominance even in presence of K sectors and truncated
 E masks; `Ranks` applied on SAME FOREST.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (hp : Intake P T X.x R)
  (hs : Scrim X a) (hP : Room P S T X.x)
variable {τ : ℝ} (hτ : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) τ) {ζ d A t L : ℝ} (h : Canary G d A)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Z : E→ Config G c} {p : E} {n : ℕ}

section stamp
include hτ
omit [DecidableEq I] in
lemma owing (s : Prices G I) : ‖owe X i R a s‖ ≤ τ := by
  let U:= strip6 X a X.V (anchor X a s R.beta); unfold owe award Activities.regularOccurrence
  by_cases hx: Healthy R.p.threshold (R.activities.reg i).support U
  · rw [masked_eq _ _ _ _ hx]; exact hτ.2 _ hx [] (Nat.zero_le _) (by simp)
  change ‖masked _ _ _ U‖≤_; rw [masked_ne _ _ _ _ hx,norm_zero]; exact hτ.1

omit hτ [DecidableEq I] in
include hp in
lemma owe_m : Measurable (owe X i R a) := by
  let k z:=anchor X a z R.beta; have hh : Measurable k:= measurable_pi_lambda _ fun j=> measurable_const.add
    (Measurable.const_smul (g:=fun p:Prices G I=>tape p j) ((measurable_pi_apply j).comp tape.measurable) (gStep R.beta))
  exact (masked_measurable _ _ _ (hp.cap.labels.regular.smooth i).borel).comp (Art.entering X (V:=fun _:Prices G I=> X.V) (Y:=fun _=>X.Y) measurable_const measurable_const ((measure_tap X a).comp hh))
end stamp

section mer
structure Ranks (Z : E→ Config G c) (d ζ : ℝ) (p : E) (n : ℕ) : Prop where
  cuff (s : Prices G I) : ContDiffAt ℝ n (uncurry (tax6 X i R a d R.beta ∘ Z)) (p,s)
  crown (s : Prices G I) : ContDiffAt ℝ n (uncurry (tax9 X i R a q b d R.beta ∘ Z)) (p,s)
  veilT (s : Prices G I) : ContDiffAt ℝ n (fun z:E×Prices G I=> veil X a q κ b D R.p d R.beta z.2 (Z z.1)) (p,s)
  coinS (s : Prices G I) : ContDiffAt ℝ n (uncurry (coin X i R a d R.beta ζ ∘ Z)) (p,s)

abbrev screen (K t d g : ℝ) := (5*K*t+d*t)/g
omit [DecidableEq I] in
lemma envelop (s : Prices G I) {v : Config G c} (h : coin X i R a d R.beta ζ v s≠0) (hh:0<ζ*X.t) : ∀ j, ‖fawn X v a s d R.beta j‖≤ 4*ζ*X.t := by
  intro j
  let t:=fawn X v a s d R.beta j
  apply le_trans ((X.χ.chosen_lt ‖t‖ _ (show 0<2*ζ*X.t by rw [mul_assoc]; positivity) (Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j))).le)
  apply le_of_eq; ring

variable {M : ℝ} (hZ : Tendsto Z (𝓝 p) (𝓝 X.V))
variable (he : 0 < ζ*X.t) (hv : ∀ k, ‖volume6 X a k X.V‖ ≤ M*X.t)
include he hv hZ hp h
omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] [DecidableEq I] in
-- E vectors priced later
lemma silence (hβ : screen ζ X.t M (gStep R.beta) ≤ L) (hL : 0≤L) : ∀ᶠ z in 𝓝 p, ∀ u : Prices G I, L < ‖u‖ → coin X i R a d R.beta ζ (Z z) u=0 := by
  filter_upwards [homing X a h hZ he (β:=R.beta)] with z hh u hU
  by_contra ht
  have hf:=envelop X i R a u ht he
  apply hU.not_ge; let g:=gStep R.beta; have hg:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hp.positive)
  refine (pi_norm_le_iff_of_nonneg hL).mpr fun j=> ?_
  have h j : g*‖tape u j‖ ≤ 5*ζ*X.t+M*X.t:= by
    let x:= anchor X a u R.beta j; let m:= volume6 X a j X.V
    have hx : g*‖tape u j‖=‖x-m‖:= by change _=‖(m+g • tape u j)-m‖; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hg.le]
    rw [hx]
    let y:=fawn X (Z z) a u d R.beta j
    apply (norm_sub_le x m).trans
    have h₁:= norm_sub_le_norm_sub_add_norm_sub x y 0; rw [sub_zero,sub_zero,norm_sub_rev x y] at h₁
    exact (add_le_add (h₁.trans (add_le_add (hh u j |>.le) (hf j))) (hv j)).trans_eq (by ring)
  exact ((PiLp.norm_apply_le (tape u j.1) j.2).trans ((le_div_iff₀ hg).mpr ((mul_comm ..).trans_le (h j.1)))).trans hβ

abbrev tracks6 (Z : E→ Config G c) (d ζ : ℝ) := strand6 X i R a d ζ ∘ Z
abbrev tracks9 (Z : E→ Config G c) (d : ℝ) := strand9 X i R a q κ b D d ∘ Z
def tally (Z : E→ Config G c) (d ζ : ℝ) := tracks6 X i R a Z d ζ + tracks9 X i R a q κ b D Z d

include hτ
lemma cable (μ : Measure (Prices G I)) [IsFiniteMeasure μ] (hh : Ranks X i R a q κ b D Z d ζ p n)
    (hg : ∀ᶠ z in 𝓝 p, ∀ s, veil X a q κ b D R.p d R.beta s (Z z)≠0 → coin X i R a d R.beta ζ (Z z) s=1) :
    Meristem (tally X i R a q κ b D Z d ζ) p μ n ∧ ∀ᶠ x in 𝓝 p, Integrable (tracks6 X i R a Z d ζ x) μ ∧ Integrable (tracks9 X i R a q κ b D Z d x) μ := by
  let D' := screen ζ X.t M (gStep R.beta); let L:= max D' 0; let S':= (closedBall (0:Prices G I) L) ×ˢ closedBall (0:ℝ) τ
  let P z (s:Prices G I×ℝ):= tax6 X i R a d R.beta (Z z) s.1 * (Real.exp (-s.2*coin X i R a d R.beta ζ (Z z) s.1)-1)
  let Q z (s:Prices G I×ℝ):= tax9 X i R a q b d R.beta (Z z) s.1 * (veil X a q κ b D R.p d R.beta s.1 (Z z)*s.2)
  let U:= tracks6 X i R a Z d ζ; let V:= tracks9 X i R a q κ b D Z d; let y x:= (x,owe X i R a x)
  have hx (J' : E→ Prices G I → ℝ) (A : E→ Prices G I × ℝ→ℝ) (hh : ∀ z, J' z=A z∘ y) (hp' : ∀ s∈ S', ContDiffAt ℝ (↑n) (uncurry A) (p,s))
      (hq : ∀ᶠ x in 𝓝 p, ∀ u : Prices G I, L < ‖u‖ → J' x u=0) : Meristem J' p μ n := by
    refine caisson μ (h:=y) (measurable_id.prodMk (owe_m X i R a hp)) (show IsCompact S' from (isCompact_closedBall ..).prod (isCompact_closedBall ..)) hp' ?_
    filter_upwards [hq] with v hz u; by_cases hu : ‖u‖ ≤ L
    · rw [indicator_of_mem (show y u∈ S' from ⟨mem_closedBall_zero_iff.mpr hu,mem_closedBall_zero_iff.mpr (owing X i R a hτ u)⟩), hh]
      rfl
    rw [indicator_of_notMem (fun he => hu (mem_closedBall_zero_iff.mp he.1)), hz u (lt_of_not_ge hu)]
  have he := silence X i R a hp h hZ he hv (L:=L) (le_max_left ..) (le_max_right ..)
  have hU: ∀ᶠ x in 𝓝 p, ∀ u, L < ‖u‖→ U x u=0 := he.mono (fun i' he u hu => by change strand6 .. = 0; unfold strand6; rw [he u hu,mul_zero,Real.exp_zero,sub_self,mul_zero])
  have hV: ∀ᶠ x in 𝓝 p, ∀ u, L< ‖u‖→V x u=0 := (he.and hg).mono (fun i' hv u hu=> by
    have hx : veil X a q κ b D R.p d R.beta u (Z i')=0:= Classical.not_not.mp (fun hz=>zero_ne_one ((hv.1 u hu).symm.trans (hv.2 u hz))); change strand9 .. = 0; unfold strand9; rw [hx,zero_mul,mul_zero])
  let H (v:E× Prices G I × ℝ):=(v.1,v.2.1); have hh' : ContDiff ℝ n H:= by unfold H; fun_prop
  have hl (v : E×Prices G I×ℝ) : ContDiffAt ℝ n (fun z:E× Prices G I × ℝ=>z.2.2) v:= contDiffAt_snd.comp _ contDiffAt_snd
  have ha s : ContDiffAt ℝ n (uncurry P) (p,s) := (ContDiffAt.comp (f:=H) (p,s) (hh.cuff s.1) hh'.contDiffAt).mul (((((hl _).neg.mul ((hh.coinS s.1).comp (f:=H) (p,s) hh'.contDiffAt)).exp).sub contDiffAt_const))
  have hb s : ContDiffAt ℝ n (uncurry Q) (p,s):= ((hh.crown s.1).comp (f:=H) (p,s) hh'.contDiffAt).mul (((hh.veilT s.1).comp (f:=H) (p,s) hh'.contDiffAt).mul (hl _))
  refine ⟨hx _ (P+Q) (fun _=>rfl) (fun s _=> (ha s).add (hb s)) ((hU.and hV).mono (fun v hx u hy=> show U v u+V v u=0 by rw [hx.1 u hy,hx.2 u hy,zero_add])),
    (spent_here μ (hx U P (fun _=> rfl) (fun s _=> ha s) hU)).and (spent_here μ (hx V Q (fun _=>rfl) (fun s _=> hb s) hV))⟩
end mer
end YM.PhysicalNext.Repeat.Baffle
