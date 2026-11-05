import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Glow
/-!
 # Both arm expressions explicit... identity on stencil after FULL permits.Then price.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Baffle Prism Brim Lotus Peak
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (hp : Intake P T X.x R) (hs : Scrim X a) (hP : Room P S T X.x)
variable {W : Config G f} {ζ d A t : ℝ} (h : Canary G d A) (hv : Drivable X d A V)
variable (M: Lotus.Leaf R)(hg:M.turn= .logKey i)
variable (L : Config G f→ℝ)(hL: R.p.Regular (R.activities.reg i).support L)(hm:M.ingredient= masked R.p.threshold (R.activities.reg i).support L)
omit [DecidableEq I] in
lemma drum : Measurable (golf X i R a M):=by
  let k z:=anchor X a z R.beta; have hh : Measurable k:= measurable_pi_lambda _ fun j=> measurable_const.add
    (Measurable.const_smul (g:=fun p:Prices G I=>tape p j) ((measurable_pi_apply j).comp tape.measurable) (gStep R.beta))
  exact M.borel.comp (Art.entering X (V:=fun _:Prices G I=> X.V) (Y:=fun _=>X.Y) measurable_const measurable_const ((measure_tap X a).comp hh))
variable {N ℓ p v m w K δ M' : ℝ}{n:ℕ} (Q : Anthem n)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E→ Config G c} {x : E}
variable (hb : 0<ζ*X.t) (hZ : Tendsto Z (𝓝 x) (𝓝 X.V))
-- Meristem.T.Container
abbrev T6 (d ζ : ℝ) (Z : E→ Config G c) := box6 X i R a M d ζ ∘ Z
abbrev T9 (d : ℝ) (Z : E→ Config G c) := box9 X i R a q κ b D M d ∘ Z
def both (d ζ : ℝ) (Z : E→ Config G c) := T6 X i R a M d ζ Z-T9 X i R a q κ b D M d Z
include h hp
variable {Q₀ : ℝ}
section
variable (z:Prices G I)(he:Score X i R a q κ b D z K d ζ δ N Q₀ Q Z x)
include he
local notation "τ"=> M.weight
local notation "u" => incomeB Q N Q₀
local notation "D₁" => incomeD Q N Q₀ δ
lemma crump : Brush n (τ*(2*altitude Q N Q₀ δ)) 1 (fun x=> Mercury.both X i R a q κ b D M d ζ Z x z) x:=by
  obtain ⟨hf,hh⟩:= arrows X i R a q κ b D hp h z Q he
  let B y:= tax6 X i R a d R.beta (Z y) z; let A y:=tax9 X i R a q b d R.beta (Z y) z
  have hl:Brush n (D₁+u) 1 A x := (hh.gathering hf).shimmy (Eventually.of_forall fun _=> (sub_add_cancel ..).symm)
  let w:= golf X i R a M z; have hw: ‖w‖≤τ:= M.earn _
  have hα:=(((hf.paints ((he.cover.smul w).climb (mul_le_mul_of_nonneg_right hw he.basis) le_rfl)).trim).gathering (((hl.paints ((he.veil.smul w).climb (mul_le_mul_of_nonneg_right hw he.basis) le_rfl)).trim.opposite)))
  apply hα.climb _ le_rfl|>.shimmy (Eventually.of_forall (fun x=> ?_)); swap
  · change B x*(coin X i R a d R.beta ζ (Z x) z*w)- A x*(veil X a q κ b D R.p d R.beta z (Z x)*w)=_ ; rw [sub_eq_add_neg]; rw [mul_comm _ w,mul_comm (Baffle.veil X a q κ b D R.p d R.beta z (Z x)) w]; rfl -- notation ..
  have heD:0≤D₁:=hh.nonneg; have heB:0≤u:=hf.nonneg; let p:=(1+(1+1:ℝ))^n; have hf:0≤p:=by unfold p; positivity
  have hq:0≤Q₀:= he.basis; have he:=Q.escort; have ht:0≤τ:=M.profit
  unfold altitude; change u*(τ*Q₀)*p+(D₁+u)*(τ*Q₀)*p≤_
  calc
    _ ≤ (D₁+u)*(τ*Q₀)*p+(D₁+u)*(τ*Q₀)*p := by gcongr; linarith
    _ = τ*(2*((0+(D₁+u)*Q₀)*p)) := by ring
    _ ≤ _ :=by unfold p; gcongr; positivity
lemma crumb (hK:0≤K) (hv:∀ᶠ y in 𝓝 x, coin X i R a d R.beta ζ (Z y) z=1 ∧ veil X a q κ b D R.p d R.beta z (Z y)=1): Brush n (τ*ground0 Q N Q₀ δ K) 1 (fun x=> Mercury.both X i R a q κ b D M d ζ Z x z) x:=by
  obtain ⟨hf,hh⟩:= arrows X i R a q κ b D hp h z Q he; let w:= golf X i R a M z; have hw:‖w‖≤τ:= M.earn _
  apply (hh.smul (-w)).climb _ le_rfl|>.shimmy (hv.mono (fun x hx=> ?_)); swap
  · change tax6 X i R a d R.beta (Z x) z*(coin X i R a d R.beta ζ (Z x) z*w) - tax9 X i R a q b d R.beta (Z x) z*(veil X a q κ b D R.p d R.beta z (Z x)*w) = -(w)*(_- _); rw [hx.1,hx.2]; ring
  rw [norm_neg]; apply (mul_le_mul_of_nonneg_right hw hh.nonneg).trans; apply mul_le_mul_of_nonneg_left _ M.profit; exact le_add_of_nonneg_left (mul_nonneg hK hf.nonneg)
end

variable [FiniteDimensional ℝ E]
include hZ hb
lemma corridor (μ : Measure (Prices G I)) [IsFiniteMeasure μ] (hh : Ranks X i R a q κ b D Z d ζ x n)
    (hm:∀ i,‖volume6 X a i X.V‖ ≤ M'*X.t)
    (he : ∀ᶠ z in 𝓝 x,∀ s, veil X a q κ b D R.p d R.beta s (Z z)≠0→coin X i R a d R.beta ζ (Z z) s=1):
    Meristem (Mercury.both X i R a q κ b D M d ζ Z) x μ n ∧ ∀ᶠ x in 𝓝 x, Integrable (T6 X i R a M d ζ Z x) μ ∧ Integrable (T9 X i R a q κ b D M d Z x) μ:=by
  let p:=x; let D':=Baffle.screen ζ X.t M' (gStep R.beta); let L:= max D' 0; let τ:=M.weight; let S':=(closedBall (0:Prices G I) L) ×ˢ closedBall (0:ℝ) τ
  let P z (s:Prices G I × ℝ):=tax6 X i R a d R.beta (Z z) s.1 * (coin X i R a d R.beta ζ (Z z) s.1*s.2)
  let Q z (s:Prices G I × ℝ):=tax9 X i R a q b d R.beta (Z z) s.1*(veil X a q κ b D R.p d R.beta s.1 (Z z)*s.2)
  let y z:=(z,golf X i R a M z); let U:= T6 X i R a M d ζ Z; let V:= T9 X i R a q κ b D M d Z
  have hw (J:E→ Prices G I→ℝ)(A:E→Prices G I×ℝ→ℝ)(hh:∀ z,J z=A z∘y)(hp:∀ w∈S',ContDiffAt ℝ (↑n) (uncurry A) (p,w))(hq:∀ᶠ z in 𝓝 p,∀ u:Prices G I,L<‖u‖ → J z u=0):Meristem J p μ n:=by
     apply caisson μ (h:=y) (measurable_id.prodMk (drum X i R a M)) (show IsCompact S' from (isCompact_closedBall ..).prod (isCompact_closedBall ..)) hp; filter_upwards [hq] with v hv u; by_cases hu:‖u‖ ≤ L
     · rw [indicator_of_mem (show y u∈ S' from ⟨mem_closedBall_zero_iff.mpr hu,mem_closedBall_zero_iff.mpr (M.earn _)⟩), hh]; rfl
     rw [indicator_of_notMem (fun he => hu (mem_closedBall_zero_iff.mp he.1)), hv u (lt_of_not_ge hu)]
  have hz := Baffle.silence X i R a hp h hZ hb hm (L:=L) (le_max_left ..) (le_max_right ..)
  have hU : ∀ᶠ z in 𝓝 p, ∀ u,L<‖u‖ → U z u=0:= hz.mono (fun z hh u hu=>by change box6 ..=0; unfold box6; rw [hh u hu,zero_mul,mul_zero])
  have hV : ∀ᶠ x in 𝓝 p, ∀ u, L< ‖u‖→V x u=0 := (hz.and he).mono (fun i' hv u hu=> by
    have hx : veil X a q κ b D R.p d R.beta u (Z i')=0:= Classical.not_not.mp (fun ht=>zero_ne_one ((hv.1 u hu).symm.trans (hv.2 u ht))); change box9 .. = 0; unfold box9; rw [hx,zero_mul,mul_zero])
  let H (v:E× Prices G I × ℝ):=(v.1,v.2.1); have hh' : ContDiff ℝ n H:= by unfold H; fun_prop
  have hl (v:E×Prices G I × ℝ):ContDiffAt ℝ n (fun z:E×Prices G I ×ℝ=>z.2.2) v:= contDiffAt_snd.comp _ contDiffAt_snd
  have ha s : ContDiffAt ℝ n (uncurry P) (p,s):= ((hh.cuff s.1).comp (f:=H) (p,s) hh'.contDiffAt).mul (((hh.coinS s.1).comp (f:=H) (p,s) hh'.contDiffAt).mul (hl _))
  have hv s : ContDiffAt ℝ n (uncurry Q) (p,s):= ((hh.crown s.1).comp (f:=H) (p,s) hh'.contDiffAt).mul (((hh.veilT s.1).comp (f:=H) (p,s) hh'.contDiffAt).mul (hl _))
  exact ⟨hw _ (P-Q) (fun _=>rfl) (fun s _=> (ha s).sub (hv s)) ((hU.and hV).mono (fun v hx u hy=> show U v u - V v u=0 by rw [hx.1 u hy,hx.2 u hy,sub_zero])),
    (spent_here μ (hw U P (fun _=>rfl) (fun s _=>ha s) hU)).and (spent_here μ (hw V Q (fun _=>rfl) (fun s _=>hv s) hV))⟩
end YM.PhysicalNext.Repeat.Mercury
