import YM.FullVolume.Glide.Ionian
import YM.FullVolume.Artes.Vogue
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Pass FullVolume.Urns FullVolume.Ray Contest FullVolume.Amp Lark.Glide Push.AbsoluteSums
open UniformSpace
variable {R:Run G} (T:Campaign R)
abbrev dome := Metric.ball (0:ℂ) 1
/-- Uses the common `Show` space at each fixed level and period, not changing
supports or norms through the UV limit. In particular includes E/K anchored
norms, hard flags, K sup and E regular derivatives, with the support costs.

Competitors include the actual winning trajectory `T.center N p`.
Disk coordinate s with offset from center `beamWidth * s`; pick any strict
interior compact. Uses `shine` (the analytic extensions take real series
coefficients before parameter complexification; `golden` represents the
values in hullB; it preserves norm, see `measureN`). -/
structure Winter {R : Run G} (T : Campaign R) : Prop where
  width : 0 < Contest.beamWidth R.alloy.B.a
  paths (m : ℕ) :
    ∃ (s : PathData G) (v : ℝ), s.Bounds (R.alloy.B.a.params m).clip (R.alloy.B.a.params m).width
        (R.alloy.B.a.params m).paths (R.alloy.B.a.clock.loopCap m) ∧
      (R.alloy.B.a.params m).width < v ∧
      ∀ g > 0, ∀ᶠ n in atTop, Stationary.Artes.Rios (p := R.alloy.B.kin.path n m) (q := s) v g
  volumes : Locrian R
  beta (n N : ℕ) (s : sun) : ∃ p : Contest N n T.L, bonusB p = ask R.alloy.B.a s
  unique (n N : ℕ) (p p' : Contest N n T.L) : bonusB p = bonusB p' →
    ∀ i : ℕ, i ≤ N → p.trail i = p'.trail i
  alignment (p N : ℕ) (Z : Contest N p T.L) (i : ℕ) (hx : i ≤ N) :
    (Z.trail i).path = R.alloy.B.kin.path N i ∧
    ∃ x : Show (stageP R.alloy.B.a i p), x.proper = (Z.trail i).activities ∧
      (x:cloud R.alloy.B.a i p) = Window.coats T.gains (halls T p N) Z i
  convergence (p : ℕ) (Z : ∀ N, Contest N p T.L) (b : ℝ) :
    Tendsto (fun i => (Z i).bonusB) atTop (𝓝 b) → ∀ m : ℕ, ∃ u v,
      Tendsto (fun N => (Z N |>.trail m).beta) atTop (𝓝 u) ∧
      Tendsto (fun N => Window.coats T.gains (halls T p N) (Z N) m) atTop (𝓝 v)
  analytic (p m : ℕ) :
    ∃ (F : Beam ℝ) (H : ℕ → Beam ℝ) (X : Beam (cloud R.alloy.B.a m p)) (Y : ℕ → Beam (cloud R.alloy.B.a m p)),
      let c := shine Complex.ofRealCLM F
      let f n := shine Complex.ofRealCLM (H n)
      let g n := shine (golden (cloud R.alloy.B.a m p)) (Y n)
      let h := shine (golden (cloud R.alloy.B.a m p)) X
      (∀ n (s : sun), ∀ Z : Contest n p T.L, m ≤ n → bonusB Z = ask R.alloy.B.a s.val →
        f n (↑(s:sun).val) = (Z.trail m).beta ∧
        g n (s:sun).val = golden _ (Window.coats T.gains (halls T p n) Z m)) ∧
      AnalyticOnNhd ℂ c dome ∧ AnalyticOnNhd ℂ h dome ∧
      (∀ n, AnalyticOnNhd ℂ (f n) dome ∧ AnalyticOnNhd ℂ (g n) dome) ∧
      ∀ d, ∀ K, K ⊆ dome → IsCompact K →
        TendstoUniformlyOn (fun n => iteratedDeriv d (f n)) (iteratedDeriv d c) atTop K ∧
        TendstoUniformlyOn (fun n => iteratedDeriv d (g n)) (iteratedDeriv d h) atTop K

lemma offers (hp : Locrian R) (he : Jams.Wild R.kit.shape R.alloy.delay) : Winter T := by
  refine ⟨Contest.raise T.gains, Stationary.Artes.nativity hp.1, hp,
    fun n N => (T.finite_coupling_arc n N).2.1, fun n N p p' => (T.finite_coupling_arc n N).2.2.1 p p',
    fun p N Z i hi => ?_, fun p Z b hx m => ?_, fun p m => ?_⟩
  · let x := homeP T.gains (halls T p N) Z i hi
    exact ⟨(show _ = R.alloy.B.bake.path _ _ from (Z.rises.prices _ (Nat.zero_le _) hi).1.path).trans
      (congr_fun (congr_fun R.alloy.B.bases N) _), x.val, home_observe T.gains (halls T p N) Z _ hi,
      Eq.symm (Window.lifts i hi)⟩
  · obtain ⟨u,v,g,hZ⟩ := Lark.Glide.Window.allB T.gains hp.1 hp.2 he tendsto_id Z (halls T p) hx
    exact ⟨_,_,Window.palm tendsto_id hZ m,hZ.fields m⟩
  obtain ⟨H,Y,F,X,h,hX,hP,hV,H'⟩ := T.sprang p hp he m
  refine ⟨F,H,X,Y, fun n s Z hs hb => ?_,
    fun z hz => Amp.hol _ _ z (mem_ball_zero_iff.mp hz),
    fun z hz => Amp.hol _ _ z (mem_ball_zero_iff.mp hz),
    fun n => ⟨fun z hz => Amp.hol _ _ z (mem_ball_zero_iff.mp hz),
              fun z hz => Amp.hol _ _ z (mem_ball_zero_iff.mp hz)⟩,
    fun d K hK hk =>
      ⟨(tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hk).mp
        ((Amp.Beam.version Complex.ofRealCLM F h (fun i => (H' i).1) hP d).mono hK),
       (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hk).mp
        ((Amp.Beam.version _ X hX (fun i => (H' i).2.1) hV d).mono hK)⟩⟩
  obtain ⟨hp,hX⟩ := H' n|>.2.2 hs _ _ hb
  dsimp only
  rw [Amp.opening,Amp.opening,←hp,←hX]
  exact ⟨rfl,rfl⟩
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.offers
