import YM.TraceExtension.Quince.Bairn
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Assure
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Chant

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open Bid Planned.PrimaryIntegral295 WaterLevels
open Cub
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Circlet PPX Next.Free
open Malachite
variable {n:ℕ}{G:Gauge}{T:Teller G}
structure Loader (C:Libretto G n) (D:Record) (K:KernelChoices)(L:Side)(j i d n0 k l r:ℕ)(x z:ℝ): Prop where
   dawn:reach x ≤ radiusD x
   buoy(P B:BudgetPoint) : P.power=k → B.power=l→ B.threshold=fiery G x L→ P.threshold ≤ 2*B.threshold →
      0≤loom P (radiusD x) C.C∧D.Q*loom P (radiusD x) C.C≤1 ∧ loom P (radiusD x) C.C < D.r ∧ B.threshold*(1+(depthW L (radiusD x):ℝ))^B.power ≤ 1
   cut : radiusB (betaF G x L)≤2*radiusB x
   hit : 1≤ radiusB (betaF G x L)
   stirred : ∀ (β:ℝ), betaF G x L/2 ≤ β →∀ f:Side,∀ (X: Support f)(P B:BudgetPoint), B.threshold=fiery G x L→ P.threshold ≤ 2*B.threshold → B.B ≤ 2*radiusB x→ P.power=k→ coverNumber B.B X ≤ packing L x→
     let F:=opalW C D P B (radiusD x) L X r x (gStep β); F ≤1∧∀ t:ℝ,0 ≤ t→ clocks C t * F * AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads G B L X r x) 0 D.K (2*((n+1)+(n+1))) ≤ sprite G x L z*t
   stand : ∀ p∈Local.tests ((Labels.frames G).level d),∀ (u v:BudgetPoint), Blend 2 v.threshold u.threshold → n ≤ v.order→∀ c f:Side,∀ (S:StepData c f)(T:Tube G S)(X:Support f)(Y: Support c), S.patch.L=L → (∀ i∈X,halo (Heir.reach x) {S.ratio.parent i}⊆Y)→ (∀ i∈Y,separation 0 i ≤ Malachite.radiusD x)→20*(radiusD x+Heir.reach x+1)<c.val→ ∀ V:Flight j i,L=V.L→HEq T.R.A0 (Carrier.linesOf V K.penalty) → ∀ (f':Config G f→ℝ)(t:ℝ),v.Regular X f' → v.supBounds 0 X f' t→Peak.lit 0 X f' d → ‖iteratedDeriv p.2.val (dimW 0 (Malachite.radiusD x) T f' ∘ (hol G).testLinks d 0 (u.threshold • p.1)) 0‖ ≤ sprite G x L z*t
section Li
variable {n:ℕ}(C:Libretto G n)(D:Record) (K:KernelChoices)
lemma decade (L:Side)(i j k l d r a:ℕ)(hi:4 ≤ i)(hj:4 ≤ j)(hd:d≤j)(hn:d ≤ n)(z:ℝ)(hz:0<z):∀ᶠ x in atTop, Loader C D K L j i d a k l r x z:=by
   let V:= Local.tests ((Labels.frames G).level d)
   filter_upwards [Rebuild.geometry (G.slopeConstant*Real.log L.val),garden C D L k l, ((Work.E01.radiusB_tendsto).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop 1,V.eventually_all.mpr (fun p _=> fourrate K.penalty (hol G) p C.rights K.penalty_pos hj hi hd hn L z hz), scales_m C D L k r z hz] with x hp h hx hv hu
   exact ⟨h.1,h.2,hp.1.1,hx,hu,hv⟩
end Li
section Prism
variable (M: ConnectedActivityE6.Target G T)(L:Side)(z:ℝ)(hz:0<z)
include hz
lemma fare_pr : ∀ᶠ x in atTop,∀ (c:Side)(R:Rep G c)(U: Cloud R), Blush.marvel (L:=L) (x:=x) (Q:=M) U ≤ sprite G x L z* (R.p.mass U.live.crest U.live.weight):=by
    have hp:Rate G L (M.rate/4) (poster M L):= Rate.power
    filter_upwards [sprited (fGood hp (by linarith [M.stop])) hz,Delay.shift_pos G L] with x hx h c R U
    let m:= R.p.mass U.live.crest U.live.weight; have hu:0 ≤ m:= U.live.profit.trans (R.p.loMass _ _ U.live.profit)
    let a:= Real.exp (-M.ε*coverNumber R.p.B U.live.crest); have ha:a≤1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr M.usable.le) (by positivity)); change m*a*_ ≤ _
    rw [mul_comm]; exact mul_le_mul ((le_abs_self _).trans hx) (mul_le_of_le_one_right hu ha) (mul_nonneg hu (Real.exp_pos _).le) (sprite_pos _ hz).le
-- gas forced divisor
lemma force_pr (c:ℝ)(hc:0<c):∀ᶠ x:ℝ in atTop, c*glyph (betaF G x L) ≤ sprite G x L z:=by
    have hp: Rate G L (-1) (fun x=> glyph (betaF G x L)):=by
         unfold Blush.glyph; simp_rw [Real.sqrt_eq_rpow,← Real.exp_mul]; refine (Rate.monitor_cutoff (δ:=1/2) (γ:=1/5) (by norm_num : (0:ℝ)<1/2) (by norm_num)).congr (Eventually.of_forall fun x=>?_); change Real.exp (-_*(1/2))=Real.exp (-(1/2:ℝ)*(Delay.fineMonitor G L x)^(1/5:ℝ)); unfold Delay.fineMonitor Vac.Numbers.P; rw[← Real.exp_mul]; ring_nf
    filter_upwards [sprited (fGood (hp.mul_left c) (by norm_num)) hz] with x hx; exact (le_abs_self _).trans hx
end Prism
structure Medal (G:Gauge){P:Teller G} (j i d n:ℕ)(L:Side)(P0 P1: Stage)(K:KernelChoices)(C:Libretto G n)(D:Record)(T:ConnectedActivityE6.Target G P)(w:ℝ)(Q:Target.Order G w)(μ x y z:ℝ)(r:ℕ) where
    eve : Eve j i d n L P0 P1 P K C D T w Q μ x r
    card : eve.current ≤ sprite G x L z
    sail : eve.sail ≤ sprite G x L z
    leader : Loader C D K L j i d 0 P0.power P1.power r x z
    cloud : ∀ c:Side,∀ (R:Rep G c)(U:Cloud R), Blush.marvel (L:=L) (x:=x) (Q:=T) U ≤ sprite G x L z*(R.p.mass U.live.crest U.live.weight)
    talent : Mercury.tuition T L x n P0.power ≤ sprite G x L z
    gas: Doors.rate L *Blush.glyph (betaF G x L) ≤ sprite G x L y
    paid:0<z
    fee : 0<y
section
lemma decorate (j i d n:ℕ)(L:Side)(P0 P1: Stage)(K:KernelChoices)(C:Libretto G n)(D:Record)(M:ConnectedActivityE6.Target G T)(w:ℝ)(Q:Target.Order G w)(μ y z:ℝ)(r:ℕ) (hD:D.ε≤1/4) (hi:4 ≤ i)(hj:4 ≤ j)(hn:2≤ n)(hz:d≤j)(hm:d≤n)(hμ:0<μ)(hy:0<y)(h:0<z):∀ᶠ x in atTop, Nonempty (Medal G j i d n L P0 P1 K C D M w Q μ x y z r):=by
    filter_upwards [bairn (G:=G) L C D K M μ w d j i r P0 P1 Q hD hi hj hn hz hμ z h, decade C D K L i j P0.power P1.power d r 0 hi hj hz hm z h, fare_pr M L z h, force_pr (G:=G) L y hy (Doors.rate L) (Doors.rate_pos _), sprited (fGood (Mercury.tutored (L:=L) M (-1) n P0.power) (by norm_num)) h] with x hx hv hp hu hs
    obtain ⟨H,hx,hZ⟩:= hx; exact ⟨H,hx,hZ,hv,hp,(le_abs_self _).trans hs,hu,h,hy⟩
end
end YM.PhysicalNext.Repeat.Quince
