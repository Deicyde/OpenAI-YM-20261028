import YM.UVExtension.Payroll.Lunar
import YM.UVExtension.Concert.Sheet

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Payroll
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ} (hm:m<N) {ε:ℝ}

variable {ι:Type}[Fintype ι] (hv:Fintype.card ι=4)
variable (K:Vision R ε)(Hc:WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))

abbrev BandCanvas (w:ℝ) (ι:Type):= Canvas (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) w ι
-- real membership beta
omit [Fintype ι] in lemma splash {z:ℂ} (hx:z∈ Wick.aisle (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))))) : z.re ∈ band A.B.a (m+1) :=by
  rw [← PriceCompiler.beta_eq A.B.valid m] at hx; exact ⟨hx.1.le,hx.2.1.le⟩

def vacancy (G:Gauge)(ι:Type)(n:Side):ι→ Juice G n:= fun _=>⟨0,0⟩

variable (k:ℕ)(i:Stars) (T : Zeal R.target R.shape A N m){w:ℝ} (u:(d:Canvas (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) w ι)→Rain.lands A m) (he:∀ d,(u d).val=d.val none) (hx:0<w) (hV:w≤hearts G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))

include T hx hV he K Hc hm hv
lemma spherical : let l:=(clang G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Rain.lint R.target A m) (A.B.a.clock.hatBeta m))
   (∀ y d, (A.B.a.budget m).Regular Finset.univ (T.offers k (u d) i y)) ∧ ∀ y (v:Fly G (Rain.moor R.target A m i) (A.B.a.budget m)), Charm (normal (show 0<betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))) by rw [← PriceCompiler.beta_eq A.B.valid m]; exact zero_lt_one.trans (A.B.a.fits.delayed _)) hx hV) l (fun d=>v.reel (T.offers k (u d) i y)):=by
  intro l
  let S:=R.target
  let BandD:=BandCanvas (A:=A) (m:=m) w ι
  let J:= Boulevard.phase A m -- lowercase
  let H:= (Rain.panes R.target A m i); let Y:= T.tiers i J
  let P':=(Rain.Racks S A N m i J.val); let G' := vacancy G ι (Rain.pink R.target A m i)
  have hP (d: BandD): freshen d P' G'=Pane.virgin (Pane.orchestra A N H) (A.B.a.budget (m+1)) (u d).val:= by
    simp_rw [he d]; have hp: blend G' (d.val ∘ some)= (⟨0,0⟩:Juice G _) := by unfold blend; congr 1 <;> ext <;> simp [vacancy,G']
    unfold freshen; rw [hp]; rfl
  have hF:Festa _ (D.L (A.B.a.clock.J (m+1))) Y G' w (hearts G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)):=by
    refine ⟨hx,hV,fun z hz=> ⟨T.tiers i ⟨z.re,splash hz⟩⟩,fun _ z hz=> ⟨T.tiers i ⟨z.re,splash hz⟩⟩,fun d hd=> ?_⟩
    change Nonempty (Chartlet R.shape A N m H (freshen (show BandD from ⟨d, hd⟩) P' G')); exact ⟨(hP ⟨d,hd⟩).symm ▸ (T.tiers i (u ⟨d,hd⟩))⟩
  let a' (d : BandD): Chartlet R.shape A N m H (freshen d P' G'):= (hP d).symm ▸ (show Chartlet R.shape A N m H _ from T.tiers i (u d))
  obtain ⟨hp,⟨hg⟩,-⟩:= rootF R hm K Hc H Y hF hv a'
  have he d: Cousin _ _ := show Cousin (Rain.Racks R.target A N m i (↑(u d))) (freshen d P' G') from by
    let h : Rain.Racks R.target A N m i (↑(u d))=freshen d P' G':= (hP d).symm; rw [h]; exact ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
  let f d:=(Song.plusone Y (fleet d a' Y) Chi.canonical (A.B.kin.alpha N m)).logRead
  have hR y d: T.offers k (u d) i y= Concert.heir Y k f y (A.B.a.budget m) d:= by
    rw [show T.offers k (u d) i= Meadow.barony (a' d) Chi.canonical k (A.B.kin.alpha N m) from samePrint (J:=T.tiers i (u d)) (A.B.a.budget m) k (A.B.kin.alpha N m) (χ:=Chi.canonical) (he d)]
    exact Meadow.aster Chi.canonical (A.B.a.budget m) (fleet d a' Y) rfl rfl rfl (A.B.kin.alpha N m) k y
  simp_rw [hR]; exact ⟨fun y=> smoothie Y k _ y hp,fun y v=> sherbet Y k _ y rfl hg v hp⟩
end YM.UVExtension.Payroll
