import YM.UVExtension.Payroll.Now
import YM.UVExtension.Linden.Subsidy
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


variable (K: Vision R ε) (Hc:WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
variable {ι:Type}[Fintype ι] {c f:Side}
    (H:f.val=c.val*(A.B.a.S.block m).val) {X':RG.Rep G f} (X0: Chartlet R.shape A N m H X')
    {v:ι→ Juice G f}{w:ℝ}(h:Festa (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) X0 v w (hearts G (D.L (A.B.a.clock.J (m+1))) ((A.B.a.clock.hatBeta m)))) (hv:Fintype.card ι=4)

include K Hc h X0 hm hv R

-- consumed at scale, adjacent H copied literal on accounts
variable (J:(u:Canvas (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) w ι)→ Chartlet R.shape A N m H (freshen u X' v))
    (VW: Zeal R.target R.shape A N m)
lemma liveW (k:ℕ) :
   let V:(Canvas (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) w ι) → Source G c:= fun i=> Concert.shapeP X0 (fleet i J X0) (Rain.screens R.target A m) k (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (A.B.a.budget m) (VW.offers k (stageNote i)) (A.B.kin.alpha N m)
   let C:= Concert.bookA (Beam.marquee X0 (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (A.B.a.budget m)
   (∀ d, smoothP (A.B.a.budget m) C.reg (V d).logRead)∧ Nonempty (ticketR (aperture h) (A.B.a.budget m) C.reg (preExponent (A.B.a.budget m)) (fun i=> (V i).logRead) (fun _=> pay G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))) ∧
     Nonempty (Atlas (bell C.hard (radiusB (A.B.a.clock.hatBeta m)) ((A.B.a.budget m).supportExponent+1)) (aperture h) (fun d i U=> (V d).hardRead i U) (fun _=>Payroll.prize G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) (ε/8)))  ∧ Nonempty (Atlas (Concert.softer (lodge (Beam.marquee X0 (A.B.a.budget m)) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))))) (A.B.a.budget m).B ((A.B.a.budget m).supportExponent+1+1)) (aperture h) (fun i=> (bison (Meadow.timbres (fleet i J X0) (A.B.kin.alpha N m) k (χ:=Chi.canonical)) (Trio.ornament (Rain.screens R.target A m) (VW.offers k (stageNote i))) (Trio.insight (A.B.a.budget m) (fleet i J X0) (A.B.kin.alpha N m) k (Rain.screens R.target A m) (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (VW.offers k (stageNote i)))).logarithm) (fun _=> pay G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))) := by
  intro V C; let W₁:=(A.B.a.budget m); let l:=(Rain.lint R.target A m)
  obtain ⟨hK,⟨L₁⟩,⟨L₂⟩⟩:= rootF R hm K Hc H X0 h hv J
  have hf i:= spherical R hm hv K Hc k i VW stageNote (fun i=>rfl) h.margin h.bound
  let b:=step_paid A.B.a m
  let E:= K (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) b (A.B.a.clock.hatBeta m) (A.B.valid.pays m)
  have hB:=E.alive; have hg : 0 ≤ (clang G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Rain.lint R.target A m) (A.B.a.clock.hatBeta m)):= mul_nonneg (Nat.cast_nonneg _) hB
  let f':=freshW G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) l (A.B.a.clock.hatBeta m)
  obtain ⟨j,hj⟩:= E.changeK
  have hη:=Rain.jersey (A:=A) (m:=m)
  have ht: Time.Same (X.p.profile (A.B.a.clock.J m)) (A.B.a.budget m):= ⟨hη.2.1,hη.1,hη.2.2.1⟩
  have hP:= Payroll.panels G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Rain.lint R.target A m) (A.B.a.clock.hatBeta m) (A.B.a.budget m) ht
  have hq: (A.B.a.budget m).supportExponent+1+1=(X.p.profile (A.B.a.clock.J m)).supportExponent+1+1:=by rw [ht.2.2]
  have hW : tithe (2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))) (((clang G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Rain.lint R.target A m) (A.B.a.clock.hatBeta m))+(clang G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Rain.lint R.target A m) (A.B.a.clock.hatBeta m)))+arenaK ((Rain.moor R.target A m)) (fun _=>(clang G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (Rain.lint R.target A m) (A.B.a.clock.hatBeta m)))) (A.B.a.budget m) (Trio.coverTicket (Rain.lint R.target A m))=f':= by unfold f' freshW whaleK tithe; rw [hP.2.2.1]
  have hX(i: Site c)(y:ℕ) (hy:y≤2*(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)))): (coverNumber W₁.B (neighbors y i):ℝ) ≤ Trio.coverTicket (Rain.lint R.target A m):=by apply Nat.cast_le.mpr; apply (Trio.scaleMeters (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m)) W₁.B_pos i y hy).trans; rw [two_mul]
  rw [←hq] at L₂ -- actually expression (A.B.a.budget m). not SP+1? inspect
  obtain ⟨f,rfl',hp,⟨hY⟩,⟨hV⟩,hA⟩:= celebrateW k (q:=tent (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (Rain.screens R.target A m) (hw:=show tent (Rain.lint R.target A m) _+5≤(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) from le_rfl) (U:=fun i=> freshen i X' v) J (fun i=> fleet i J X0) (fa:=fun i=> VW.offers k (stageNote i)) (p:=(A.B.a.budget m)) (fun d=>rfl) (fun i=>rfl) (fun _=>rfl) rfl L₁ hK L₂ (fun i=>hg) (fun i j x=> (hf i).2 j x) (fun i j d=> (hf i).1 j d) hB (fun i=> hX i (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) (by omega)) (fun i=> hX i _ le_rfl) (hW.trans_le E.run) hj
  subst f
  refine ⟨hp, Concert.broaden _ _ hY (fun z hz=>?_), ⟨hV⟩,hA⟩
  rw [hP.1,hP.2.1,hP.2.2.2]; exact E.seek
end YM.UVExtension.Payroll

