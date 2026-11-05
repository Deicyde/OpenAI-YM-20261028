import YM.R2I.Campaign.Clock
import YM.TraceExtension.Endpoint
import YM.OPE.ElementaryLog
import YM.OPE.Nesting.Endpoint

/-!
# Pay all these construction demands when purchasing the actual Jewel campaign

The usual f756 endpoints on `Uses` don't follow (we did NOT make that
choice of trajectory). But the same `R.kit`, history, schedule and Bandage
have the local estimates of the chosen Decal. The weak measuring frames here
are NOT identified with Trace's own, and are not strong enough for sharp
OPE. No all-order comparison. Does combine Trace.Target, real UV existence
and uniqueness in exactly Jewel's band/successful-trial sense, + Nested
ordinary OPE and EveryPhase on the same Final. Useful analytic instruments for
further progress. Depends neither on the choice of perturbative prescription
nor any additional mathematical premise. See the endpoint for quantifiers.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I
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
open Campaign
set_option quotPrecheck false
open Boutique
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. Again from DensityClock.lean. -/
lemma engage (h:G.Simple){q:ℕ→ℕ} (Δ : Daisy.Charity.RG12.Decal G) (hQs:Tendsto q atTop atTop)
    (hU:Attentive b q) (hQ:Mallow.AccordV X.shape q A.delay) (hBa: Extras Δ b) (hYf:Mallow.FrameAccord X.target P A.delay)
    (h100:∀ i,(A.B.a.params i).supportExponent = 100){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧
      Extras Δ R.b ∧ Attentive R.b R.Q ∧ (∀ i,(R.alloy.B.a.params i).supportExponent=100) ∧
      Tendsto R.Q atTop atTop ∧ Mallow.FrameAccord R.kit.target R.rolls R.alloy.delay ∧ ∃ Θ, Sky R T Θ v :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hU.ahead,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩
    exact ⟨R,T',⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,hQ,hBa,hU,h100,hQs,hYf,θ1,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩
end

open Daisy.Charity.RG12
structure Funded (Δ : Decal G) (R : Run G) (T : Campaign R) : Prop where
    localBudget : Extras Δ R.b
    attentive : Attentive R.b R.Q
    logCopy : Tendsto R.Q atTop atTop
    locrian : Locrian R
    wild : Jams.Wild R.kit.shape R.alloy.delay
    silk : Mallow.FrameAccord R.kit.target R.rolls R.alloy.delay
    poly : Mallow.AccordV R.kit.shape R.Q R.alloy.delay
    fixed m : (R.alloy.B.a.params m).supportExponent=100
    tic : OPE.Log.OnBudget R.alloy.B.a
    halo : OPE.HaloGate R.family.path.levels
    paced : Flick R.family.path.levels
    stoves : OPE.Therm.Poetry R.family.path.levels
    hasSky : ∃ (v:ℕ→ℕ→ℝ), ∃ Θ, Sky R T Θ v

theorem selectRun {Λ: Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL:EventuallyPaid Λ) :
    ∃ (R:Run G)(T:Campaign R), R.family.path.levels.clock.kernel.penalty=b ∧
      Λ R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T := by
  let Q (i:ℕ):= i+2
  obtain ⟨M,P,A,X,Y,K,c,H,hAmp,hWild,hB,hF,hP,hX,hT,hY,hK,hQ,hHalo,hΛ,hA,
    ξ,v,t,a,D,Φ,θ1,hν,hφ,hv,hψ,UΩ,hP',hZ⟩ := allFactor h hb Δ Q (fun i j hij=>Nat.add_le_add_right hij _) (fun _=>Nat.le_add_left ..) Λ hL
  obtain ⟨R,T,hR,hG,hN,hW,hU,hK',hA',hAddr,hlim,hS,Θ,hΘ⟩ :=
    engage h Δ (q:=Q) (tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id) hA hQ hK hY hX Φ H hAmp hWild θ1 UΩ hν hφ hP' hv hψ hZ
  rw [← hW] at hB hF hHalo hT hΛ hP
  exact ⟨R,T,hB,hΛ,hN,hK',hA',hlim,hR,hG,hS,hU,hAddr,hT,hHalo,hF,hP,UΩ,Θ,hΘ⟩

namespace Funded
variable {Δ:Decal G} {R:Run G} {T:Campaign R} (W:Pillars R T) (hG:G.Simple) (h:Funded Δ R T)
include h hG
lemma jewel : FullVolume.Final.Jewel R T W := by
  obtain ⟨v,Θ,hV⟩ := h.hasSky
  exact FullVolume.Final.jewelOf17 T W hG h.locrian h.wild v Θ hV
omit hG
lemma gallery (F:Extraction.Order) : Trace.Over.Gallery R.family F := by
  obtain ⟨-,-,-,-,-,-,-,hf,_⟩ := h.attentive R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  exact (hf F).2
lemma coverage : SharpGram.Dense.Coverage R.family R.makes := by
  obtain ⟨-,-,-,-,-,-,-,-,hm,H⟩ := h.attentive R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  exact H
include hG W
lemma logPackage : OPE.Log.LogPackage R.family R.w (mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨v,Θ,hV⟩ := h.hasSky
  obtain ⟨hT,-⟩ := R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  refine ⟨opePackage17 W hG h.poly h.halo hV,
    exodusL hG R.b R.T R.Q R.t R.stories R.doors hT hV.supports h.poly hV.fee h.silk, h.tic,?_, h.fixed⟩
  apply h.logCopy.comp
  exact tendsto_atTop_mono (f:=R.family.path.levels.clock.J) (fun i=> R.family.path.levels.fits.mono i.le_succ) R.family.path.levels.fits.deep
end Funded
end YM.PhysicalNext.Repeat.Legato.R2I

namespace YM.R2IGoals
set_option maxHeartbeats 1200000
open Function Filter PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12 R2I
open YM.FullVolume YM.FullVolume.Final Extraction Campaign
open scoped Topology BigOperators Classical

universe u
variable {G:Gauge} {R : Run G} {T : Campaign R}

/-- Same-Broad-supply baseline for further work.

The two coefficient APIs
use their actual Reader/Prescription.

The rotation-equivariant OPE recipe
IS NOT identified with the raw `AllShapes` (theorem below about every
coherent prescription).

Includes universal every
phase reconstruction and Trace results at their exact domains. -/
structure Broad (Δ : Decal G) (W : Campaign.Pillars R T) (h:G.Simple) : Prop where
  paid : Funded Δ R T
  jewel : Jewel R T W
  logBudget : OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors
  coverage : SharpGram.Dense.Coverage R.family R.makes
  trace : ∀ (f:Extraction.Order) (S : Table R.family.book) (F:Spec.Final R.family f S), Trace.Target.Result.{u} F h
  refine (f:Extraction.Order) : ∃ (g:Extraction.Order) (B:ℕ→ℝ)
      (S:Table R.family.book) (F:Spec.Final R.family (f.refine g) S)
      (X:Climb.Scaling S) (L:EveryPhase.Almanac F)
      (P:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
    (∀ m:ℕ,(f.refine g).limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) ∧
    (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S ∧
    PositionsUV R.family Extraction.Sequence.full ∧
    Pert.FirstExtension F X ∧ EveryPhase.Completed F L ∧
    Trace.Target.Result.{u} F h ∧
    OPE.Facilities R.family (f.refine g) S ∧ OPE.Orbits.Foundation F P ∧
    OPE.Nesting.Uniform F P ∧
    (∀ p:OPE.Prescription F.sector.derivatives,p.Coherent → OPE.AllShapes F p) ∧
    (∀ U:Ultrafilter (ℕ×ℕ), (U:Filter _) ≤ (f.refine g).fuse → Nonempty (SharpGram.Lenses.Mantle F (U:Filter _)))

lemma fromFunded {Δ:Decal G} (W:Pillars R T)(h:G.Simple)(H:Funded Δ R T) : Broad.{u} Δ W h:= by
  have hJ := H.jewel W h
  have he := H.logPackage W h
  have hR (f:Extraction.Order) (S : Table R.family.book) (F:Spec.Final R.family f S) : Trace.Target.Result.{u} F h :=
    Trace.Target.assembled F h (Trace.arenaT F h (Trace.crest_ready F h (H.gallery f)))
  refine ⟨H,hJ,he,H.coverage,hR,fun f=>?_⟩
  obtain ⟨g,B,hB⟩ := PertExtension.Running.extraction R.family hJ.actual f
  obtain ⟨w,S,F,X,hS,hX⟩:= R.extractible17 h he.toPackage (f.refine g)
  obtain ⟨L,hL⟩:= EveryPhase.all_characters F
  let t:=F.phase.transport
  obtain ⟨p,hp⟩:= OPE.Prescription.chosen F.room.kernel.laws.toSymmetric t.injection
  let r:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin := ⟨p,hp,F.room.kernel,t.injection,t.rights,t.spots⟩
  have hb m:=Extraction.Order.retained (g:=w) (hB m)
  have hf : f.refine (g.refine w) = (f.refine g).refine w := rfl
  refine ⟨g.refine w, ?_⟩; rw [hf]
  exact ⟨B,S,F,X,L,r,hb,from_spec ((f.refine g).refine w) ⟨F⟩ hJ.fullMesh,hJ.fullMesh,hX,hL,
    hR _ S F,⟨hS,_,_,_,he⟩,OPE.Orbits.produce F r hS,OPE.Nesting.uniform F r hS,
    fun p hp=> hS.everything F p hp,fun U hu=> SharpGram.Lenses.attains_mantle17 F hS U hu H.coverage⟩

theorem investPlan (h:G.Simple)(b:ℝ)(hb:0 < b)(Δ:Decal G){Λ:RG.Levels G→Prop}(hL:EventuallyPaid Λ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = b ∧ Λ R.family.path.levels ∧ Broad.{u} Δ W h := by
  obtain ⟨R,T,hB,hΛ,⟨W⟩,hK⟩:= selectRun Δ b hb h hL
  exact ⟨R,T,W,hB,hΛ,fromFunded W h hK⟩
theorem commencement (h:G.Simple)(b:ℝ)(hb:0 < b) (Δ:Decal G):
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = b ∧ Broad.{u} Δ W h := by
  have he:EventuallyPaid (fun _ : RG.Levels G=>True):= fun _ _ _ V => ⟨V,Push.PriceCompiler.DelayLe.refl _,by intros; trivial⟩
  obtain ⟨R,T,W,hB,-,h⟩:= investPlan.{u} h b hb Δ he
  exact ⟨R,T,W,hB,h⟩
end YM.R2IGoals
#print axioms YM.R2IGoals.commencement
