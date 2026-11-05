import YM.RG17.Witness
import YM.FullVolume.EveryPhase
import YM.OPE.Orbits.Kernel
import YM.Pert.FirstTarget
import YM.PertExtension.Running

/-!
# Extending the extraction

Same July witness format, keep the extra receipts all the way to
consumer. Uses the same full-volume provider construction, with added
halo delay and AccordV retained; does NOT claim arbitrary R chosen only
according to uv_and_every_phase would support this. Includes Running.limits
on this refined order, and early separated correlation and OPE estimates.
Not comparisons through positive perturbative orders.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open Spec Climb

section compare
open Pert Maxwell Org Next.UVStress
variable {C:Family G}
-- Factor the FirstExtension part from the baseline FirstTarget.
private lemma attached {S:Table C.book} {f : Extraction.Order} {I : IR (C:=C) S} {W : DiffPlan S}
    {M : MaxwellData C} {X : Scaling S} (p : Pert.Supplier f W M I X) {c U J} (h : Tab S W M I p.uv c U J)
    (F:Spec.Final C f S) (eqb:F.sector=⟨W,mill M I c U,J⟩) (hg:G.Simple)
    (hd : M.T.W=Maxwell.Free.scheme C.labels) (hK : M.T.K=Maxwell.Free.gear C.labels)
    (hj : M.T.J=YM.UVNext.FreeStress.torch C.book.grid 1) : Pert.FirstExtension F X := by
  have hm : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hg hd hj,inv_neg,inv_one,neg_smul,one_smul,hj,common_stress]
    rfl
  have he : F.sector.derivatives=W := congrArg Spec.Algebra.derivatives eqb
  refine ⟨?_,fun n j q is a K hp hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : F.sector.energy=J)]
    have hh := mixed_leading p h q is a j hp hsep he
    rw [hm] at hh; exact hh
  · revert he; cases F with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hK]
  exact rotation_lead p h d j
end compare
open Next.UVStress Analysis Org Acme

set_option maxHeartbeats 800000 in
theorem Run.extractible17 (R:Run G) (hG:G.Simple)
    (L:OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (f:Extraction.Order) : ∃ (g:Extraction.Order) (S:Table R.family.book)
      (F:Spec.Final R.family (f.refine g) S) (X:Climb.Scaling S),
      OPE.Services R.family (f.refine g) S ∧ Pert.FirstExtension F X := by
  obtain ⟨hT,hq,hV,-,-,-,-,hW⟩:= R.bought _ R.tuning.receipts _ R.accepts R.stories R.doors R.makes R.carries R.books
  obtain ⟨hc,hF,hQ,hS,hCn,B',-,-,U',F',X',-,h'⟩:= hT.reception
  let C:=R.family
  have hv: Ribbons.Created C:= ⟨_,R.t,R.stories,rfl⟩
  have hπ:Acme.Aroma C:= ⟨Ribbons.laurelE C hG hS hV hq hv hF,hq, Ribbons.fugacious C hG hV⟩
  obtain ⟨g,A,L',R',z,S,E,h,hA,s,hN⟩:= h' f
  obtain ⟨T₀,hM0,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M, hJ, hM, hK, _, _, ht0, hd⟩ := YM.UVNext.FreeStress.fire hG T₀ 1 one_ne_zero
  have hh := M.hT.smooth
  have hG' : East.CompleteWeak C (f.refine g):= hW _
  have hs := grilled C hF hS hq s.copies
  have hL := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=>
    hG' N D R (zero_lt_one.trans_le hr) hh _)
  obtain ⟨hf,I,X,hI,hX,hY,hZ,hM',hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready
    hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hL hπ
  let p : Pert.Supplier (f.refine g) E M I X :=
    ⟨⟨s,hf,hp,ha,hs⟩,hA.clean.ready,hA.clean.tilt,hI,hX,hd,hY,hZ,hM'⟩
  have ht := Bid.station M E I p.uv YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c, U, J, H, K, hK'⟩ := ht.picks E M I p.uv p.ider p.deriv
  obtain ⟨F,hFa⟩:= Pert.withFinal hc p.uv c U J H hK'
  refine ⟨g,S,F,X,⟨hs,hG,⟨_,_,_,L⟩,A,L',R',E,hA⟩,
    attached p H F hFa hG (hM.trans (congr_arg Lighthouse.W hM0)) (hK.trans (congr_arg Lighthouse.K hM0)) hJ⟩
end YM.PhysicalNext.Repeat.Legato

namespace YM.FullVolume.Final
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open Campaign Campaign.Face RG.Shoot Pass Muse Contest Ovens
open Extraction Extraction.Lease FullVolume.Amp FullVolume.Amp.Beam FullVolume.Ray
variable {G:Gauge} {R:Run G}

-- Factor july so we can use this R T W.
theorem jewelOf17 (T:Campaign R) (W:Pillars R T) (h:G.Simple) (hC:Locrian R) (hJ:Jams.Wild R.kit.shape R.alloy.delay)
    (v:ℕ→ℕ→ℝ) (Θ:Luna.Tableau T.width 300) (hk:Campaign.Sky R T Θ v) : Jewel R T W := by
  have H := offers T hC hJ
  have hP := realUV H W hJ
  refine ⟨R.makes,⟨Θ,v,hk⟩,fun f => ?_,fun p N => T.goes N p,
    fun N p => T.L.supplier h, H, wins T H, bareTrial T H,
    fun m p => ⟨saved R.makes.wilson m p, field_independent R.makes.wilson h m p⟩,
    genuine _ h, hP, clients H hJ Θ v hk⟩
  obtain ⟨g,S,hS⟩ := (R.again h).2 f
  exact ⟨g,S,hS,from_spec (f.refine g) hS hP⟩
end YM.FullVolume.Final

namespace YM.RG17
set_option maxHeartbeats 1200000
open Function Filter YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open YM.FullVolume YM.FullVolume.Final Extraction Campaign
open scoped Topology BigOperators Classical

/-- Full-volume UV and every-phase joint endpoint with OPE Services and
an ordinary exact OPE Reader, weak leading correlation estimates (as
`FirstExtension`), actual beta limits all fixed levels. Still not
physical Wilson perturbative comparison. Same hierarchy, fields, and
`Pillars`; this selects ONCE on a schedule further paying halos. -/
theorem supplies (G:Gauge) (h:G.Simple) (δ:ℝ) (hd:0<δ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = δ ∧ Jewel R T W ∧
      ∀ f : Extraction.Order,
        ∃ (g : Extraction.Order) (S : Table R.family.book)
          (F : Spec.Final R.family (f.refine g) S),
          (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S ∧
          PositionsUV R.family Extraction.Sequence.full ∧
          ∃ (L : YM.EveryPhase.Almanac F) (P:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
              (X:Climb.Scaling S) (B:ℕ→ℝ), YM.EveryPhase.Completed F L ∧
              OPE.Services R.family (f.refine g) S ∧ OPE.Orbits.Foundation F P ∧ Pert.FirstExtension F X ∧
              (∀ m:ℕ,(f.refine g).limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) ∧
              PertExtension.Running.isLimit R.family (f.refine g) B := by
   obtain ⟨R,T,hT,hY,⟨W⟩,hP,hV,hG,v,Θ,hW⟩:= Campaign.operaShip17 h δ hd
   have J:= jewelOf17 T W h hT hY v Θ hW
   have he:= Campaign.opePackage17 W h hV hG hW
   refine ⟨R,T,W,hP,J,fun f=>?_⟩
   obtain ⟨g,B,hB⟩ := PertExtension.Running.extraction R.family J.actual f
   obtain ⟨w,S,F,X,hS,hX⟩:= R.extractible17 h he (f.refine g)
   obtain ⟨L,hL⟩:= EveryPhase.all_characters F
   let t:=F.phase.transport
   obtain ⟨p,hp⟩:= OPE.Prescription.chosen F.room.kernel.laws.toSymmetric t.injection
   let r:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin := ⟨p,hp,F.room.kernel,t.injection,t.rights,t.spots⟩
   have hb m:=Extraction.Order.retained (g:=w) (hB m)
   have hf : f.refine (g.refine w) = (f.refine g).refine w := rfl
   refine ⟨g.refine w, ?_⟩
   rw [hf]
   exact ⟨S,F,from_spec ((f.refine g).refine w) ⟨F⟩ J.fullMesh,J.fullMesh,L,r,X,B,
     hL,hS,OPE.Orbits.produce F r hS,hX,hb,fun m=> Order.along (hb m)⟩
end YM.RG17
#print axioms YM.PhysicalNext.Repeat.Legato.Run.extractible17
#print axioms YM.FullVolume.Final.jewelOf17
#print axioms YM.RG17.supplies

#print axioms YM.PhysicalNext.Repeat.Legato.attached
