import TraceBridge
import ContactSpec
import ContactBridge
import YM.Nonperturbative.Headlines

/-! One construction witness gives the public result and the detailed release clauses. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE.Orbits YM.Nonperturbative
universe u v

/-- The penalty is fixed before choosing the family. The table, phases, fields, OPE reader
and contact devices are then chosen once for each refinement. -/
theorem constructed (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) (hb : 0 < b) :
    ∃ C : YM.Family g.core, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
      WilsonRegularity (wilsonFamily C) ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Final C (p.refine q) S) (L : EveryPhase.Almanac F)
        (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
        (M : Contacts.Devices F.sector.derivatives) (X : Climb.Scaling S),
        (hierarchy F Q).Properties (p.refine q).per ∧ (hierarchy F Q).Contacts ∧
        (Extraction.Order.mk Extraction.Sequence.full (p.refine q).per).Ordered C S ∧
        FullVolume.PositionsUV C Extraction.Sequence.full ∧ Spec.Calibrated C ∧
        Independent.Core.{u,v} (GaugeGroup.coreSimple hg) F L Q ∧
        Headline.Reconstruction F L ∧
        (∀ i, (view (L.actors i)).Axioms) ∧
        Headline.SeparatedOPE F Q ∧ Headline.NestedOPE F Q ∧ Headline.TraceExclusions.{u,v} F ∧
        M.basis = Q.port ∧ Contacts.Solstice.MultipleLight F M ∧
        Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Contacts.Solstice.Thresholds M) ∧
        Pert.FirstExtension F X ∧ Pert.Position.FourMeters F X := by
  obtain ⟨C,penalty,makes,orders⟩ := Nonperturbative.existence.{u,v} g.core (GaugeGroup.coreSimple hg) b hb
  refine ⟨C,penalty,makes,regular C hg makes,fun p => ?_⟩
  obtain ⟨q,S,F,L,Q,M,X,ordered,uv,cal,core,recon,ope,nested,trace,same,contacts,basis,thresholds,first,four⟩ := orders p
  exact ⟨q,S,F,L,Q,M,X,
    ⟨wilsonLimit F Q ordered, publicReconstruction F Q L core.reconstruction,
      publicOPE F Q ope, publicTrace F Q hg trace⟩,
    contactDistribution F M contacts, ordered,uv,cal,core,recon,
    fun i => view_axioms _ (core.reconstruction.isTheory i),
    ope,nested,trace,same,contacts,basis,thresholds,first,four⟩

end YangMills
