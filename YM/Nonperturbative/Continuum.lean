import YM.Independent.ConstructionRun
import YM.Independent.Core
import YM.Pert.Position.Four
import YM.Contacts.Solstice.Result

set_option autoImplicit false
noncomputable section
namespace YM.Nonperturbative
open Independent Spec OPE.Orbits Contacts.Solstice

universe u v

/-- The ordinary OPE and Euclidean contacts use the same field prescription. -/
theorem contacts_on {G : Gauge} {C : Family G} {p : Extraction.Order} {S : Table C.book}
    (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (services : OPE.Services C p S) :
    ∃ M : Contacts.Devices F.sector.derivatives, M.basis = Q.port ∧ MultipleLight F M ∧
      Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Thresholds M) := by
  let t := F.phase.transport
  let M : Contacts.Devices F.sector.derivatives :=
    ⟨Q.port,Q.spans,F.sector.turns,F.room.kernel,t.injection,t.rights,t.spots,t.motion,
      fun d => Classical.choice (MultipleContact.detector_exists d S)⟩
  exact ⟨M,rfl,provided F M rfl services,Contacts.Transport.real_basis M,
    ⟨(installs M (f := fun _ => 1) (fun _ => zero_lt_one)).choose⟩⟩

/-- Nonperturbative extraction, reconstruction, OPE and contact resolution. The
Wilson family is chosen once and each requested order can then be refined. -/
theorem continuum_with_position_tests {G : Gauge} (hG : G.Simple) {b : ℝ} (hb : 0 < b) :
    let R := fundedRun hG hb
    R.family.path.levels.clock.kernel.penalty = b ∧
    ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table R.family.book)
      (F : Final R.family (p.refine q) S) (L : EveryPhase.Almanac F)
      (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (M : Contacts.Devices F.sector.derivatives),
      (Extraction.Order.mk Extraction.Sequence.full (p.refine q).per).Ordered R.family S ∧
      FullVolume.PositionsUV R.family Extraction.Sequence.full ∧ Core.{u,v} hG F L Q ∧
      OPE.Nesting.Uniform F Q ∧ M.basis = Q.port ∧ MultipleLight F M ∧
      Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Thresholds M) ∧
      ∃ X : Climb.Scaling S, Pert.FirstExtension F X ∧ Pert.Position.FourMeters F X := by
  obtain ⟨T,W,penalty,funded,_⟩ := (constructionRun hG hb).choose_spec
  refine ⟨penalty,?_⟩
  intro p
  obtain ⟨q,_,S,F,X,L,Q,_,ordered,uv,first,reconstruction,trace,service,ope,nested,_,_⟩ :=
    (R2IGoals.fromFunded.{u} W hG funded).refine p
  obtain ⟨M,same,contacts,basis,thresholds⟩ := contacts_on F Q service.toServices
  exact ⟨q,S,F,L,Q,M,ordered,uv,
    Core.of_receipts hG F L Q reconstruction trace service.toServices ope,
    nested,same,contacts,basis,thresholds,X,first,Pert.Position.four_on F X hG first⟩

/-- Nonperturbative extraction, reconstruction, OPE and contact resolution. The
Wilson family is chosen once and each requested order can then be refined. -/
theorem continuum {G : Gauge} (hG : G.Simple) {b : ℝ} (hb : 0 < b) :
    let R := fundedRun hG hb
    R.family.path.levels.clock.kernel.penalty = b ∧
    ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table R.family.book)
      (F : Final R.family (p.refine q) S) (L : EveryPhase.Almanac F)
      (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (M : Contacts.Devices F.sector.derivatives),
      (Extraction.Order.mk Extraction.Sequence.full (p.refine q).per).Ordered R.family S ∧
      FullVolume.PositionsUV R.family Extraction.Sequence.full ∧ Core.{u,v} hG F L Q ∧
      OPE.Nesting.Uniform F Q ∧ M.basis = Q.port ∧ MultipleLight F M ∧
      Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Thresholds M) := by
  obtain ⟨penalty, allOrders⟩ := continuum_with_position_tests.{u,v} hG hb
  refine ⟨penalty, fun p => ?_⟩
  obtain ⟨q,S,F,L,Q,M,ordered,uv,core,nested,same,contacts,basis,thresholds,_⟩ := allOrders p
  exact ⟨q,S,F,L,Q,M,ordered,uv,core,nested,same,contacts,basis,thresholds⟩

end YM.Nonperturbative
