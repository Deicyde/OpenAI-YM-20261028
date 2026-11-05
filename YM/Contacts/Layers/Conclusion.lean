import YM.Contacts.Layers.Trees
import YM.OPE.Single

/-! # First endpoint: signed estimates supporting the annulus argument -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set Metric MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {W I : Type}
variable {F : Extraction.Order} (Z : Final C F S) (M : Devices Z.sector.derivatives)
structure Assures : Prop where
   moments : ∀ (W I:Type) [Fintype I] (i:I) (R:I→W→ℝ) (U:Set W) A p e, Ticket Z M R U A i p e → (∀ x∈ U,∀ i, R i x∈ Ioc (0:ℝ) 1) → ∀ ε:ℝ, 0<ε → ∃ c>(0:ℝ),∀ t ∈ U,∀ i : Viewers Z, ‖readExpr M.basis (spectator Z i) (e t)‖ ≤ c * p t * surcharges R t ε
   outputs : ∀ (W I:Type) [Fintype I] (i:I) (R:I→W→ℝ) (U:Set W) A p e, Ticket Z M R U A i p e → (∀ x∈ U,∀ i, R i x∈ Ioc (0:ℝ) 1) → ∀ ε:ℝ, 0< ε → ∀ w:ℕ, ∀ x ∈ A, Inspect U (R i) x A → Window M U w x A → ∃ c>(0:ℝ),∀ t∈U, ‖M.row (x t) w (e t)‖ ≤ c*(p t*(R i t)^(w:ℝ))*surcharges R t ε

/-- Chosen detection prescription & all-arities signed subpower estimates for the actual
unselected hierarchy and every character, plus projection estimates. As in `sec:onof`
approach to contact strata, not yet distributional existence through strata. -/
theorem signed_placements (G:Gauge) (h:G.Simple) : ∃ (C:Family G)(F:Extraction.Order)(S:Table C.book)
    (Z:Final C F S) (M:Devices Z.sector.derivatives), M.rotation = Z.sector.turns ∧ Services C F S ∧ Assures Z M := by
  obtain ⟨C,g,S,hs,Z,P,hP⟩:= single G h Extraction.Order.full
  let M : Devices Z.sector.derivatives := ⟨P,hP.coherent,Z.sector.turns,Z.room.kernel,
    Z.phase.transport.injection,Z.phase.transport.rights,Z.phase.transport.spots,Z.phase.transport.motion,
    fun d=> Classical.choice (MultipleContact.detector_exists d S)⟩
  exact ⟨C, _,S,Z,M,rfl,hs,fun W I _ i R U A p e t ht ε he=> t.price hs ht he,
    fun W I _ i R U A p e t ht ε he w x hx hp hh=> t.output_price hs ht he w hx hp hh⟩
#print axioms signed_placements
end YM.Contacts.Layers
