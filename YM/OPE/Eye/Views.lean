import YM.OPE.Eye.Word
import YM.OPE.Cards.Pressure
import YM.Work.B05
import YM.Work.B04
import YM.Work.B03

/-! # Observation on the actual selection, including its law readout

`Viewers` includes the hierarchy *and* each character (not just the chosen phase).
An eventual bound quantifying over `Viewers` inside a cutoff-independent estimate is
uniform in the phase. Note the normalization on the unselected option.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Lattice RG Wilson MergeProof Source Bid OS Ground Spec
open Extraction Word
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{C:Family G} {V I : Type}[Fintype I]{S: Table C.book}{F:Extraction.Order}(U:Final C F S)
variable (h:Org.Grill C F)
lemma theme : Theme U.α.room U.α.unselected := Work.B03.answer U.room.kernel _ U.α.room U.α.unselected U.phase.phase.still U.phase.phase.lengths
include h in
lemma reflective : Org.Phase.reflects (C:=C) U.α.room U.α.unselected:= Work.B05.answer Work.B04.answer U.room h U.sector U.phase.transport U.α.room U.α.unselected U.phase.phase.still (theme U)

abbrev Viewers := Option U.α.space.X
def spectator (v:Viewers U): Table C.book:= v.elim S U.α.ensemble

@[simp] lemma unselected_view : spectator U none=S:=rfl
@[simp] lemma any_selected (i:U.α.space.X) : spectator U (some i)=U.α.ensemble i:=rfl
lemma spectate (v : Viewers U): (spectator U v).Hierarchy := by cases v <;> first| exact U.room.kernel| exact U.phase.phase.states _
lemma spectate_respects (v : Viewers U): (spectator U v).respects S:=by
    cases v with
    | none=>exact fun _=>le_rfl
    | some v=> exact fun i => (U.phase.phase.retains v i).symm.le -- direction
lemma spectate_ready (v: Viewers U) : U.sector.derivatives.Inclusions (spectator U v):=by
    cases v; exact U.phase.transport.injection; exact U.phase.phase.coordinates _
lemma spectate_evolution (v : Viewers U) : U.sector.derivatives.Derivatives (spectator U v):=by
    cases v; exact U.phase.transport.derivatives; exact U.phase.phase.calculus _

local notation "A"=> U.α.unselected
local notation "R"=> U.α.space
-- abbreviation for reading words

def viewing (x:I→E4)(v:I→ C.book.Token): U.α.unselected.algebra:= if h:Injective x then M U.α.unselected (worded x v) ((worded_distinct ..).2 h) else 0
lemma character_sees (i:U.α.space.X) (x:I→ E4)(v:I→ C.book.Token)(h:Injective x) : U.α.space.character i (viewing U x v)=observe (U.α.ensemble i) x v:=by rw [viewing, dif_pos h]; exact Retain.pops A R (U.phase.phase.chosen _) _ _
local notation "ω"=> U.α.room.omega0

def glance (v: Viewers U) : (A|>.algebra)→ₗ[ℂ] ℂ:= v.elim
    { toFun f:= inner ℂ U.α.room.omega0 (f.val U.α.room.omega0)
      map_add' a b:= by change inner ℂ ω (a.val ω+b.val ω)=_; rw [inner_add_right]
      map_smul' t a:= by change inner ℂ ω (t • a.val ω)=_; rw [inner_smul_right]; rfl } (fun i=> (U.α.space.character i).toAlgHom.toLinearMap)
-- actually map_smul proof redundant?
lemma glance_sees (i:Viewers U)(x:I→E4)(v:I→ C.book.Token)(h:Injective x): (glance U i) (viewing U x v)=observe (spectator U i) x v:=by
    cases i with
    | some i=> exact character_sees U i x v h
    | none=>
      obtain ⟨s,d,hd⟩:= Spread.Resolution.place_exists ((worded_distinct v).2 h)
      rw [viewing,dif_pos h,Ground.overline A U.phase.phase.still (worded x v) _ s hd]; change inner ℂ ω _= _; rw [Spread.insertValue]; exact invariance U.room.kernel.translations ((worded_distinct v).2 h) s
lemma glance_bound (v : Viewers U)(f:U.α.unselected.algebra): ‖glance U v f‖≤ ‖f‖:=by
    cases v with
    | some v=> exact Cards.pressure_character U.phase.phase.decomposition f v
    | none=>
       have hω: ‖ω‖=1:= nil_norm U.α.room.GNS U.room.kernel.laws
       calc ‖inner ℂ ω (f.val ω)‖ ≤ ‖ω‖*‖f.val ω‖ := norm_inner_le_norm ..
            _ ≤ ‖ω‖*(‖f.val‖*‖ω‖):= mul_le_mul_of_nonneg_left (f.val.le_opNorm _) (norm_nonneg _)
            _ = ‖f‖:=by rw [hω,one_mul,mul_one]; rfl
lemma glance_contract {f:U.α.unselected.algebra}{c:ℝ}(hc:0≤c): ‖f‖ ≤ c ↔ ∀ i:Viewers U, ‖glance U i f‖ ≤c:= by
    refine ⟨fun h i=> (glance_bound U i f).trans h,fun h=> (Cards.pressure U.phase.phase.decomposition f hc).2 (fun i=> h (some i))⟩
end YM.OPE
