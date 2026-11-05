import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Staunch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Geometry
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Refit

/-!
# Turn a forest slice and all actual U arguments in one call

Not treating a repeated Y argument as a fresh one. Includes the varying
coarse-field-dependent inverse-leg transport via THE replica, not via U
or its tag outcome. In particular necessary for preserving Y-charge in a
later combined integrand rather than postulating same chart formulas after
selection. χ of E6 here. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
open ConnectedActivityE6 Shell Coat SliceRows
open Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (s : Signed) (b : Site c)

-- instantiate component k families through inverse choices
variable (F : Forest S.ratio)
def glide (Y : F.Slice G) : (Locations.forest s b F).Slice G := fun i =>
    if s.flip i.val.2 then (Y (Locations.free s b F i))⁻¹ else Y (Locations.free s b F i)

lemma forest_toll (G : Gauge) : MeasurePreserving (glide (G:=G) s b F) (F.order G) ((Locations.forest s b F).order G) := by
  let j:=Locations.free s b F
  have hj := (measurePreserving_piCongrLeft (fun _=> G.probHaar) j).symm
  let g (i : (Locations.forest s b F).Free) (x : G.El) := if s.flip i.val.2 then x⁻¹ else x
  have hg i : MeasurePreserving (g i) G.probHaar G.probHaar := by unfold g; split; exact G.preserve_inv; exact MeasurePreserving.id _
  exact (measurePreserving_pi _ _ hg).comp hj

lemma forward (Y : F.Slice G) : (Locations.forest s b F).drape (glide s b F Y) = pull s (S.ratio.embed b) (F.drape Y) := by
  funext i
  rw [read_back]
  let H:=Locations.forest s b F
  by_cases he : i ∈ H.trunks
  · rw [show (Locations.forest s b F).drape _ i = _ from H.on_tree (glide s b F Y) ⟨i,he⟩, show F.drape Y _=1 from F.on_tree Y ⟨_,(Locations.trunk_map ..).mp he⟩]
    split <;> simp
  let v : H.Free := ⟨i,he⟩
  rw [show (Locations.forest s b F).drape _ i = _ from H.off_tree (glide s b F Y) v, show F.drape Y (sendEdge s (S.ratio.embed b) i) = Y (Locations.free s b F v) from F.off_tree Y (Locations.free s b F v)]; rfl

variable {F} {T : Tube G S}


structure Parked (X : Coat T F) (Y : Coat T (Locations.forest s b F)) : Prop where
  seeds : Y.seeds = Locations.book s b X.seeds
  x : Y.x=X.x
  v : Y.V=pull s b X.V
structure Tuned (X : Coat T F) (Y : Coat T (Locations.forest s b F)) : Prop extends Parked s b X Y where
  χ : Y.χ=X.χ
  width : Y.width=X.width
  way : Y.k=Channels.ticket s b X.k
  held : Y.Y=glide s b F X.Y
variable (X : Coat T F)

abbrev wheels (V : Config G c) := lifting (fiber s b V S) (diagram s b S)



namespace Parked
variable {s b X} {Y : Coat T (Locations.forest s b F)} (h : Parked s b X Y)
include h
lemma aligned : Y.t=X.t ∧ Y.B=X.B ∧ Y.R=X.R := ⟨congr_arg (fun x=> Pressure.fiery G x S.patch.L) h.x,congr_arg radiusB h.x,congr_arg Pressure.Stores.till h.x⟩
lemma eligible (i : Bond f) : Y.Hot i ↔ X.Hot (diagram s b S i) := by rw [Hot,h.seeds,h.aligned.2.1]; exact remains_hot ..
lemma panel (i : Mention c f) : Y.selected i.1 (spot S i.2) ↔ X.selected (perChannel s b S i).1 (spot S (perChannel s b S i).2) := label_selection s b h.x h.seeds i
lemma pans (u : Directions G f) : Y.lens (wheels (S:=S) s b X.V u) = wheels (S:=S) s b X.V (X.lens u) := by
  funext i; by_cases hu : Y.Hot i <;> unfold lens wheels <;> first
    | rw [if_pos hu, lifting_apply, lifting_apply, if_pos ((h.eligible i).1 hu)]
    | rw [if_neg hu,lifting_apply,if_neg (mt (h.eligible i).2 hu),map_zero]
end Parked
namespace Tuned
variable {s b X} {Y : Coat T (Locations.forest s b F)} (h : Tuned s b X Y) {W C : ℝ}
include h
lemma completed (u : Directions G f) : Y.input (wheels (S:=S) s b X.V u)=pull s (S.ratio.embed b) (X.input u) := by
  funext i; let q:=diagram s b S i
  have he := Channels.lift_turn (S:=S) s b X.V u
  by_cases hu : Y.Hot i
  · rw [Y.viewing _ _ hu,h.v,wheels,he,read_back,read_back]; rw [show X.input u (sendEdge s (S.ratio.embed b) i)=_ from X.viewing u (sendEdge s (S.ratio.embed b) i) ((h.toParked.eligible i).1 hu)]
  · rw [Y.dormant _ i hu,h.held,forward,read_back,read_back]; rw [show X.input u (sendEdge s (S.ratio.embed b) i)=F.drape X.Y (sendEdge s _ i) from X.dormant u q (mt (h.toParked.eligible i).2 hu)]
lemma saving (ht : ShellAccess S G X.x W X.width C) : Y.saved=wheels (S:=S) s b X.V X.saved := by
  funext i
  rw [wheels,lifting_apply]
  unfold saved; have hp := Locations.trunk_map s b F i; change i∈_ ↔ diagram s b S i∈F.trunks at hp
  rw [if_congr (or_congr hp (h.toParked.eligible i)) rfl rfl]; split
  · rw [map_zero]
  unfold small; rw [h.v,h.χ,h.width,h.toParked.aligned.1,h.held,forward,Locations.replica_move, Channels.read_back, Channels.read_back]
  unfold fiber scatter; split
  next h =>
    let v:= replica S.ratio X.V (diagram s b S i); let u:= F.drape X.Y (diagram s b S i)
    change cutLog X.χ _ (u⁻¹ * v⁻¹⁻¹) = -G.adjoint v⁻¹ (cutLog X.χ _ (u*v⁻¹))
    rw [show u⁻¹*v⁻¹⁻¹ = (v⁻¹*(u*v⁻¹)*v⁻¹⁻¹)⁻¹ by group,ht.log.inverse,ht.log.conjugate]
  rfl
lemma signal (ht : ShellAccess S G X.x W X.width C) (u : Directions G f) : Y.signal (wheels (S:=S) s b X.V u) = wheels (S:=S) s b X.V (X.signal u) := by
  unfold Coat.signal; rw [map_add,h.saving ht,h.toParked.pans]
end Tuned
end YM.PhysicalNext.Repeat.Turn
