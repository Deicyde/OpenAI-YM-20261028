import YM.Push.LOOP_COEFFICIENT.Block.Vessel
import YM.Push.LOOP_COEFFICIENT.Block.Yard


/-!
# Assembly of the joint-level determinant port
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block.Vessel
open Function Matrix Set Filter Lattice Laurent Bloch RG Wilson Complex Portal Fine Exterior Precision
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {L c f : Side} {G : Gauge} {η A B g σ C e M K : ℝ} {Y : Lights G L} {P : Pier G L} {W : PathData G} {p : Clip} {V : Vessel G L}
structure Canopy (V : Vessel G L) (η K : ℝ) : Prop where
  back : Yard V.back η K
  kick : Grows V.kick η
  kick' : Quanta V.kick (Tube η) (Tube η) 1 K
  horizontal q : q∈Tube η → V.kick.base q = 0
  signal : Grows V.signal η
  signal' : Quanta V.signal (Tube η) (Tube η) 1 K


structure Cruise (V : Vessel G L) (Y : Lights G L) (W : PathData G) (p : Clip) (η C : ℝ) : Prop where
  port : Yard (V.port.fabric Y W p) η C
  ref : Yard (station Y W p) η C
  joint : Yard (V.onboard Y W p) η C
  steers : Yard (V.sail Y W p) η C
  drifts : ∃ e M,ChargeStrip (V.drift Y W p) e M



variable (W p)
def loopData (V : Vessel G L) (T : Towers L) : LoopData G L := let Y := axisProfile G T.A0; let μ := (L.val:ℝ)⁻¹
    ⟨T.A0,V.onboard Y W p,V.port.fabric Y W p,station Y W p,V.drift Y W p,complete W p μ,gauged G μ⟩
variable {W p}
open scoped Matrix.Norms.Frobenius in
lemma Cruise.uses (hη : 0<η) {r : Ratio c f} {S : StepData c f} {T : Towers r.count} {V : Vessel G r.count} {D Λ} (h : Cruise V (axisProfile G T.A0) W p η A)
    (hR : T.A0.safe) (hW : W.Bounds p σ D Λ) (hs : S.patch.Branches S.kernel G) (ht : ∀ t : S.Choices,V.Charts t (installed r T.A0)) : (loopData W p V T).Uses (g:=r) S p W := by
  have he := A0_projects (G:=G) (g:=r) T.A0 hR
  refine ⟨fun t => ((ht t).onboard he hW hs).sync,fun t => let ⟨χ,hχ,_⟩ := (ht t).turns; ⟨χ,hχ.hχ,(hχ.adjusted W p he hW).sync⟩,?_,fun t => (ht t).drift he hW hs (fun _ _ hq => h.steers.unit _ (Work.F07.realStrip _ hη hq.bar)),?_,?_⟩
  all_goals dsimp only [loopData,LoopData.lift]; rw [ratio_mu S r]
  · exact (station_models he hW).sync
  · exact (complete_models hW (inv_pos.mpr (side_pos r.count)) f).sync
  · exact (ghost_models G (r.count.val:ℝ)⁻¹ f).sync


end YM.Push.Loops.Block.Vessel
