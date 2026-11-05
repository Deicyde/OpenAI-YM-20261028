import YM.MultipleContact.Center.Gather
import YM.MultipleContact.Multi.Endpoint
/-! Same witnesses, adding mixed estimates about actual collapsing centers, including centroids. Comparable internal clusters in fixed-clearance arrangements. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact
open Extraction Spec Two Table Bunching
open Filter Set Function
open scoped Topology BigOperators Classical ContDiff
theorem centeredSummit (G:Gauge)(hG:G.Simple){b:ℝ} (hb:0<b)(f:Order) :
    ∃(C:Family G)(g:Order)(T:Table C.book)(Z:Final C (f.refine g) T)(Q:Splitting Z.sector.derivatives)(D:∀k,Detector T k),
      C.Makes ∧ C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ Extraction.Wcmain C ∧ Q.Covariant Z.sector.turns Z.room.kernel.spin ∧ TwoPrescriptions Z.sector.derivatives Q D ∧ ComparableProducts T ∧ (∀ m:ℕ, Joins.Store T m) ∧ (∀m:ℕ,Centered.Good m T):=by
      obtain ⟨C,g,T,Z,Q,D,M,H,K,hW,hQ,hD,h,hJ⟩:=joinedSummit G hG hb f
      exact ⟨C,g,T,Z,Q,D,M,H,K,hW,hQ,hD,h,hJ,Centered.ascend Z.room.kernel Z.phase.transport.derivatives Z.phase.transport.injection Q hJ⟩
end YM.MultipleContact
