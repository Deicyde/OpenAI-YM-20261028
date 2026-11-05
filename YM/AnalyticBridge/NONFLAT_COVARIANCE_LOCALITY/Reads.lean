import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Channel
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Chart
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Kick
import YM.Push.FREE_RESOLVENT.ListJets
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils


/-!
# Numerical dependencies of D entries/columns

These are at actual tags and actual lengths. Localize V and tag reads and
prove zero outside range if test direction is single-link. Geometry (A, F)
dependence paid separately. Stated in terms of values of *positive*
representatives, parents and initial sites; when using to allocate physical
support, always keep both endpoints, including in charts.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Function Lattice RG Pressure Precision Wilson Tree 
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.SectorMeasure.Oriented
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {R : ℕ} {s : Signed}
    {V W : Config G c} {q : Site c} {z v : Coord G c}



lemma replica_agrees (h : AgreeNear id q R V W) :
    AgreeNear S.ratio.parent q R (replica S.ratio V) (replica S.ratio W) := by
  intro e he
  unfold replica; split <;> first | rfl | exact h _ he

lemma facade_agrees (A : Directions G f) (h : AgreeNear id (s.act q) (R+1) V W) :
    AgreeNear S.ratio.parent q R (facade S s V A) (facade S s W A) := by
  apply pulled_near
  intro i hi; unfold increment; rw [replica_agrees h i hi]

lemma jet_reads_face (A : Directions G f) (u : Cell f)
    (h : AgreeNear id (s.act (S.ratio.parent u.1)) 5 V W) :
    plaquetteJet S V s u A = plaquetteJet S W s u A := by
  have hh (a : Directions G f) : faceValue (facade S s V a) u = faceValue (facade S s W a) u :=
    travel_near _ (Work.E03.parent_step S) _ _ _ _ 4 le_rfl (facade_agrees a h)
  unfold plaquetteJet; simp_rw [hh]

/-- Length allowance from the cover, incl plaquette in `Slot.length`. -/
lemma pulse_reads_face (A : Directions G f) (i : Site f) (u : Slot)
    (h : AgreeNear id (s.act (S.ratio.parent i)) (u.length+1) V W) :
    pulsePath S V s i A u=pulsePath S W s i A u := by
  have ht : travel (facade S s V 0) i u.walk=travel (facade S s W 0) i u.walk :=
    travel_near _ (Work.E03.parent_step S) _ _ _ _ u.length (Nat.le_add_right ..) (facade_agrees _ h)
  rw [pulsePath, pulsePath, ht, jet_reads_face (W:=W) A]
  refine h.shrink ?_
  rw [separation_signed]; have hh := slot_distance (S:=S) u i
  unfold Slot.length; omega

-- Include the same left and RIGHT tag in the actual prediction point.
lemma same_tags (S : StepData c f) (i : Bond c) (k k' : S.Choices)
    (hl : k.1 i.1=k'.1 i.1) (hr : k.1 (i.1+step i.2)=k'.1 (i.1+step i.2))
    (ht : k.2 i=k'.2 i) (U : Config G f) :
    S.prediction U k i=S.prediction U k' i := by
  have he : S.connector U k.1 i = S.connector U k'.1 i := by
    unfold StepData.connector StepData.frames; rw [hl,hr]
  rw [StepData.prediction,StepData.prediction,he,ht]

lemma jet_reads_prediction (hp : S.patch.Branches S.kernel G) (i : Bond c) (s : Signed)
    (k k' : S.Choices) (hl : k.1 (sendEdge s 0 i).1=k'.1 (sendEdge s 0 i).1)
    (hr : k.1 ((sendEdge s 0 i).1+step (sendEdge s 0 i).2)=
      k'.1 ((sendEdge s 0 i).1+step (sendEdge s 0 i).2))
    (ht : k.2 (sendEdge s 0 i)=k'.2 (sendEdge s 0 i))
    (A : Directions G f)
    (h : AgreeNear id (s.act i.1) (predReach S.patch+1) V W) :
    blockJet V k s i A=blockJet W k' s i A := by
  let b := sendEdge s 0 i
  have hx : AgreeNear S.ratio.parent b.1 (predReach S.patch) (replica S.ratio V) (replica S.ratio W) := by
    apply replica_agrees (S:=S)
    apply h.shrink; have hb : separation (s.act i.1) b.1 ≤ 1 := spin_step i s; omega
  have hy (a : Directions G f) : predictGroup V k s i a=predictGroup W k' s i a := by
    unfold predictGroup facade
    simp_rw [(carry s hp k _).2,(carry s hp k' _).2,Motion.turn_read]
    have he : AgreeNear S.ratio.parent b.1 (predReach S.patch)
        (increment (replica S.ratio V) a) (increment (replica S.ratio W) a) := by
      intro e he; unfold increment; rw [hx e he]
    rw [prediction_near_eq hp _ _ k (sendEdge s 0 i) he,same_tags S _ _ _ hl hr ht]
  unfold blockJet predictorTurn; simp_rw [hy]

def SingleAt (a : Directions G f) (e : Bond f) := ∀ j : Bond f, j≠e → a j=0
variable {a : Directions G f} {e : Bond f} (h : SingleAt a e)
include h






end YM.AnalyticBridge.NonflatCovarianceLocality
