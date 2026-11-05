import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymWhole

/-! # Reindex the actual scalar determinant and exponent-chain labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Bower.Spin
open Function Filter Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree Push Push.SectorMeasure Oriented
open Precision Finset MeasureTheory Matrix ConnectedActivityE6 ConnectedActivityE6.Shell ConnectedActivityE6.Channel ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Census ConnectedActivityE6.Coat 
open ConnectedActivityE6.Poll  AbsoluteSums AnalyticBridge.GaussianFieldAlignment
open Locations Channels Tensor Orthogonal
open Next.Fluctuations Work.F03 ConnectedActivityE6.Pulse Itinerary Window
open OrderedAffine2B.SymWhole (weave_times weave_trans weave_one weave_scale weave_add weave_sub)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {Y X : Coat T F}
variable (s : Signed) (b : Site c) (X : Coat T F) {γ W x : ℝ}

def tracks (e : Equiv.Perm (Bond f)) (n : ℕ) : Equiv.Perm (Itinerary f n) :=
  match n with
  | 0 => Equiv.refl _
  | n+1 => (chart f n).trans ((e.prodCongr (tracks e n)).trans (chart f n).symm)














variable (hp : S.patch.Branches S.kernel G) {p d Q y} (hT : T.up.Bounds p d Q y)
include hp hT



omit hp hT in
lemma a_cont {P : Teller G} {L : Side} {w A B C : ℝ} (h : Rotator P L w A B C X) (i : ℕ) : ContinuousOn (fun v=> aSeq X.shutter X.plate v i) (Set.uIcc 0 1) := by
  match i with
  | 0=> exact continuousOn_const
  | 1=> exact vibrate X.shutter X.plate h.scale h.full
  | j+2 => exact ContinuousOn.neg (ContinuousOn.sub ((strung X.plate).continuousOn.mul (vibrate X.shutter X.plate h.scale h.full)) continuousOn_const)




end YM.PhysicalNext.Bower.Spin
