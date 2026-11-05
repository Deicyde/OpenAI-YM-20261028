import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Center
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorLie
import YM.Extra.MULTISOURCE_BOUNDS.Columns
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymStencils
import YM.Push.LOCAL_SPLITTING.Marginal
import YM.Push.LOCAL_SPLITTING.Padding
import YM.Push.RELAY_DIFFERENCE.Stencils
import YM.Push.STRESS_FLUX.Ward
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques


/-!
# Rotate exact sector rows and ALSO their ordered-jet extensions

One family of addressed rows (use only with the same patches/Teller/etc);
does not buy the trajectory hypotheses for . V extensions here
are transformed AS FUNCTIONS, not claiming their orthogonal arguments are
independent of V. No hard-crossing derivative. Compare the new code for
curb that makes this possible on the real implementation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymRows
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Pressure.Tube Stores Exterior
open Next Next.SectorChange Next.SectorChange.Rows AnalyticBridge.GaussianFieldAlignment
open Push.SectorMeasure Oriented AnalyticBridge.SectorAffine.Offset Orthogonal Tensor Matrix
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

section translates
open Channels Locations
variable (s : Signed) (b : Site c) (V : Config G c) (k : S.Choices) (T : Tube G S) (x : ℝ)

lemma sendsF (r : ℕ) (i : Twin f) : zip (T.Φ r (translate b V)) (T.Xn r (translate b V)) i = zip (T.Φ r V) (T.Xn r V) (twin (S.ratio.embed b) i) := by
  unfold Xn Φ zip; simp_rw [translated_plot,translated_leap]
  exact Equiv.sum_comp (twin b) (fun j => T.Φ r V (twin (S.ratio.embed b) i) j (T.Xn r V j))
lemma sendsI (r : ℕ) (i : Bond c) : zip (T.Φ' r (translate b V)) (T.Xn r (translate b V)) i = zip (T.Φ' r V) (T.Xn r V) (Channels.shift b _ i) := by
  unfold Xn Φ' kick zip; simp_rw [translated_plot,translated_lane]
  exact Equiv.sum_comp (twin b) (fun j => T.Φ' r V (Channels.shift b _ i) j (T.Xn r V j))

lemma fixed_sends (h : S.patch.Branches S.kernel G) (i : Slots S) : fixedBase T x (pull s b V) (Channels.ticket s b k) i =
    unchanged G S i (fixedBase T x V k (Channels.perChannel s b S i)) := by
  obtain ⟨q,i|i⟩ := i
  · change fixedF T _ _ _ i=fixedF T _ _ (s*q) _; rw [fixedF,facade_zero,channel_turn,Xf,translated_plot,sendsF]; rfl
  change fixedI T _ _ _ _ i=fixedI T _ _ _ (s*q) _; rw [fixedI,zNoise,prediction_zero s b q V k h,channel_turn,translated_Z,sendsI]; rfl

end translates

section gauges
open Gauges
variable (z : Site c → G.El) (V : Config G c) (k : S.Choices) (T : Tube G S) (x : ℝ)

lemma rolledF (r : ℕ) (i : Twin f) : zip (T.Φ r (Lattice.gauge z V)) (T.Xn r (Lattice.gauge z V)) i = G.adjoint (z (S.ratio.parent i.1.1)) (zip (T.Φ r V) (T.Xn r V) i) := by
  unfold Xn zip; rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [plotted_turn]; exact leap_turn ..
lemma rolledI (r : ℕ) (i : Bond c) : zip (T.Φ' r (Lattice.gauge z V)) (T.Xn r (Lattice.gauge z V)) i = G.adjoint (z i.1) (zip (T.Φ' r V) (T.Xn r V) i) := by
  unfold Xn zip; rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [plotted_turn]; exact lane_turn ..

lemma fixed_rolled (h : S.patch.Branches S.kernel G) (i : Slots S) : fixedBase T x (Lattice.gauge z V) k i =
    outRotation z i (fixedBase T x V k i) := by
  obtain ⟨q,i|i⟩ := i
  · change fixedF T _ _ _ i=_; rw [fixedF,facade_null,Xf,Work.F05.pull_gauge_zero,rolledF, plotted_turn]; exact (map_sub (G.adjoint _) _ _).symm
  change fixedI T _ _ _ _ i=_; rw [fixedI,zNoise,Work.F05.pull_gauge_zero,pred_null z V q k h]
  change Z _ _ (Lattice.gauge (turned z q) _) i - zip _ _ i=_; rw [Z_turn,rolledI]; exact (map_sub (G.adjoint _) _ _).symm
end gauges

variable (x : ℝ) (A A' : Stores S) (F F' : Forest S.ratio)

/-- Address assignments ('`' points TO old`), with window including
all endpoints. For full scalar use the work (Bond f) labels below also
on the identity completion. -/
structure Box where
  edges : Equiv.Perm (Bond f)
  onKey : Active A' x F' ≃ Active A x F
  onHold : Frozen A' x F' ≃ Frozen A x F
  onAll : F'.Free ≃ F.Free
  slots : Equiv.Perm (Slots S)
  atK (i : Active A' x F') : (onKey i).val.val=edges i.val.val
  atH (i : Frozen A' x F') : (onHold i).val.val=edges i.val.val
  atAll (i : F'.Free) : (onAll i).val=edges i.val
  pane (i j : Bond f) : meeting S x (edges i) (edges j) ↔ meeting S x i j
  begun (i : Slots S) : keep x (shots S x) A' F' i ↔ keep x (shots S x) A F (slots i)

section default
open Channels Locations
variable (s : Signed) (b : Site c)
def calendar : Box x A (book s b A) F (Locations.forest s b F) :=
  ⟨diagram s b S,Locations.active s b A F x,frozen s b A F x, free s b F,perChannel s b S,fun _=>rfl,fun _=>rfl,
  fun _=>rfl, moves_meeting x s b, SymStencil.standing A F x s b⟩

def room : Box x A A F F :=
  ⟨Equiv.refl _,Equiv.refl _,Equiv.refl _,Equiv.refl _,Equiv.refl _,fun _=>rfl,fun _=>rfl,fun _=>rfl,fun _ _=>Iff.rfl,fun _=>Iff.rfl⟩
end default

variable {A A' F F' x} (L : Box x A A' F F') (O : ColorOrtho G (Bond f)) (U : ColorOrtho G (Slots S))
    (V V' : Config G c) (k k' : S.Choices) (T : Tube G S) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F))
    (Y' : LinkArray G (Frozen A' x F'))

abbrev funds := Orthogonal.move (onBond O) L.onKey
abbrev offer := warp (onBond O) L.onKey


structure Test : Prop where
  kernel : Equivalent T V V' k k' L.onKey (onBond O)
  wave (a : Directions G f) (i : Slots S) : bump T x V' k' (lifting O L.edges a) i = U i (bump T x V k a (L.slots i))
  permanent (i : Slots S) : base T x V' k' i = U i (base T x V k (L.slots i))
  frame (i : Slots S) : fixedBase T x V' k' i = U i (fixedBase T x V k (L.slots i))
  y (i : Frozen A' x F') : autoShell q d V' Y' i = O i.val.val (autoShell q d V Y (L.onHold i))

section chooses
open Channels Locations Gauges
variable (s : Signed) (b : Site c) (z : Site c → G.El) (h : S.patch.Branches S.kernel G)
  {v C E : ℝ} (hT : T.up.Bounds T.high v C E)
include h hT
lemma turn_test : Test (calendar x A F s b) (fiber s b V S) (unchanged G S) V (pull s b V) k (Channels.ticket s b k) T
     q d Y (rollY s b x A F Y) :=
    ⟨turned_cov s b V k T x h A F hT,rotated_bump s b V k T x h,rotated_base s b V k T x h,
      fixed_sends s b V k T x h,rollY_shell s b V x A F Y q d⟩
lemma gauge_test : Test (room x A F) (rotating (constantGauge z S.ratio)) (outRotation z) V (Lattice.gauge z V) k k T q d Y (gaugeY z x A F Y) :=
    ⟨gauge_cov T z V k x A F h hT,gauge_bump T z V k x h,gauge_base T z V k x h,fixed_rolled z V k T x h,shell_turn z V x A F Y q d⟩
end chooses

namespace Test
variable {O U V V' k k' T L q d Y Y'} (h : Test L O U V V' k k' T q d Y Y')





include h
variable {v C E : ℝ}










-- All old and turned channel charges.
def payment {g : Gauge} (z : LogArray g (Slots S)) (A : Stores S) (x : ℝ) (F : Forest S.ratio) (i : Slots S) :=
    if keep x (shots S x) A F i then ‖z i‖^2/2 else 0


omit h in
lemma charged (a : Prices G (Active A x F)) (i : Slots S) : payment (lands T x V k (shots S x) A F q d Y a) A x F i=
    i.2.elim (chargedUp T x V k (shots S x) A F q d Y a i.1) (chargedSide T x V k (shots S x) A F q d Y a i.1) := by
  obtain ⟨s,i|i⟩ := i <;> rfl

variable (hT : T.up.Bounds T.high v C E)
include hT










omit h hT in
lemma single_pair {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (O : ColorOrtho G α)
    (e : α ≃ β) (a b : Prices G β) (i : α) : ∑ j, Orthogonal.move O e a (i,j)*Orthogonal.move O e b (i,j)=∑ j, a (e i,j)*b (e i,j) := by
  change dotProduct (tape (Orthogonal.move O e a) i).ofLp (tape (Orthogonal.move O e b) i).ofLp=dotProduct (tape a (e i)).ofLp (tape b (e i)).ofLp
  rw [FreeResolvent.color_dot,FreeResolvent.color_dot,move_tape,move_tape,(O i).inner_map_map]



end Test
end YM.PhysicalNext.OrderedAffine2B.SymRows
