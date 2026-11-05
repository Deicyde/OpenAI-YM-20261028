import YM.Pert.Position.Crest
import YM.Pert.Rigid.Camera
/-! Motor-corrected exact frames per horizon via leading equations. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Position
open Filter Function Set Topology Classical Maxwell RawLabels Rigid Climb Spec Org Labels Submodule
open scoped ContDiff
variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book}
variable (F : Labels.Frames G) {d : ℕ}
lemma motor_unit {d : ℕ} {F : Frames G} (b : Buffer F d) : motor F b ((freeTable F).unit d)=(freeTable F).unit d := by simp only [motor,_root_.add_apply,b.property.1,add_zero]; rfl
lemma motor_filter {j d : ℕ} {F : Frames G} (b : Buffer F d) (j0 : j<d) {v : E F d} (h : v ∈ lower F j d) : motor F b v ∈ lower F j d := by
  change v+b.val v∈lower F j d; exact Submodule.add_mem _ h (b.property.2.1 j j0 _ h)
lemma motor_bar {d : ℕ} {F : Frames G} (b : Buffer F d) (v : E F d) :
    (freeTable F).conj (Extra.FD.table_spin F) d (motor F b v)=motor F b ((freeTable F).conj (Extra.FD.table_spin F) d v) := by unfold motor; simp only [_root_.add_apply,map_add,b.property.2.2.1]; rfl
lemma motor_spin {d : ℕ} {F : Frames G} (b : Buffer F d) (s : Signed) (v : E F d) : Extra.FD.rideO F s.ortho d (motor F b v) = motor F b (Extra.FD.rideO F s.ortho d v) := by unfold motor; simp only [_root_.add_apply,map_add,b.property.2.2.2.1]; rfl
lemma motor_mulI {d : ℕ} {F : Frames G} (b : Buffer F d) (v : E F d) : motor F b (Complex.I • v) = Complex.I • motor F b v := by unfold motor; simp only [_root_.add_apply,b.property.2.2.2.2,smul_add]; rfl

def cmotor (B : Buffer F d) : Module.End ℂ (E F d) where
  toFun p := motor F B p
  map_add' _ _ := map_add _ _ _
  map_smul' c x := by change c • x + B.val (c • x) = c • (x + B.val x); rw [dispatch_cmul, smul_add]
lemma cmotor_at (B : Buffer F d) (v) : cmotor F B v = motor F B v := rfl
lemma cmotor_zero : cmotor F (0 : Buffer F d)=LinearMap.id := LinearMap.ext (fun v=> add_zero v)

private def finalized (B : Buffer F d) (h : IsUnit (motor F B)) : E F d ≃ₗ[ℂ] E F d := LinearEquiv.ofBijective (cmotor F B) (ContinuousLinearMap.isUnit_iff_bijective.mp h)
def adjusted (X : Scaling S) (B : ℕ→Buffer C.labels d) (k : ℕ) : YM.Spin.change S d :=
    if h : IsUnit (motor C.labels (B k)) then (finalized C.labels (B k) h).trans (X.U k d) else X.U k d

-- symmetry data relative to any RealSpin proof on each side (irrelevant proof).
private lemma commutes (F : Labels.Frames G) (H : (freeTable F).RealSpin) (B : Buffer F d) (s : Signed) (p : E F d) :
    (freeTable F).mirror H d s (motor F B p) = motor F B ((freeTable F).mirror H d s p) := by
  have he : H = Rigid.idol F := rfl
  subst H
  change wear F d s _ = motor F B (wear F d s p); simp_rw [wear_ride F]
  exact motor_spin _ _ _
lemma adjusted_own {p : Final C I S} {X : Scaling S} (h : FirstExtension p X) {B : ℕ→Buffer C.labels d} (k : ℕ) (hk : YM.Spin.realH p.room.kernel.spin (Free.spin_free _) (X.U k d)) : YM.Spin.realH p.room.kernel.spin (Free.spin_free _) (adjusted X B k) := by
  unfold adjusted
  split_ifs; swap; exact hk
  change (∀ s v, X.U _ _ (motor C.labels (B k) ((freeTable C.labels).mirror _ _ s v)) = _) ∧ (∀ v, X.U _ _ (motor C.labels (B k) ((freeTable C.labels).conj (Free.spin_free _) d v)) = _)
  constructor
  · intro s v; rw [←commutes]; exact hk.1 ..
  intro v; change X.U k d (motor C.labels (B k) ((freeTable C.labels).conj (Extra.FD.table_spin C.labels) d v))=_
  rw [←motor_bar]; exact hk.2 ..
lemma adjusted_unit (X : Scaling S) (B : ℕ→ Buffer C.labels d) (k : ℕ) : adjusted X B k ((freeTable C.labels).unit d)= X.U k d ((freeTable C.labels).unit d) := by
  unfold adjusted;split_ifs;swap;exact rfl
  change X.U k d (motor _ (B k) _)=_;rw [motor_unit]
lemma adjusted_at {X : Scaling S} {B : ℕ→ Buffer C.labels d} (hB : Tendsto B atTop (𝓝 0)) : ∀ᶠ k in atTop, adjusted X B k=fun v=> X.U k d (motor C.labels (B k) v) := by -- coerces eq?
  filter_upwards [hB.eventually (invertible_tail C.labels d)] with k hk
  unfold adjusted;rw [dif_pos hk];rfl

def toFour {d : ℕ} (hd : d≤4) := (Free.scheme F).rise hd
lemma motor_small (hG : G.Simple) (hd : d<4) (B : Buffer F 4) (v : E F d) : motor F B (toFour F hd.le v)=toFour F hd.le v := by
  obtain ⟨a,rfl⟩ := UVNext.FreeStress.below F hG hd v
  have hunit := (Free.scheme F).fixs (Free.scheme_filters F) (Maxwell.table_regular F) hd.le
  unfold toFour
  rw [map_smul,hunit]
  change cmotor F B _ = _
  rw [map_smul,cmotor_at,motor_unit]
end YM.Pert.Position
