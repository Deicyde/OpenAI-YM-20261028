import YM.Push.LOOP_COEFFICIENT.LoopRow
import YM.Push.LOOP_COEFFICIENT.Paths.Angles
import YM.Push.LOOP_COEFFICIENT.Paths.Windows


/-!
# Cover strings for signed transport at two link angles
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Matrix Set Metric Lattice RG Wilson Laurent Bloch Complex Work.F02
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {r : ℕ}

abbrev Surface (G : Gauge) := Shifts (Angles G)

def letterAt (d : Step) (x : Cover) (v : Surface G) := letterAngle d.neg d.dir (v (d.used x).1)

def run (v : Surface G) (x : Cover) (w : Walk) : G.Mat := match w with
  | [] => 1
  | d::w => letterAt d x v * run v (x+d.vec) w





variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → Surface G}
lemma letterAt_diff (h : ∀ i, ContDiff ℂ ω fun z => g z i) (d : Step) (x : Cover) : ContDiff ℂ ω fun z => letterAt d x (g z) := (letter_diff ..).comp (h _)
lemma run_diff (h : ∀ i,ContDiff ℂ ω fun z => g z i) (x : Cover) (w : Walk) : ContDiff ℂ ω fun z => run (g z) x w := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ih => exact (letterAt_diff h d x).mul (ih _)
@[simp] lemma run_zero (x : Cover) (w : Walk) : run (0:Surface G) x w = 1 := by induction w generalizing x <;> simp_all [run,letterAt]
lemma run_congr {x : Cover} {w : Walk} {g h : Surface G} (e : size x + w.length ≤ r) (hgh : ∀ i∈Window r,g i = h i) : run g x w = run h x w := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih =>
    have he := size_add x (d.vec : Cover); rw [size_vec] at he; rw [List.length_cons] at e
    have hh : (d.used x).1 ∈ Window r := by
      rw [Step.used]; split
      next ht => rw [Step.vec,if_pos ht] at he; rw [sub_eq_add_neg]; change size (x + -(step d.dir)) ≤ r; omega
      next => exact (Nat.le_add_right ..).trans e
    rw [run,run,ih (show _ ≤ r by omega),letterAt,letterAt,hgh _ hh]

lemma run_bound {R : ℝ} (hR : 0≤R) (v : Surface G) (h : ∀ b i x, ‖letterAngle b i (v x)-1‖ ≤ R) (x : Cover) (w : Walk) : ‖run v x w‖ ≤ (1+R)^w.length * ‖(1:G.Mat)‖ := by
  induction w generalizing x with
  | nil => simp [run]
  | cons d w ih =>
    let X := letterAt d x v
    let T := run v (x+d.vec) w
    calc
      _ = ‖T + (X-1)*T‖ := by rw [sub_mul,one_mul,add_sub_cancel,run]
      _ ≤ ‖T‖ + R*‖T‖ := (norm_add_le ..).trans (add_le_add (le_refl _) ((norm_mul_le ..).trans (by gcongr; exact h ..)))
      _ = (1+R)*‖T‖ := by ring
      _ ≤ (1+R) * ((1+R)^w.length * ‖(1:G.Mat)‖) := by gcongr; apply ih
      _ = _ := by simp [pow_succ']; ring

def unwrap (z : Co n (Angles G) → ℝ) (x : Site n) : Surface G := fun i => cvec fun j => z (wrap n i+x,j)
lemma run_merged (z : Co n (Angles G) → ℝ) (b : Site n) (x : Cover) (w : Walk) : run (unwrap z b) x w = G.mat (travel (expandAt b (merged z)) x w) := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => rw [run,travel,G.mat_mul,ih]; unfold letterAt Step.read; rcases d with ⟨i,_|_⟩
                   · rw [show letterAngle false i (unwrap z b _) = _ from merged_read z _ i]; rfl
                   · rw [show letterAngle true i (unwrap z b _) = _ from merged_inv z _ i]; rfl

def turned (s : Signed) (w : Walk) := w.map (·.rotate s)

lemma turned_reverse (s : Signed) (w : Walk) : turned s (Lattice.reverse w) = Lattice.reverse (turned s w) := by simp [turned,Lattice.reverse,List.map_reverse,Function.comp_def,Step.rev_rotate]
lemma turned_pull (s : Signed) (z : Co n (Angles G) → ℝ) (x : Site n) (w : Walk) : run (unwrap z (s.act x)) 0 (turned s w) = G.mat (travel (pull s 0 (merged z)) x w) := by rw [run_merged,travel_at,travel_pull]; simp [affine,turned]

lemma slotWalk_length (a : Slot) : (slotWalk a).length ≤ 2*a.length := by simp only [slotWalk,Lattice.reverse,List.length_append,List.length_map,List.length_reverse]; change a.walk.length + 4 + a.walk.length ≤ 2*(a.walk.length+4); omega
lemma slotWalk_closed {R : Type*} [AddCommGroup R] [One R] (a : Slot) (x : Four R) : stop x (slotWalk a) = x := by rw [slotWalk,stop_append,stop_append,square_stop,reverse_stop]

def swung (a : Slot) (s : Signed) := turned s (slotWalk a)
lemma swung_length (a : Slot) (s : Signed) : (swung a s).length ≤ 2*a.length := by simpa [swung,turned] using slotWalk_length a


def fieldSlot (a : Slot) (s : Signed) (z : Surface G) := colorProject G ((1/2:ℂ) • (run z 0 (swung a s) - run z 0 (Lattice.reverse (swung a s))))
lemma fieldSlot_diff (h : ∀ i,ContDiff ℂ ω fun z => g z i) (a : Slot) (s : Signed) : ContDiff ℂ ω (fun z => fieldSlot a s (g z)) := (colorProject G).contDiff.comp (((run_diff h ..).sub (run_diff h ..)).const_smul (1/2:ℂ))
lemma fieldSlot_congr {a : Slot} (s : Signed) {g h : Surface G} (e : 2*a.length ≤ r) (hgh : ∀ i∈Window r,g i = h i) : fieldSlot a s g = fieldSlot a s h := by
  have he := (swung_length a s).trans e
  unfold fieldSlot; rw [run_congr (w:=swung a s) (by simpa [size]) hgh,run_congr (w:=Lattice.reverse _) (by simpa [size,Lattice.reverse]) hgh]
lemma fieldSlot_merged (a : Slot) (s : Signed) (z : Co n (Angles G) → ℝ) (x : Site n) : fieldSlot a s (unwrap z (s.act x)) = colorUp G (a.atSite (pull s 0 (merged z)) x) := by
  rw [fieldSlot,swung, ← turned_reverse,turned_pull,turned_pull]
  rw [show travel (pull s 0 (merged z)) x (Lattice.reverse (slotWalk a)) = _ from slotWalk_closed a x ▸ travel_reverse (slotWalk a) _ x,colorProject_skew,atSite_curvature]
  · unfold Gauge.curvature; rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num]; rfl
  · simp only [star_smul,G.mat_inv,star_sub,star_star,Complex.star_def,map_div₀,map_one,map_ofNat,← smul_neg,neg_sub]
def chargeOp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) := ‖f‖
lemma chargeOp_nonneg {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : 0≤chargeOp f := norm_nonneg f
lemma fieldSlot_bound {σ : ℝ} (hσ : 0<σ) (v : Surface G) (h : ∀ b i x, ‖letterAngle b i (v x)-1‖ ≤ radius σ) (s : Signed) (a : Slot) : ‖fieldSlot a s v‖ ≤ slotConst G * Real.exp (σ*a.length) := by
  have he w (hw : List.length w ≤ 2*a.length) : ‖run v 0 w‖ ≤ Real.exp (σ*a.length) * ‖(1:G.Mat)‖ := by
    apply (run_bound (radius_pos hσ).le v h ..).trans; rw [radius,add_sub_cancel,← Real.exp_nat_mul]; have : (w.length:ℝ)≤2*a.length := by exact_mod_cast hw
    gcongr Real.exp ?_ * _
    nlinarith
  have hw := swung_length a s
  have hz := norm_sub_le (run v 0 (swung a s)) (run v 0 (Lattice.reverse (swung a s))) |>.trans (add_le_add (he _ hw) (he _ (by simpa [Lattice.reverse])))
  refine ((colorProject G).le_opNorm _).trans ?_; rw [norm_smul,norm_div,norm_one,Complex.norm_two]
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (by norm_num : 0 ≤ (1:ℝ)/2)) (chargeOp_nonneg (E:=G.Mat) (colorProject G)); apply this.trans_eq
  change chargeOp (E:=G.Mat) (colorProject G)*_= (chargeOp (E:=G.Mat) (colorProject G)*_) * _; ring
end YM.Push.Loops.Paths
