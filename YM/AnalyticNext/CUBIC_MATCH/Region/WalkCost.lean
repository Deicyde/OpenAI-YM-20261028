import YM.AnalyticNext.CUBIC_MATCH.Region.GermCost
import YM.AnalyticNext.CUBIC_MATCH.Region.Scale


set_option warningAsError false

/-!
# Costs of the native walks in an oriented channel

Spend at most path length per factor, including windings through L-cell
seams. On the plaquette, `gain` not the naive bound gives the extra L power
(down to μ² for the first term, as for the two-link term).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {μ : Type*} {n L : Side}
  {c f : μ → Side} {η θ C : ℝ}
  {V : ∀ p, Dir G (c p) → Dir G (f p)} {r : ShiftRoot c f}

/-- Each represented-FINE link cost. Uniformly in L and inputs. -/
def tileFee (G : Gauge) (C : ℝ) := (G.colorScale + ‖sec (fun u => G.mat (G.lieExp u)) 0‖+1)*C
lemma tileFee_nonneg (h : 0 ≤ C) : 0 ≤ tileFee G C := by
  unfold tileFee; have hx := G.colorScale_pos; positivity

def visitRead (V : ∀ p, Dir G (c p) → Dir G (f p)) (r : ShiftRoot c f) (i : Cover) (w : Walk) : GermRead G c G.El := fun p x a u =>
    travel (represent (u • V p a)) (wrap (f p) i+r p x) w
abbrev walkMat (V : ∀ p, Dir G (c p) → Dir G (f p)) (r : ShiftRoot c f) (i : Cover) (w : Walk) : GermRead G c G.Mat :=
   fun p x a t => G.mat (visitRead V r i w p x a t)

def hopSign (d : Step) (y : Site n) (a : Dir G n) := if d.neg then -collect G a (d.used y) else collect G a (d.used y)
lemma hop_read (d : Step) (a : Dir G n) (y : Site n) (t : ℝ) :
    d.read (represent (t • a)) y=G.lieExp (t • hopSign d y a) := by
  unfold hopSign Step.read; simp only [Work.F03.represent_link,Pi.smul_apply]; split <;> rename_i h
  · rw [smul_neg,Work.F03.exp_neg_color]; rfl
  rfl

namespace ScaleRead

lemma hop (h : ScaleRead c f L r V θ C) (d : Step) (u : Cover) (b : ℕ) (hp : size u+1≤b) : LocalRep c 1 θ
    (C*tilt L*phaseCost L θ b) (fun p x a => hopSign d (wrap (f p) u+r p x) (V p a)) := by
  rcases d with ⟨i,s|s⟩
  · exact (h.link u (coord i)).raisePrice (mul_le_mul_of_nonneg_left (phase_mono h.rate.le (by omega)) (mul_nonneg h.fee tilt_pos.le))
  have he := h.link (u - step i) (coord i)
  refine (he.negative.raisePrice ?_).fits fun p x a => ?_
  · have hh : size (u-step i) ≤ size u+1 := by simpa only [sub_eq_add_neg,size_reverse_step] using size_add u (-step i)
    exact mul_le_mul_of_nonneg_left (phase_mono h.rate.le (hh.trans hp)) (mul_nonneg h.fee tilt_pos.le)
  have hx : wrap (f p) (u-step i)+r p x=wrap (f p) u+r p x-step i := by rw [map_sub,wrap_step]; abel
  change -(V ..)=-(V p a (wrap _ _+r p x-step i,_)); rw [hx]; rfl

/-- Bound transported factors individually -- no secondary moment assumption. -/
lemma perLink (h : ScaleRead c f L r V θ C) (d : Step) (u : Cover) (b : ℕ) (hp : size u+1≤b) :
    let D := tileFee G C*tilt L*phaseCost L θ b
    RayReceipt c θ D (D^2) (fun p x a t => G.mat (d.read (represent (t • V p a)) (wrap (f p) u+r p x))) := by
  intro D
  let P := phaseCost L θ b
  have hh := h.hop d u b hp
  have hg := G.colorScale_pos
  let E := ‖sec (fun u => G.mat (G.lieExp u)) 0‖
  have hE : 0 ≤ E := norm_nonneg (sec _ (0:G.Color) (F:=G.Mat))
  have h₁ : G.colorScale*(C*tilt L*P) ≤ D := calc
    _ ≤ (G.colorScale + E+1)*(C*tilt L*P) := mul_le_mul_of_nonneg_right (by linarith) hh.cash
    _ = _ := by unfold D tileFee E P; ring
  have he : E ≤ (G.colorScale+E+1)^2 := by nlinarith
  have h₂ : E*(C*tilt L*P)*(C*tilt L*P) ≤ D^2 := calc
    _ = E*(C*tilt L*P)^2 := by ring
    _ ≤ (G.colorScale+E+1)^2*(C*tilt L*P)^2 := mul_le_mul_of_nonneg_right he (sq_nonneg _)
    _ = _ := by unfold D tileFee E P; ring
  simp_rw [hop_read]; exact (receiptExp hh).raisePrice h₁ h₂

lemma along (h : ScaleRead c f L r V θ C) (u : Cover) (w : Walk) (b : ℕ) (hp : size u+w.length ≤ b) :
    let D := (w.length:ℝ)*(tileFee G C*tilt L*phaseCost L θ b)
    RayReceipt c θ D (D^2) (walkMat V r u w) := by
  let Y := tileFee G C*tilt L*phaseCost L θ b
  induction w generalizing u with
  | nil =>
    simp only [List.length_nil,Nat.cast_zero,zero_mul, ne_eq, OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
    refine ⟨fun _ _ _ => contDiffAt_const, fun _ _ _ => rfl, ?_,?_⟩
    · exact (LocalRep.none (E:=G.Mat) h.rate).fits (fun _ _ _ => Eq.symm (positive_nil (g:=(1:G.Mat)) (k:=1) (by omega)))
    exact (LocalRep.none (E:=G.Mat) h.rate).fits (fun _ _ _ => Eq.symm (positive_nil (g:=(1:G.Mat)) (k:=2) (by omega)))
  | cons d w ih =>
    have hu : size (u+d.vec) ≤ size u+1 := by simpa only [size_native] using size_add u (d.vec:Cover)
    rw [List.length_cons] at hp
    let n := w.length
    have hf := h.perLink d u b (by omega)
    have hm : RayReceipt c θ Y (Y^2) (fun p x a t => G.mat (d.read (represent (t • V p a)) (wrap (f p) u+r p x))) := hf
    have ht := hm.mul (ih (u+d.vec) (by omega))
    simp only [walkMat,visitRead,map_add,wrap_vec,add_right_comm (wrap _ u)] at ht
    unfold walkMat visitRead; simp only [travel,G.mat_mul]
    refine ht.raisePrice ?_ ?_
    · change Y + n * Y ≤ ((w.length+1:ℕ):ℝ)*Y; unfold n; push_cast; linarith
    change Y^2+Y*(n*Y)+(n*Y)^2 ≤ (((n+1:ℕ):ℝ)*Y)^2; push_cast
    nlinarith [sq_nonneg Y,mul_nonneg (show 0 ≤ (n:ℝ) by positivity) (sq_nonneg Y)]



end ScaleRead

def faceFirst (G : Gauge) (C : ℝ) := G.colorScale*(2*C)


def faceSecond (G : Gauge) (C θ : ℝ) := (4*tileFee G C*Real.exp (θ*4))^2





end YM.CubicMatch
