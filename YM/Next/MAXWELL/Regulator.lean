import YM.Next.MAXWELL.Current
import YM.Next.MAXWELL.Source


/-!
# Stress test regulator: source at a and observation off the source

With true colors, and Bochner integration conventions in `Current` and
`Source`. Avoid extending the **products** of fields onto the diagonal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j : ℕ}

section curl
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def exteriorD (p : Axis → E4 → F) : Field F := fun a b => grad a (p b) - grad b (p a)

lemma grad_sum_f {s : Finset Axis} (f : Axis → E4 → F) {x : E4} (H : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (k : Axis) :
    grad k (fun x => ∑ i ∈ s, f i x) x = ∑ i ∈ s, grad k (f i) x := by
  unfold grad D
  rw [fderiv_fun_sum H, sum_apply]

lemma grad_dif {f g : E4 → F} {x} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Axis) :
    grad k (f-g) x = grad k f x - grad k g x := by unfold grad D; rw [fderiv_sub hf hg]; rfl

lemma exterior_closed {A : Axis → E4 → F} {U : Set E4} (H : ∀ i x, x ∈ U → ContDiffAt ℝ ∞ (A i) x) :
    Bianchi U (exteriorD A) := by
  refine ⟨fun a b x hx => (grad_smooth a (m := ∞) (H _ _ hx) (by simp)).sub
    (grad_smooth _ (H _ _ hx) (by simp)),fun a b x _ => by simp [exteriorD],?_⟩
  intro a b c x hx
  have hd (a b : Axis) : DifferentiableAt ℝ (grad a (A b)) x :=
    (grad_smooth a (m := ∞) (H _ _ hx) (by simp)).differentiableAt (by simp)
  have ht (i a b : Axis) : grad a (grad b (A i)) x = grad b (grad a (A i)) x := grad_comm
    ((H i x hx).of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) _ _
  unfold exteriorD
  rw [grad_dif (hd b c) (hd c b), grad_dif (hd c a) (hd a c), grad_dif (hd a b) (hd b a),
    ht c a b,ht b a c,ht a b c]
  abel

/-- Lie_v f = d i_v f here. -/
def tangent (v : Drive) (f : Field F) (a : Axis) (x : E4) := ∑ b : Axis, v b x • f b a x

def variation (v : Drive) (f : Field F) := exteriorD (tangent v f)

lemma tangent_diff (v : Drive) (f : Field F) {x} (a : Axis) (H : Killing v)
    (h : ∀ i l, ContDiffAt ℝ ∞ (f i l) x) : ContDiffAt ℝ ∞ (tangent v f a) x :=
  ContDiffAt.sum fun i _ => (H.diff _).contDiffAt.smul (h i a)

lemma variation_closed (v : Drive) (f : Field F) {U : Set E4} (H : Killing v) (h : Bianchi U f) :
    Bianchi U (variation v f) := exterior_closed fun a x hx => tangent_diff _ _ a H fun i l => h.smooth i l x hx

end curl

section regulator

def opposite (q : E4 → ℝ) (i l : Axis) (b : Axis) :=
  (if i=b then grad l q else 0) - (if l=b then grad i q else 0)

def cure (t : ℝ) (i l : Axis) : Field ℝ := exteriorD (opposite (soften t) i l)

lemma cure_0 (i l : Axis) : cure 0 i l = fun a b => bareCurl a b i l := by rw [cure,soften_zero]; rfl

lemma opp_grad_formula {t : ℝ} (b i l : Axis) {x : E4} (ht : ContDiffAt ℝ ∞ (soften t) x) (a : Axis) :
    grad a (opposite (soften t) i l b) x = kr i b * grad a (grad l (soften t)) x -
      kr l b * grad a (grad i (soften t)) x := by
  have h (i k : Axis) : DifferentiableAt ℝ (if i=b then grad k (soften t) else 0) x := by
    split_ifs
    · exact (grad_smooth k (m := ∞) ht (by simp)).differentiableAt (by simp)
    exact differentiableAt_const _
  rw [opposite, grad_dif (h i l) (h l i),kr_eq,kr_eq]
  split_ifs <;> simp [grad,D]

lemma cure_continuous (i l a b : Axis) {z : ℝ × E4} (h : z.2 ≠ 0) :
    ContinuousAt (fun w : ℝ × E4 => cure w.1 i l a b w.2) z := by
  let L (a c : Axis) (w : ℝ × E4) := grad a (opposite (soften w.1) i l c) w.2
  have hl (a c : Axis) : ContinuousAt (L a c) z := by
    let H (a j : Axis) (w : ℝ × E4) := -2 * normal * basis a j * (w.1^2+‖w.2‖^2)⁻¹^2 +
      8 * normal * w.2 a * w.2 j * (w.1^2+‖w.2‖^2)⁻¹^3
    have hw (a j : Axis) : ContinuousAt (H a j) z := by
      have ht : ContinuousAt (fun w : ℝ × E4 => (w.1^2+‖w.2‖^2)⁻¹) z := by
        have hv := norm_pos_iff.mpr h
        apply ContinuousAt.inv₀
        · fun_prop
        positivity
      unfold H; fun_prop
    refine (((hw a l).const_mul (kr i c)).sub ((hw a i).const_mul (kr l c))).congr ?_
    filter_upwards [continuousAt_snd.eventually_ne h] with w hw
    have hs : 0 < ‖w.2‖ := norm_pos_iff.mpr hw
    have he : w.1^2+‖w.2‖^2 ≠ 0 := by positivity
    have hc : ContDiffAt ℝ ∞ (soften w.1) w.2 := contDiffAt_const.mul
      ((contDiffAt_const.add (contDiff_norm_sq ℝ).contDiffAt).inv he)
    change kr i c * H a l w - kr l c * H a i w = _
    dsimp only [L]; rw [opp_grad_formula _ _ _ hc a,soften_second he,soften_second he]
  exact (hl a b).sub (hl b a)

lemma cure_law {t : ℝ} (ht : 0 < t) (i l : Axis) : Bianchi univ (cure t i l) := by
  apply exterior_closed
  intro a x _; unfold opposite; apply ContDiffAt.sub <;> split_ifs
  all_goals first
  | exact contDiffAt_const
  | exact grad_smooth _ ((soften_diff ht).contDiffAt.of_le (m := ∞) le_top) (by simp)

lemma cure_charge {t : ℝ} (ht : 0 < t) (i l : Axis) (b : Axis) (x : E4) :
    divF (cure t i l) b x = kr l b * grad i (source t) x - kr i b * grad l (source t) x := by
  let f := soften t
  let A := opposite (soften t) i l
  have H (x : E4) : ContDiffAt ℝ ω f x := (soften_diff ht).contDiffAt
  have hs (a x) : ContDiffAt ℝ ω (A a) x := by
    unfold A opposite
    apply ContDiffAt.sub <;> split_ifs
    all_goals first
    | exact contDiffAt_const
    | exact grad_smooth _ (H _) le_top
  have hw (y : E4) : (∑ a : Axis, grad a (A a) y) = 0 := by
    simp_rw [A, opp_grad_formula _ _ _ ((soften_diff ht).contDiffAt.of_le (m := ∞) le_top),
      Finset.sum_sub_distrib, kr_eq,ite_mul]
    simp [grad_comm ((soften_diff ht).contDiffAt.of_le (x:=y) le_top) i l]
  have hu : (∑ a : Axis, grad a (grad b (A a)) x) = 0 := by
    simp_rw [show ∀ a, grad a (grad b (A a)) x = grad b (grad a (A a)) x from fun a => grad_comm ((hs _ _).of_le le_top) a b]
    rw [← grad_sum_f (fun i => grad i (A i)) (fun i _ => (grad_smooth _ (hs _ _) (m:=ω) le_top).differentiableAt (by simp)),
      funext hw]; simp [grad,D]
  have hk (a b) := (grad_smooth a (hs b x) (m := ω) le_top).differentiableAt (by simp)
  have he (a) : grad a (cure t i l a b) x = grad a (grad a (A b)) x - grad a (grad b (A a)) x :=
    grad_dif (hk a b) (hk b a) _
  simp_rw [divF,he,Finset.sum_sub_distrib,hu,sub_zero]
  change lap (A b) x = _
  have hp : A b = (kr i b • grad l (soften t)) + ((-kr l b) • grad i (soften t)) := by
    unfold A opposite; simp only [kr_eq]
    split_ifs <;> simp [sub_eq_add_neg]
  have hD (i) : grad i (lap (soften t)) x = - grad i (source t) x := by rw [minus_lap ht,grad,D,fderiv_neg]; rfl
  have hc (a) (z : ℝ) : lap (z • grad a (soften t)) x = z * (-grad a (source t) x) := by
    have h := lap_linear (z • ContinuousLinearMap.id ℝ ℝ) (grad_smooth a (m := ω) (H x) le_top)
    change lap (z • grad a (soften t)) x = z * lap (D (basis a) (soften t)) x at h
    rw [h,lap_D];
    · rw [show D (basis a) (lap (soften t)) x = _ from hD a]
    exact H x
  rw [hp,lap_add (show ContDiffAt ℝ ω (kr i b • grad l (soften t)) x from (grad_smooth l (m := ω) (H x) le_top).const_smul (kr i b))
    (show ContDiffAt ℝ ω ((-kr l b) • grad i (soften t)) x from
      (grad_smooth i (m := ω) (H x) le_top).const_smul (-kr l b)), hc,hc]; ring

def regulated (t : ℝ) (x : E4) (i l : Axis) (c : G.ColorIndex) : Field G.Color :=
  fun a b y => cure t i l a b (y-x) • unitColor G c

lemma reg_pulse {x y : E4} (hx : x ≠ y) (i l : Axis) (c : G.ColorIndex) (a b : Axis) :
    pulse (omegaLeg c i l) x a b y = regulated 0 x i l c a b y := by
  ext1 d
  rw [← K_observe _ _ _ _ hx,K_symmetric _ _ hx,omega_K_eq _ _ _ _ _ _ hx.symm]
  unfold regulated; rw [cure_0]; simp [unitPaint,mul_ite]

lemma reg_cont (x : E4) (i l : Axis) (c : G.ColorIndex) (a b : Axis) {z : ℝ × E4} (hz : x ≠ z.2) :
    ContinuousAt (fun w : ℝ × E4 => regulated w.1 x i l c a b w.2) z := by
  have hw : ContinuousAt (fun w : ℝ × E4 => (w.1,w.2-x)) z := by fun_prop
  exact ((cure_continuous i l a b (z := (z.1,z.2-x)) (sub_ne_zero.mpr hz.symm)).comp (x := z) (f := fun w : ℝ × E4 => (w.1,w.2-x)) hw).smul continuousAt_const

lemma shift_gradient {f : E4 → ℝ} {x y : E4} {a : Axis} (h : ContDiffAt ℝ ∞ f (y-x)) :
    grad a (fun y => f (y-x)) y = grad a f (y-x) := by
  change fderiv ℝ (f ∘ ((·-x) : E4 → E4)) y _ = _
  have ht : HasFDerivAt ((·-x) : E4 → E4) (ContinuousLinearMap.id ℝ E4) y :=
    (hasFDerivAt_id y).sub_const _
  rw [fderiv_comp y (h.differentiableAt (by simp)) ht.differentiableAt, ht.fderiv]; rfl

lemma reg_grad {t : ℝ} (ht : 0 < t) (x y : E4) (i l : Axis) (c : G.ColorIndex) (a b k : Axis) :
    grad a (regulated t x i l c b k) y = grad a (cure t i l b k) (y-x) • unitColor G c := by
  have hs : ContDiffAt ℝ ∞ (cure t i l b k) (y-x) := (cure_law ht i l).smooth b k _ (mem_univ _)
  let L := tint (G:=G) (unitColor G c)
  change grad a (L ∘ (fun y => cure t i l b k (y-x))) y = L _
  rw [grad_linear L (show ContDiffAt ℝ ∞ (fun y => cure t i l b k (y-x)) y from
    hs.comp y (f := fun y => y-x) (contDiffAt_id.sub contDiffAt_const)), shift_gradient hs]
  rfl

lemma regulated_closed {t : ℝ} (ht : 0 < t) (x : E4) (i l : Axis) (c : G.ColorIndex) (U : Set E4) :
    Bianchi U (regulated t x i l c) := by
  have H := cure_law ht i l
  refine ⟨fun a b y _ => ?_, fun a b y _ => ?_,fun a b k y _ => ?_⟩
  · exact ((H.smooth a b (y-x) (mem_univ _)).comp y (f := fun y => y-x) (contDiffAt_id.sub contDiffAt_const)).smul contDiffAt_const
  · unfold regulated; rw [H.skew a b (y-x) (mem_univ _),neg_smul]
  simp_rw [reg_grad ht, ← add_smul,H.cycle _ _ _ _ (mem_univ _),zero_smul]

lemma regulated_charge {t : ℝ} (ht : 0 < t) (x y : E4) (i l : Axis) (c : G.ColorIndex) (b : Axis) :
    divF (regulated t x i l c) b y =
      (kr l b * grad i (source t) (y-x) - kr i b * grad l (source t) (y-x)) • unitColor G c := by
  unfold divF; simp_rw [reg_grad ht x]; rw [← Finset.sum_smul]
  rw [← cure_charge ht]; rfl

end regulator

end YM.Maxwell.Free
