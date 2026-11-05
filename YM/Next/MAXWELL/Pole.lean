import YM.Next.MAXWELL.Kernel

/-!
# Harmonic multipoles of the leg kernel (on real Euclidean space)

Denominator orders that keep track of angular weight. We'll use these
rather than uniqueness/divisibility claims about values on a complex
cone. Also needed at varying widths and for analyticity and growth of the
free table. Identities here are on separated positions/Euclidean germs,
not about contact distributions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open scoped ContDiff Topology BigOperators RealInnerProductSpace

variable {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {G : Gauge} {j k l r : ℕ}

def rad (s : ℕ) (x : E4) := (‖x‖^2)^s

def lap (f : E4 → F) (x : E4) := ∑ i : Axis, grad i (grad i f) x

theorem rad_diff (s : ℕ) : ContDiff ℝ ω (rad s) := (contDiff_norm_sq ℝ).pow _

@[simp] theorem lap_zero : lap (0 : E4 → F) = 0 := by
  have he (v : Axis) : grad v (0 : E4 → F) = 0 := by ext1 x; simp [grad,D]
  simp [lap, he, funext_iff]

theorem lap_local {f g : E4 → F} {x} (h : f =ᶠ[𝓝 x] g) : lap f x = lap g x := by
  refine Finset.sum_congr rfl fun i _ => GermD _ ?_
  filter_upwards [h.eventuallyEq_nhds] with y hy
  exact GermD _ hy

theorem lap_add {f g : E4 → F} {x : E4} (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) :
    lap (f+g) x = lap f x + lap g x := by
  have he : (∀ i : Axis, grad i (f+g) =ᶠ[𝓝 x] grad i f + grad i g) := fun i => by
    have hv (y : E4) (h : DifferentiableAt ℝ f y) (w : DifferentiableAt ℝ g y) :
        grad i (f+g) y = (grad i f+grad i g) y := by
      unfold grad D; rw [fderiv_add h w]; rfl
    filter_upwards [hf.eventually (by simp),hg.eventually (by simp)] with y hy hy';
    exact hv y (hy.differentiableAt (by simp)) (hy'.differentiableAt (by simp))
  unfold lap; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change D _ _ _ = _
  rw [GermD (basis i) (he i), D, fderiv_add (((grad_smooth i hf (m := ω) le_top)).differentiableAt (by simp))
    (((grad_smooth i hg (m := ω) le_top)).differentiableAt (by simp))]; rfl

theorem lap_linear (L : F →L[ℝ] M) {f : E4 → F} {x : E4} (hf : ContDiffAt ℝ ω f x) : lap (L ∘ f) x = L (lap f x) := by
  unfold lap; rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => (GermD (basis i) (f := grad i (L ∘ f)) (g := L ∘ grad i f) ?_).trans
    (grad_linear L (grad_smooth i hf le_top) _)
  filter_upwards [hf.eventually (by simp)] with y hy
  exact grad_linear L (hy.of_le le_top) _

theorem lap_smooth {f : E4 → F} {x} (hf : ContDiffAt ℝ ω f x) : ContDiffAt ℝ ω (lap f) x :=
  ContDiffAt.sum fun i _ => grad_smooth i (grad_smooth i hf (m := ω) le_top) le_top

theorem lap_D {f : E4 → F} {x : E4} (hf : ContDiffAt ℝ ω f x) (u : E4) : lap (D u f) x = D u (lap f) x := by
  have he (i : Axis) : grad i (D u f) =ᶠ[𝓝 x] D u (grad i f) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact commuteD (hy.of_le le_top) _ _
  rw [lap, show lap f = fun y => ∑ i : Axis, grad i (grad i f) y from rfl,D, fderiv_fun_sum]
  · rw [sum_apply]
    refine Finset.sum_congr rfl fun i _ => (GermD (basis i) (he i)).trans
      (commuteD ((grad_smooth i hf (m := ω) le_top).of_le le_top) (basis i) u)
  exact fun i _ => (grad_smooth i (grad_smooth i hf (m := ω) le_top) (m := ω) le_top).differentiableAt (by simp)

def Clears (s : ℕ) (f : E4 → F) := ∃ g : E4 → F, ContDiff ℝ ω g ∧
  ∀ x ∈ away, rad s x • f x = g x

/-- A harmonic homogeneous pole whose Kelvin numerator extends (all
calculations here in real space). We use r≥2 for the kernel. -/
structure Pole (r : ℕ) (f : E4 → F) : Prop where
  diff : ∀ x ∈ away, ContDiffAt ℝ ω f x
  degree (t : ℝ) (ht : 0 < t) x : x ∈ away → f (t • x) = (t⁻¹^r) • f x
  precise : Clears (r-1) f
  Laplace : EqOn (lap f) 0 away

namespace Pole
variable {f g : E4 → F}

protected theorem congr (H : Pole r f) (h : EqOn f g away) : Pole r g where
  diff x hx := (H.diff x hx).congr_of_eventuallyEq (h.symm.eventuallyEq_of_mem (open_away.mem_nhds hx))
  degree t ht x hx := by
    rw [← h hx, ← H.degree t ht x hx]; exact (h (smul_ne_zero ht.ne' hx)).symm
  precise := by
    obtain ⟨G,hG,hw⟩ := H.precise
    exact ⟨G,hG,fun x hx => by rw [← h hx]; exact hw x hx⟩
  Laplace := fun x hx => (lap_local (h.symm.eventuallyEq_of_mem (open_away.mem_nhds hx))).trans (H.Laplace hx)

theorem coord (H : Pole r f) (L : F →L[ℝ] M) : Pole r (L ∘ f) where
  diff x hx := L.contDiff.contDiffAt.comp x (H.diff x hx)
  degree t ht x hx := by rw [Function.comp_apply,H.degree _ ht x hx,map_smul]; rfl
  precise := by
    obtain ⟨G,hG,hw⟩ := H.precise
    refine ⟨L ∘ G,L.contDiff.comp hG,fun x hx => ?_⟩
    change _ • L (f x) = L (G x); rw [← map_smul, hw x hx]
  Laplace x hx := by rw [lap_linear L (H.diff x hx), H.Laplace hx]; exact map_zero L

protected theorem scale (H : Pole r f) (t : ℝ) : Pole r (t • f) := H.coord (t • ContinuousLinearMap.id ℝ F)

protected theorem add (H : Pole r f) (K : Pole r g) : Pole r (f+g) where
  diff x hx := (H.diff x hx).add (K.diff x hx)
  degree t ht x hx := by simp only [Pi.add_apply,H.degree _ ht x hx,K.degree _ ht x hx,smul_add]
  precise := by
    obtain ⟨G,hG,hw⟩ := H.precise
    obtain ⟨L,hL,hr⟩ := K.precise
    refine ⟨G+L,hG.add hL,fun x hx => ?_⟩
    simp only [Pi.add_apply,smul_add,hw x hx,hr x hx]
  Laplace x hx := by rw [lap_add (H.diff x hx) (K.diff x hx),H.Laplace hx,K.Laplace hx]; simp

protected theorem sub (H : Pole r f) (K : Pole r g) : Pole r (f-g) := by
  have he := H.add (K.scale (-1)); simpa [sub_eq_add_neg] using he

protected theorem zero (r : ℕ) : Pole r (0 : E4 → F) := by
  refine ⟨fun _ _ => contDiffAt_const, fun t ht x hx => ?_, ⟨0,contDiff_const,?_⟩,fun _ _ => by rw [lap_zero]⟩ <;> simp

lemma rad_D (s : ℕ) (x u : E4) :
    rad 1 x * D u (rad s) x = (s:ℝ) * D u (rad 1) x * rad s x := by
  let R := fun x : E4 => ‖x‖^2
  have he : rad 1 = R := by simp [funext_iff,rad,R]
  rw [he]
  let L := fderiv ℝ R x
  have hs : HasFDerivAt R L x := by
    unfold L; rw [← he]; exact (rad_diff 1 |>.differentiable (by simp) x).hasFDerivAt
  rw [D, (show HasFDerivAt (rad s) _ x from hs.pow s).fderiv,D]
  simp only [smul_apply,smul_eq_mul]
  cases s with
  | zero => simp
  | succ s =>
    rw [nsmul_eq_mul, Nat.add_sub_cancel]
    change R x * ((↑(s+1 : ℕ) : ℝ) * (R x) ^ s * L u) = _ * L u * (R x) ^ (s+1)
    rw [pow_succ]; ring

protected theorem step (H : Pole r f) (hr : 2 ≤ r) (u : E4) : Pole (r+1) (D u f) where
  diff x hx := dSmooth (H.diff x hx) _ le_top
  degree t ht x hx := by
    have htx : t • x ∈ away := smul_ne_zero ht.ne' hx
    let L : E4 →L[ℝ] E4 := t • ContinuousLinearMap.id ℝ E4
    have he : f ∘ L =ᶠ[𝓝 x] (t⁻¹ ^ r) • f := by
      filter_upwards [open_away.mem_nhds hx] with y hy; exact H.degree _ ht y hy
    have hk := GermD u he
    rw [D,D,fderiv_const_smul ((H.diff x hx).differentiableAt (by simp)),
      fderiv_comp x (show DifferentiableAt ℝ f (L x) from (H.diff _ htx).differentiableAt (by simp))
        L.differentiableAt, L.fderiv, ContinuousLinearMap.comp_apply] at hk
    change fderiv ℝ f (t • x) (t • u) = t⁻¹ ^ r • D u f x at hk
    apply smul_right_injective F ht.ne'
    unfold D
    change t • (fderiv ℝ f (t • x)) u = _; rw [← map_smul (fderiv ℝ f (t • x)), hk]; change _ = t • (t⁻¹^(r+1)) • D u f x
    rw [smul_smul, pow_succ', ← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  precise := by
    obtain ⟨g,hg,h⟩ := H.precise
    let s := r-1
    have hr' : r=s+1 := by dsimp [s]; omega
    have hw : (r+1)-1=s+1 := by omega
    rw [hw]
    refine ⟨fun x => rad 1 x • D u g x - ((s:ℝ)* D u (rad 1) x) • g x, contDiff_iff_contDiffAt.mpr
      (fun x => ((rad_diff 1).contDiffAt.smul (dSmooth hg.contDiffAt u (m := ω) le_top)).sub
        ((contDiffAt_const.mul (dSmooth (rad_diff 1).contDiffAt u (m := ω) le_top)).smul hg.contDiffAt)), ?_⟩
    intro x hx
    have he : g =ᶠ[𝓝 x] (rad s • f) := by
      filter_upwards [open_away.mem_nhds hx] with y hy
      exact (h y hy).symm
    have hs := GermD u he
    change D u g x = fderiv ℝ (rad s • f) x u at hs
    rw [fderiv_smul ((rad_diff s).differentiable (by simp) x)
      ((H.diff x hx).differentiableAt (by simp))] at hs
    change D u g x = rad s x • D u f x + D u (rad s) x • f x at hs
    dsimp only
    rw [hs,smul_add,← h x hx]
    simp only [smul_smul,rad_D s x u]
    rw [show r-1 = s from rfl, add_sub_cancel_right]
    congr 1; simp [rad,pow_succ']
  Laplace x hx := by
    have he : lap f =ᶠ[𝓝 x] 0 := H.Laplace.eventuallyEq_of_mem (open_away.mem_nhds hx)
    rw [lap_D (H.diff _ hx),GermD u he]; simp [D]

protected theorem taylor (H : Pole r f) (hr : 2 ≤ r) (u : Fin j → E4) :
    Pole (r+j) (fun y => Tensor.coeff f j y u) := by
  induction j generalizing r f with
  | zero => simpa [Tensor.coeff_apply_zero] using H
  | succ j ih =>
    have hs := (ih (H.step hr (u 0)) (by omega) (Fin.tail u)).scale (((↑(j+1 : ℕ) : ℝ))⁻¹)
    rw [show r+(j+1) = r+1+j by omega]
    apply hs.congr
    intro x hx
    symm
    conv_lhs => rw [← Fin.cons_self_tail u]
    exact Tensor.coeff_apply_cons ((H.diff x hx).of_le le_top) _ _

/-- Uniform *global* estimate on one multipole. -/
protected theorem bounds (H : Pole r f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ away, ‖f x‖ ≤ C * ‖x‖⁻¹ ^ r := by
  let A := Metric.sphere (0 : E4) 1
  have hc := isCompact_sphere (0 : E4) 1
  obtain ⟨C,h⟩ := hc.exists_bound_of_continuousOn (show ContinuousOn f A from fun x hx =>
    ((H.diff x (show x ∈ away from by
      have hw : ‖x‖ = 1 := by simpa [A,Metric.mem_sphere] using hx
      exact norm_pos_iff.mp (by linarith))).continuousAt).continuousWithinAt)
  refine ⟨max C 0, le_max_right ..,fun x hx => ?_⟩
  let t := ‖x‖
  have ht : 0 < t := norm_pos_iff.mpr hx
  let y := t⁻¹ • x
  have he : ‖y‖ = 1 := by rw [show y=t⁻¹ • x from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),inv_mul_cancel₀ ht.ne']
  have hy : y ∈ away := norm_pos_iff.mp (by rw [he]; norm_num)
  have hp : ‖f y‖ ≤ max C 0 := (h y (by simpa [Metric.mem_sphere,A] using he)).trans (le_max_left ..)
  conv_lhs => rw [show x=t • y from (smul_inv_smul₀ ht.ne' _).symm,H.degree t ht y hy]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_comm]
  exact mul_le_mul_of_nonneg_right hp (by positivity)

end Pole

lemma green_pole : Pole 2 Green where
  diff x hx := by
    have hs := norm_pos_iff.mpr (show x ≠ 0 from hx)
    exact contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp; positivity : ‖x‖^2 ≠ 0))
  degree t ht x hx := by
    unfold Green; rw [norm_smul,Real.norm_eq_abs, abs_of_pos ht,mul_pow,mul_inv]
    simp [smul_eq_mul]; ring
  precise := by
    refine ⟨fun _ => normal, contDiff_const,fun x hx => ?_⟩
    have hs := norm_pos_iff.mpr (show x ≠ 0 from hx)
    change rad 1 x * Green x = normal; simp only [rad,pow_one,Green]
    field_simp
  Laplace := fun x h => harmonic h

lemma bare_pole (i l a b : Axis) : Pole 4 (bareCurl i l a b) := by
  have he (i a b : Axis) : Pole 3 (if a=i then grad b Green else 0) := by
    split_ifs
    · exact green_pole.step (by omega) _
    exact Pole.zero 3
  have hs (i : Axis) : Pole 3 (curlOpp i a b) := (he i a b).sub (he i b a)
  exact ((hs l).step (by omega) _).sub ((hs i).step (by omega) _)

theorem kernel_pole (p : Probe G j) (q : Probe G l) : Pole (4+j+l) (legKernel p q) := by
  induction p using leg_probe_induction generalizing q with
  | vars u c i m =>
    induction q using leg_probe_induction with
    | vars v d a b =>
      have he (x) (hx : x ∈ away) : legKernel (leg u c i m) (leg v d a b) x = _ :=
        raw_mixed u v i m a b c d hx
      by_cases hw : c=d
      · apply ((((bare_pole i m a b).taylor (by omega) u).taylor (by omega) v).scale ((-1 : ℝ)^l)).congr
        intro x hx; rw [he x hx, if_pos hw]; rfl
      apply (Pole.zero _).congr; intro x hx; rw [he x hx, if_neg hw]; rfl
    | zero =>
      apply (Pole.zero _).congr; intro x hx; exact (map_zero (pairing hx _)).symm
    | add p q hp hq =>
      apply (hp.add hq).congr; intro x hx; exact (map_add (pairing hx _) p q).symm
    | smul t p hp =>
      apply (hp.scale t).congr; intro x hx; exact (map_smul (pairing hx _) t p).symm
  | zero =>
    apply (Pole.zero _).congr; intro x hx; exact (map_zero ((pairing hx).flip q)).symm
  | add a b ha hb =>
    apply ((ha q).add (hb q)).congr; intro x hx; exact (map_add ((pairing hx).flip q) a b).symm
  | smul t p hp =>
    apply ((hp q).scale t).congr; intro x hx; exact (map_smul ((pairing hx).flip q) t p).symm

end YM.Maxwell.Free
