import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import YM.Next.MAXWELL.Affine



/-!
# Enclosing with boxes

Adapters for d^3y face measure: here unscaled coordinates orthonormal
with the Axis basis, choose the remaining axes by Fin.succAbove. In
particular bottom face of a positive-time enclosure has outward normal
*negative* time direction. No current needs to extend to the enclosed
insert.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free.Box
open Set Function Filter Tensor Analysis MeasureTheory WithLp
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {G : Gauge} {j l : ℕ}

abbrev Plain := Axis → ℝ
abbrev Section3 := SpaceAxis → ℝ

def enclosedBy (p q : Plain) : Set E4 := ofLp ⁻¹' Icc p q

def strictly (p q : Plain) : Set E4 := ofLp ⁻¹' pi univ (fun i => Ioo (p i) (q i))

lemma strict_coord {p q : Plain} {x : E4} (H : x ∈ strictly p q) (a : Axis) :
    p a < x a ∧ x a < q a := (show ofLp x ∈ pi univ _ from H) a (mem_univ _)

lemma admitted (p q : Plain) : strictly p q ⊆ enclosedBy p q := fun _ H =>
  ⟨fun a => (strict_coord H a).1.le,fun a => (strict_coord H a).2.le⟩

lemma open_box (p q : Plain) : IsOpen (strictly p q) := by
  have H : Continuous (ofLp : E4 → Plain) := by fun_prop
  exact (isOpen_set_pi finite_univ fun i _ => isOpen_Ioo).preimage H

lemma testBox {p q : Plain} {x : E4} (hx : x ∈ strictly p q) :
    ∃ χ : E4 → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[𝓝 x] (fun _ => 1) ∧ tsupport χ ⊆ strictly p q := by
  obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ((open_box p q).mem_nhds hx)
  let B : ContDiffBump x := ⟨r/2,r,by positivity,by linarith⟩
  exact ⟨B,B.contDiff,B.hasCompactSupport,B.eventuallyEq_one,by rw [B.tsupport_eq]; exact h⟩

def face (p q : Plain) (a : Axis) : Set Section3 := Icc (p ∘ a.succAbove) (q ∘ a.succAbove)

def inFace (a : Axis) (t : ℝ) (x : Section3) : E4 := toLp 2 (a.insertNth t x)

lemma inFace_cont (a : Axis) (t : ℝ) : Continuous (inFace a t) := by
  unfold inFace; exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)).symm.continuous.comp
    (show Continuous (fun x : Section3 => a.insertNth (α := fun _ => ℝ) t x) from continuous_const.finInsertNth a continuous_id)

@[simp] lemma inFace_at (a t x) : inFace a t x a = t := by simp [inFace]



def side (p q : Plain) (J : Axis → E4 → ℝ) (a : Axis) (t : ℝ) :=
  ∫ x : Section3 in face p q a, J a (inFace a t x)

def perimeter (p q : Plain) (J : Axis → E4 → ℝ) := ∑ a : Axis, (side p q J a (q a) - side p q J a (p a))

lemma box_divergence {p q : Plain} (hp : p ≤ q) (J : Axis → E4 → ℝ)
    (h : ∀ a y, y ∈ enclosedBy p q → ContDiffAt ℝ ∞ (J a) y) :
    (∫ x : Plain in Icc p q, ∑ a : Axis, grad a (J a) (toLp 2 x)) = perimeter p q J := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)).symm.toContinuousLinearMap
  let f (a) := J a ∘ L
  have ht (a : Axis) (x : Plain) (hx : x ∈ Icc p q) : ContDiffAt ℝ ∞ (f a) x :=
    (h a (toLp 2 x) hx).comp x L.contDiff.contDiffAt
  have hd (x) (hx : x ∈ Icc p q) : (∑ a : Axis, fderiv ℝ (f a) x (Pi.single a 1)) =
      ∑ a : Axis, grad a (J a) (toLp 2 x) := by
    apply Finset.sum_congr rfl; intro i _
    change fderiv ℝ (J i ∘ L) x _ = _
    rw [fderiv_comp x (show DifferentiableAt ℝ (J i) (L x) from (h i (toLp 2 x) hx).differentiableAt (by simp))
      L.differentiableAt, L.fderiv]; rfl
  have hc : ContinuousOn (fun x => ∑ a : Axis, fderiv ℝ (f a) x (Pi.single a 1)) (Icc p q) := by
    intro x hx; apply ContinuousAt.continuousWithinAt
    refine ContDiffAt.continuousAt (n := ∞) (𝕜:=ℝ) ?_
    exact ContDiffAt.sum fun i _ => dSmooth (ht i x hx) _ (by simp)
  have he := integral_divergence_of_hasFDerivAt_off_countable' p q hp f (fun i => fderiv ℝ (f i))
    ∅ countable_empty (fun i x hx => (ht i x hx).continuousAt.continuousWithinAt)
    (fun x hx i => ((ht i x (admitted p q (a := toLp 2 x) hx.1)).differentiableAt (by simp)).hasFDerivAt)
    (hc.integrableOn_compact isCompact_Icc (μ:=volume))
  exact (setIntegral_congr_fun measurableSet_Icc hd).symm.trans he

/-- Stokes with same flux despite central insert. J defined everywhere but
only used off x in the calculation; perimeter computes outward flux. -/
lemma box_flux {p q : Plain} (h : p ≤ q) {x : E4} (χ : E4 → ℝ) (Hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hw : χ =ᶠ[𝓝 x] fun _ => 1) (ht : tsupport χ ⊆ strictly p q) (J : Axis → E4 → ℝ)
    (hs : ∀ a y, y ∈ enclosedBy p q → y ≠ x → ContDiffAt ℝ ∞ (J a) y)
    (hd : ∀ y, y ∈ enclosedBy p q → y ≠ x → ∑ a : Axis, grad a (J a) y = 0) :
    exportFlux J χ = perimeter p q J := by
  let F (a : Axis) (y : E4) := (1-χ y)*J a y
  have hx (a) : F a =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hw] with y hy; simp only [F, hy,sub_self,zero_mul]
  have hf (a y) (hy : y ∈ enclosedBy p q) : ContDiffAt ℝ ∞ (F a) y := by
    by_cases he : y=x
    · exact he.symm ▸ (contDiffAt_const.congr_of_eventuallyEq (hx a))
    exact (contDiffAt_const.sub Hχ.contDiffAt).mul (hs a y hy he)
  have heq : perimeter p q F = perimeter p q J := by
    have he (a : Axis) (t : ℝ) (ha : t=p a ∨ t=q a) : side p q F a t = side p q J a t := by
      have hv (y : Section3) : inFace a t y ∉ tsupport χ := by
        intro hy; have hk := strict_coord (ht hy) a; rw [inFace_at] at hk; rcases ha with h | h <;> simp_all
      simp only [side,F,image_eq_zero_of_notMem_tsupport (hv _),sub_zero,one_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [he _ _ (Or.inr rfl),he _ _ (Or.inl rfl)]
  let W (a : Axis) (y : E4) := -(grad a χ y • J a y)
  have hh (z : E4) (hz : z ∈ enclosedBy p q) : ∑ a : Axis, W a z = ∑ a : Axis, grad a (F a) z := by
    by_cases he : z=x
    · subst z
      have hp (a : Axis) : grad a χ x = 0 := image_eq_zero_of_notMem_tsupport fun he => collar hw (gradient_part χ a he)
      have hv (a : Axis) : grad a (F a) x = 0 := (GermD (basis a) (hx a)).trans (by simp [D])
      simp [W,hp,hv]
    have hl (a : Axis) : grad a (F a) z = W a z + (1-χ z)*grad a (J a) z := by
      have hv : DifferentiableAt ℝ (fun x => 1-χ x) z := differentiableAt_const _ |>.sub (Hχ.differentiable (by simp) z)
      change fderiv ℝ (fun x => (1-χ x)*J a x) z _ = _
      rw [fderiv_fun_mul hv ((hs a z hz he).differentiableAt (by simp)),
        fderiv_fun_sub (differentiableAt_const _) (Hχ.differentiable (by simp) z)]
      rw [show fderiv ℝ (fun _ : E4 => (1:ℝ)) z = 0 from (hasFDerivAt_const (1:ℝ) z).fderiv]
      simp only [W,smul_eq_mul,D,grad,add_apply,smul_apply,zero_sub, neg_apply];
      ring
    simp_rw [hl, Finset.sum_add_distrib, ← Finset.mul_sum,hd _ hz he,mul_zero,add_zero]
  have ht' (a : Axis) : Integrable (W a) := (shell_cost Hχ hc (fun y hy =>
    (hs a y (admitted p q (ht (tsupport_fderiv_subset ℝ hy))) (fun he : y=x => collar hw (he ▸ hy))).continuousAt) a).neg
  unfold exportFlux; rw [← Finset.sum_neg_distrib]; simp_rw [← integral_neg]
  change (∑ a : Axis, ∫ x, W a x) = perimeter p q J
  rw [← integral_finsetSum _ (fun a _ => ht' a), ← heq,← box_divergence h F hf]
  let f (x : E4) := ∑ a, W a x
  have hp : MeasurePreserving (toLp 2 : Plain → E4) := PiLp.volume_preserving_toLp ..
  have hv : (∫ y : E4, f y) = ∫ y : Plain, f (toLp 2 y) := (hp.integral_comp
    (PiLp.continuousLinearEquiv 2 ℝ _ |>.symm.toHomeomorph.measurableEmbedding) f).symm
  rw [show (fun x => ∑ a : Axis, W a x) = f from rfl,hv]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact setIntegral_congr_fun measurableSet_Icc fun x hx => hh (toLp 2 x) hx
  · intro x hx
    have he (a : Axis) : grad a χ (toLp 2 x) = 0 := image_eq_zero_of_notMem_tsupport
      fun he => hx (admitted p q (ht (tsupport_fderiv_subset ℝ (gradient_part χ a he))))
    simp [f,W,he]

lemma energy_through {a : Axis} {p q : Plain} (h : p ≤ q) {x y : E4}
    (hx : x ∈ strictly p q) (hy : y ∉ enclosedBy p q) (P : Probe G j) (Q : Probe G l) :
    perimeter p q (fun i z => cross (pulse P x) (pulse Q y) i a z) =
      - K (raiseLeg (basis a) P) Q x y := by
  obtain ⟨χ,hχ,Hχ,hw,he⟩ := testBox hx
  have hxy : x ≠ y := by rintro rfl; exact hy (admitted p q hx)
  have hP := pulse_wave P x
  have hQ := pulse_wave Q y
  let J := current (drift a) (pulse P x) (pulse Q y)
  have hf : perimeter p q J = singleFlux (drift a) χ (pulse P x) (pulse Q y) := by
    refine (box_flux h χ hχ Hχ hw he J (fun a z hz h => current_diff (drift_K _) _
      (fun i l => hP.smooth i l z h) fun i l => hQ.smooth i l z (fun ht : z=y => hy (ht ▸ hz))) ?_).symm
    intro z hz hne
    let U : Set E4 := {x}ᶜ ∩ {y}ᶜ
    have H : z ∈ U := ⟨hne,fun hw : z=y => hy (hw ▸ hz)⟩
    unfold J
    rw [current_div (wave_closed (wave_mono inter_subset_left hP))
      (wave_closed (wave_mono inter_subset_right hQ)) (isOpen_compl_singleton.inter isOpen_compl_singleton) (drift_K a) H]
    simp only [divF,hP.divergence _ _ H.1,hQ.divergence _ _ H.2,inner_zero_right, inner_zero_left]
    simp
  have hs : tsupport χ ⊆ {y}ᶜ := fun z hz heq => hy ((show z=y from heq) ▸ admitted p q (he hz))
  have he : J = (fun i z => cross (pulse P x) (pulse Q y) i a z) := by funext i z; simp [J,current,drift,kr_eq,ite_mul]
  rw [← he]
  simpa [K_symmetric _ Q hxy,K_sample _ _ hxy.symm] using
    hf.trans (drift_flux isOpen_compl_singleton hQ P a hχ Hχ hs hw)

end YM.Maxwell.Free.Box
