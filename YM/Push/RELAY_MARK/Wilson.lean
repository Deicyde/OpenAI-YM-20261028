import YM.Next.EXTRACTION.Tails
import YM.Work.A15
import YM.Work.B04
import YM.Work.C13.Decay
import YM.Work.G07.Calculus
/-!
# Positive-link gradient and actual cutoff equations

Convention . The derivative is along `exp (t A) * U_e`
(with the other positive links held fixed) and contains **one** real
contribution per positive-axis pair. Thus a backward incidence also
uses the original configuration (adjoint transport). The partition/law
are for these conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark

open Lattice Wilson MeasureTheory Filter Function Set
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

variable {G : Gauge} {n : Side} (U : Config G n) (x : Site n) (ν : Axis)

section Gauge
attribute [local instance] Gauge.frobInner

lemma curvature_pair (A : G.Color) (g : G.El) :
    -(G.colorMat A * G.mat g).trace.re = (G.repDim : ℝ) * inner ℝ A (G.curvature g) := by
  let X := G.colorMat A
  let S := G.mat g
  have hs : (X * star S).trace.re = - (X*S).trace.re := by
    have hv : (X*S).trace.re = (star (X*S)).trace.re := by
      rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]; rfl
    rw [star_mul, show star X = -X from G.colorMat_skew _, mul_neg, Matrix.trace_neg,
      Complex.neg_re, Matrix.trace_mul_comm (star S) X] at hv
    linarith only [hv]
  let Y := (1/2:ℝ) • (G.mat g - G.mat g⁻¹)
  rw [← G.trace_color]
  change - (X*S).trace.re = - (X*G.colorMat (G.projectColor Y)).trace.re
  have hl : inner ℝ Y X = inner ℝ (G.lie.starProjection Y) X := sub_eq_zero.mp (by
    rw [← inner_sub_left]; exact Submodule.starProjection_inner_eq_zero _ _ (G.colorMat_mem A))
  rw [← G.colorMat_project] at hl
  have hh : (X * star Y).trace.re = - (X*G.colorMat (G.projectColor Y)).trace.re := by
    rw [real_inner_comm X Y, real_inner_comm X (G.colorMat _)] at hl
    change (X * star Y).trace.re = (X * star (G.colorMat (G.projectColor Y))).trace.re at hl
    rw [hl, G.colorMat_skew, mul_neg, Matrix.trace_neg, Complex.neg_re]
  rw [← hh]
  unfold Y
  simp only [G.mat_inv, star_smul, star_trivial, star_sub, star_star, mul_smul_comm, mul_sub,
    Matrix.trace_smul, Matrix.trace_sub, Complex.real_smul, Complex.ofReal_div,
    Complex.sub_re]
  unfold S at *
  push_cast at *
  simp [hs]; ring

lemma left_price_deriv (g : G.El) (A : G.Color) :
    HasDerivAt (fun t : ℝ => G.price (G.lieExp (t • A) * g)) (inner ℝ A (G.curvature g)) 0 := by
  have hh : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • A))) (G.colorMat A) 0 := by
    simp only [G.mat_lieExp,map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat A) (0 : ℝ)
  let L : G.Mat →L[ℝ] ℝ := Complex.reCLM.comp ((Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap)
  have he := L.hasFDerivAt.comp_hasDerivAt 0 (hh.mul_const (G.mat g))
  have hu := (he.div_const (G.repDim:ℝ)).const_sub (1:ℝ)
  refine hu.congr_deriv ?_
  change - ((G.colorMat A * G.mat g).trace.re / (G.repDim:ℝ)) = _
  have hd : (G.repDim:ℝ) ≠ 0 := by exact_mod_cast G.dimPos.ne'
  rw [← neg_div,curvature_pair]
  field_simp
end Gauge

section Act

def turnLink (e : Edge (Site n)) (A : G.Color) (t : ℝ) (U : Config G n) : Config G n :=
    update U e (G.lieExp (t • A) * U e)

@[simp] lemma turn_here (e : Edge (Site n)) (A : G.Color) (t : ℝ) : turnLink e A t U e = G.lieExp (t • A) * U e := update_self ..
lemma turn_away {e b : Edge (Site n)} (A : G.Color) (t : ℝ) (he : b ≠ e) : turnLink e A t U b=U b := update_of_ne he ..

@[simp] lemma turn_zero (e : Edge (Site n)) (A : G.Color) : turnLink e A 0 U = U := by
  simp [turnLink]

lemma turn_add (e : Edge (Site n)) (A : G.Color) (s t : ℝ) : turnLink e A (t+s) U =
    turnLink e A t (turnLink e A s U) := by
  funext b
  by_cases h : b=e
  · subst b
    simp only [turn_here,← mul_assoc]
    apply congr_arg (· * U e)
    apply G.mat_injective
    simp only [G.mat_mul,G.mat_lieExp,map_smul,add_smul]
    simp only [map_add, map_smul]
    haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
    exact NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat A)).smul_left t).smul_right s)
  rw [turn_away U A _ h,turn_away _ A _ h,turn_away _ A _ h]

lemma turn_preserving (e : Edge (Site n)) (A : G.Color) (t : ℝ) :
    MeasurePreserving (turnLink e A t) (prior G n) (prior G n) := by
  haveI : (prior G n).IsMulLeftInvariant := by unfold prior; infer_instance
  convert measurePreserving_mul_left (prior G n) (turnLink e A t 1) using 1
  funext U b
  by_cases h : b=e <;> simp [h,turnLink, Function.update_of_ne]

lemma skip {X : Type*} (F : Config G n → X) (b : Edge (Site n)) :
    (∀ (P Q : Config G n), (∀ d : Edge (Site n), d ≠ b → P d = Q d) → F P = F Q) →
    ∀ A : G.Color, ∀ (U : Config G n) t, F (turnLink b A t U) = F U := fun h A U t =>
  h _ _ fun _ he => turn_away U A t he
end Act

section Gradient

variable {R : Type*} [AddCommGroup R] [One R]

/-- Value on an ordered square (orientation can differ from Face). -/
def plane (V : Links R G.El) (y : Four R) (i j : Axis) := travel V y (square i j)

lemma plane_read (V : Links R G.El) (y : Four R) (i j : Axis) : plane V y i j =
    V (y,i) * V (y+step i,j) * (V (y+step j,i))⁻¹ * (V (y,j))⁻¹ := by
  unfold plane square
  simp only [travel, Step.vec_pos, Step.vec_neg, Step.pos_read, Step.neg_read, mul_one, mul_assoc]
  congr 2; abel_nf

lemma plane_swap (V : Links R G.El) (y : Four R) (i j : Axis) : plane V y j i=(plane V y i j)⁻¹ :=
    oriented_swap _ _ _ _

def stem (V : Links R G.El) (y : Four R) (b : Axis) (p : PlaqAxes) :=
    G.curvature (faceValue V (y,p)) - G.adjoint (V (y-step b,b))⁻¹ (G.curvature (faceValue V (y-step b,p)))

def flux (V : Links R G.El) (e : Edge (Four R)) (p : PlaqAxes) :=
    if p.val.1=e.2 then stem V e.1 p.val.2 p
    else if p.val.2=e.2 then -(stem V e.1 p.val.1 p) else 0

def field (V : Links R G.El) (e : Edge (Four R)) : G.Color := ∑ p : PlaqAxes, flux V e p

private lemma step_ne (h : 2 ≤ n.val) (i : Axis) : (step i : Site n) ≠ 0 := by
  letI : Fact (1 < n.val) := ⟨h⟩
  intro he
  have hl := congr_fun he i
  simp [Per] at hl

private lemma plane_head (hn : 2 ≤ n.val) (A : G.Color) (j : Axis) (hj : j ≠ ν) (t : ℝ) :
    plane (turnLink (x,ν) A t U) x ν j = G.lieExp (t • A) * plane U x ν j := by
  simp only [plane_read]
  rw [turn_here,turn_away,turn_away,turn_away]
  · simp only [mul_assoc]
  all_goals simp [hj,step_ne hn j]

private lemma plane_back (x : Four R) (i j : Axis) (V : Links R G.El) :
    travel V x (oriented (posDir i) (negDir j)) =
      (V (x-step j,j))⁻¹ * (plane V (x-step j) i j)⁻¹ * V (x-step j,j) := by
  have he := oriented_next (posDir j) (posDir i) (x-step j) V
  simp only [Step.vec_pos,sub_add_cancel, Step.rev_pos,Step.pos_read] at he
  rw [he]
  change _ * plane _ _ _ _ * _ = _
  nth_rw 1 [plane_swap V (x-step j) i j]

private lemma tail_turn (hn : 2 ≤ n.val) (A : G.Color) (j : Axis) (hj : j ≠ ν) (t : ℝ) :
    travel (turnLink (x,ν) A t U) x (oriented (posDir ν) (negDir j)) =
      G.lieExp (t • A) * travel U x (oriented (posDir ν) (negDir j)) := by
  rw [plane_back,plane_back]
  simp only [plane_read,sub_add_cancel]
  rw [turn_away U A _ (by simp [hj]),turn_away,turn_away,turn_here]
  · group
  all_goals simp [hj,step_ne hn j]

private lemma backward_price (A : G.Color) (hn : 2 ≤ n.val) (j : Axis) (hj : j ≠ ν) :
    HasDerivAt (fun t : ℝ => G.price (plane (turnLink (x,ν) A t U) (x-step j) ν j))
      (- inner ℝ A (G.adjoint (U (x-step j,j))⁻¹ (G.curvature (plane U (x-step j) ν j)))) 0 := by
  let u := travel U x (oriented (posDir ν) (negDir j))
  have hp (V : Config G n) : G.price (plane V (x-step j) ν j) = G.price (travel V x (oriented (posDir ν) (negDir j))) := by
    rw [plane_back]
    let g : G.El := (V (x-step j,j))⁻¹
    have he := G.price_conj g (plane V (x-step j) ν j)⁻¹
    simpa only [g, inv_inv,G.price_inv] using he.symm
  have ht : (fun t : ℝ => G.price (plane (turnLink (x,ν) A t U) (x-step j) ν j)) = fun t : ℝ => G.price (G.lieExp (t • A)*u) :=
    funext fun t => by rw [hp,tail_turn U x ν hn A j hj]
  rw [ht]
  refine (left_price_deriv u A).congr_deriv ?_
  unfold u; rw [plane_back]
  let v := (U (x-step j,j))⁻¹
  rw [show G.curvature _ = G.adjoint v (G.curvature (plane U (x-step j) ν j)⁻¹) from by
    simpa only [v,inv_inv] using G.curvature_conjugate v ((plane U (x-step j) ν j)⁻¹)]
  rw [G.curvature_inv,map_neg,inner_neg_right]

private lemma forward_sum (hn : 2 ≤ n.val) (A : G.Color) (j : Axis) (hj : j ≠ ν) :
    HasDerivAt (fun t : ℝ => ∑ y : Site n, G.price (plane (turnLink (x,ν) A t U) y ν j))
      (inner ℝ A (G.curvature (plane U x ν j)- G.adjoint (U (x-step j,j))⁻¹ (G.curvature (plane U (x-step j) ν j)))) 0 := by
  have hx : x-step j ≠ x := by simp [step_ne hn j]
  let Q (y : Site n) :=
    if y=x then inner ℝ A (G.curvature (plane U x ν j))
    else if y=x-step j then -inner ℝ A (G.adjoint (U (x-step j,j))⁻¹ (G.curvature (plane U (x-step j) ν j))) else 0
  have H (y : Site n) : HasDerivAt (fun t : ℝ => G.price (plane (turnLink (x,ν) A t U) y ν j)) (Q y) 0 := by
    unfold Q; split
    next h => subst y; simp_rw [plane_head U x ν hn A j hj]; exact left_price_deriv ..
    next h =>
      split
      next he => subst y; exact backward_price U x ν A hn j hj
      next he =>
        have hu : y+step j ≠ x := mt (eq_sub_of_add_eq ·) he
        have hc (t : ℝ) : plane (turnLink (x,ν) A t U) y ν j = plane U y ν j := by
          simp only [plane_read]; rw [turn_away,turn_away,turn_away,turn_away] <;> simp [hj,h,hu]
        simp_rw [hc]; exact hasDerivAt_const _ _
  apply HasDerivAt.congr_deriv (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => H i))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), Finset.sum_eq_single (x-step j)]
  · simp [Q, hx, inner_sub_right]; try ring
  · intro b hb hb'; unfold Q; rw [if_neg (Finset.ne_of_mem_erase hb), if_neg hb']
  simp [hx]

lemma side_flux (hn : 2 ≤ n.val) (A : G.Color) (p : PlaqAxes) :
    HasDerivAt (fun t : ℝ => ∑ y : Site n, G.price (faceValue (turnLink (x,ν) A t U) (y,p)))
      (inner ℝ A (flux U (x,ν) p)) 0 := by
  rcases p with ⟨⟨i,j⟩,h⟩
  change i < j at h
  unfold flux
  dsimp only
  split
  next H => subst i; exact forward_sum U x ν hn A j h.ne'
  next H =>
    split
    next he =>
      subst j
      change HasDerivAt (fun t : ℝ => ∑ y : Site n, G.price (plane _ y i ν))
        (inner ℝ A (-(G.curvature (plane U x i ν)- G.adjoint (U (x-step i,i))⁻¹ (G.curvature (plane U (x-step i) i ν))))) 0
      simp_rw [plane_swap _ _ ν i,G.price_inv,G.curvature_inv,map_neg,neg_sub_neg, neg_sub]
      exact forward_sum U x ν hn A i H
    next he =>
      rw [inner_zero_right]
      change HasDerivAt (fun t : ℝ => ∑ y : Site n, G.price (plane _ y i j)) _ 0
      have hc (t : ℝ) (y : Site n) : plane (turnLink (x,ν) A t U) y i j = plane U y i j := by
        simp only [plane_read]; rw [turn_away,turn_away,turn_away,turn_away] <;> simp [he,H]
      simp_rw [hc]; exact hasDerivAt_const _ _

lemma field_deriv (e : Edge (Site n)) (hn : 2 ≤ n.val) (A : G.Color) :
    HasDerivAt (fun t : ℝ => energy (turnLink e A t U)) (inner ℝ A (field U e)) 0 := by
  simp only [energy]
  simp_rw [Fintype.sum_prod_type, Finset.sum_comm (s:=Finset.univ (α:=Site n)) (t:= Finset.univ (α:=PlaqAxes))]
  rw [field,inner_sum]
  exact HasDerivAt.fun_sum (fun p _ => side_flux U e.1 e.2 hn A p)
end Gradient

section Parts

lemma continuous_ad (G : Gauge) : Continuous (fun u : G.El × G.Color => G.adjoint u.1 u.2) := by
  change Continuous (fun u : G.El × G.Color => G.projectColor (G.mat u.1 * G.colorMat u.2 * star (G.mat u.1)))
  exact G.projectColor.continuous_of_finiteDimensional.comp
    (((G.continuous_mat.comp continuous_fst).mul (G.colorMat.continuous_of_finiteDimensional.comp continuous_snd)).mul
      ((G.continuous_mat.comp continuous_fst).star))

lemma continuous_field {R : Type*} [AddCommGroup R] [One R] (G : Gauge) (e : Edge (Four R)) :
    Continuous (fun V : Links R G.El => field V e) := by
  have hs (x : Four R) (b : Axis) (p : PlaqAxes) : Continuous (fun V : Links R G.El => stem V x b p) := by
    have hc (z : Four R) : Continuous fun V : Links R G.El => G.curvature (faceValue V (z,p)) :=
      G.continuous_curvature.comp (continuous_travel ..)
    have hd : Continuous (fun V : Links R G.El => (V (x-step b,b))⁻¹) := (continuous_apply _).inv
    have he := (continuous_ad G).comp (hd.prodMk (hc (x-step b)))
    exact (hc x).sub he
  unfold field
  apply continuous_finsetSum; intro p _
  by_cases h : p.val.1 = e.2
  · simp only [flux,h,↓reduceIte]; exact hs ..
  by_cases hx : p.val.2=e.2
  · simp only [flux,h,hx,↓reduceIte]; exact (hs ..).neg
  simp only [flux,h,hx,↓reduceIte]; exact continuous_const

variable (e : Edge (Site n)) (A : G.Color) {W S W' : Config G n → ℂ}

lemma times_integrable {μ : Measure (Config G n)} [IsFiniteMeasure μ] (hW : Continuous W) (hS : RG.Envelope S) :
    Integrable (fun U => W U*S U) μ := by
  obtain ⟨K,hK⟩ := hS.cost
  apply Integrable.mul_bdd ?_ hS.meas.aestronglyMeasurable (Eventually.of_forall hK)
  exact hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_variation (hW : Continuous W) (hW' : Continuous W')
    (h : ∀ U : Config G n, HasDerivAt (fun t : ℝ => W (turnLink e A t U)) (W' U) 0)
    (hS : RG.Envelope S) (he : ∀ (V : Config G n) t, S (turnLink e A t V) = S V) :
    (∫ U, W' U * S U ∂(prior G n)) = 0 := by
  let f (s : ℝ) (P : Config G n) := W (turnLink e A s P)* S P
  let g (s : ℝ) (P : Config G n) := W' (turnLink e A s P)* S P
  have ha (V : Config G n) (s : ℝ) : HasDerivAt (fun t : ℝ => f t V) (g s V) s := by
    have ht : HasDerivAt (fun t : ℝ => W (turnLink e A t V)) (W' (turnLink e A s V)) s := by
      let R := turnLink e A s V
      have hu : HasDerivAt (fun t : ℝ => t-s) 1 s := by
        simpa using! ((hasDerivAt_id' s).sub_const s)
      have hh : HasDerivAt (fun t : ℝ => W (turnLink e A t R)) (W' R) (s-s) := by rw [sub_self]; exact h R
      have hc (t : ℝ) : turnLink e A (t-s) R = turnLink e A t V := by rw [← turn_add,sub_add_cancel]
      simpa only [Function.comp_def,hc, one_smul] using hh.scomp (h:=fun t => t-s) s hu
    exact ht.mul_const _
  let μ := prior G n
  have hk (s) : (∫ U, f s U ∂μ) = ∫ U, W U * S U ∂μ := by
    let Q (u : Config G n) := W u * S u
    have he' : f s = Q ∘ turnLink e A s := funext fun u => by simp only [f,Q,Function.comp_apply,he]
    rw [he']
    have ht := turn_preserving (n:=n) e A s
    haveI : (prior G n).IsMulLeftInvariant := by unfold prior; infer_instance
    apply ht.integral_comp ?_ Q
    have hb : turnLink (G:=G) e A s = (Homeomorph.mulLeft (turnLink (G:=G) e A s 1)) := by
      funext U b
      change _ = turnLink e A s 1 b * U b
      by_cases h : b=e <;> simp [turnLink,h,Function.update_of_ne]
    rw [hb]; exact (Homeomorph.mulLeft _).measurableEmbedding
  obtain ⟨K,hK⟩ := hS.cost
  obtain ⟨D,hD⟩ := hW'.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  have h0 : f 0 = (fun V => W V * S V) := funext fun _ => by simp [f]
  have hv : g 0 = (fun V => W' V * S V) := funext fun _ => by simp [g]
  have hr : HasDerivAt (fun t => ∫ U, f t U ∂μ) (∫ U, g 0 U ∂μ) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := f) (F':=g) (μ:=μ) (bound:=fun _ => D*K)
      (s:=univ) univ_mem (Eventually.of_forall fun x => ?_) ?_ ?_ (Eventually.of_forall fun V x _ => ?_) ?_
      (Eventually.of_forall fun V x _ => ha V x)).2
    · exact ((hW.measurable.comp (turn_preserving e A x).measurable).mul hS.meas).aestronglyMeasurable
    · rw [h0]; exact times_integrable hW hS
    · rw [hv]; exact (hW'.measurable.mul hS.meas).aestronglyMeasurable
    · unfold g; rw [norm_mul]
      exact mul_le_mul (hD _) (hK _) (norm_nonneg _) ((norm_nonneg _).trans (hD V))
    · exact integrable_const _
  simp_rw [hk,hv] at hr
  exact hr.unique (hasDerivAt_const ..)

/-- Haar integration by parts with β of either sign (also β=0 here).
Divergence is not optional if the multiplier X uses the same link. S
can carry any bounded measurable spectator with the stated avoidance;
not assumed gauge invariant. -/
theorem ibp (β : ℝ) (hn : 2 ≤ n.val) (hW : Continuous W) (hW' : Continuous W')
    (h : ∀ U : Config G n, HasDerivAt (fun t : ℝ => W (turnLink e A t U)) (W' U) 0)
    (hS : RG.Envelope S) (he : ∀ (V : Config G n) t, S (turnLink e A t V) = S V) :
    moment β (fun U => (W' U - (β * inner ℝ A (field U e) : ℝ) * W U) * S U) = 0 := by
  let Q := fun U : Config G n => W' U - ((β * inner ℝ A (field U e) : ℝ) : ℂ) * W U
  have hq : Continuous Q := hW'.sub ((Complex.continuous_ofReal.comp
    ((continuous_const (y:=β)).mul (continuous_const (y:=A)|>.inner (continuous_field G e)))).mul hW)
  let B := fun U : Config G n => (bare β U : ℂ)
  have hb : Continuous B := Complex.continuous_ofReal.comp (bare_cont _)
  have hr (U : Config G n) : HasDerivAt (fun t => B (turnLink e A t U))
      (- ((β * inner ℝ A (field U e) : ℝ) : ℂ) * B U) 0 := by
    refine (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (((field_deriv U e hn A).const_mul (-β)).exp)).congr_deriv ?_
    simp [B,bare, Complex.ofReal_mul]; ring
  have hz := integral_variation e A (W := fun U => B U * W U) (W':=fun U => B U * Q U)
    (hb.mul hW) (hb.mul hq) (fun U => ((hr U).mul (h U)).congr_deriv (by simp only [turn_zero,Q]; ring)) hS he
  change moment β (fun U => Q U * S U) = 0
  rw [moment_formula β _ (times_integrable hq hS)]
  simp_rw [mul_assoc] at hz
  change _ * (∫ U, B U * (Q U * S U) ∂prior G n) = _
  rw [hz,mul_zero]

lemma equation_silent (β : ℝ) (hn : 2 ≤ n.val) (hh : β ≠ 0) (hS : RG.Envelope S)
    (he : ∀ (V : Config G n) t, S (turnLink e A t V) = S V) :
    moment β (fun U => (inner ℝ A (field U e):ℂ) * S U) = 0 := by
  have ht := ibp e A (W:=1) (W':=0) β hn continuous_const continuous_const (fun _ => hasDerivAt_const ..) hS he
  simp only [Pi.zero_apply, Pi.one_apply, mul_one, zero_sub,Complex.ofReal_mul,← neg_mul, mul_assoc,
    moment,integral_const_mul] at ht
  exact (mul_eq_zero.mp ht).resolve_left (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hh))
end Parts
end YM.Push.Mark
