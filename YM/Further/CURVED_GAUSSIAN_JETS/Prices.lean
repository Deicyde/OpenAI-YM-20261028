import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Profile
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.STATIONARY_UNIFORM.Prediction


/-!
#  compulsory direct & noise first derivatives in a decentered chart

Post-L, true tagged predictor and curvatures (not the derivative of an
ideal noise centered at U(sa)). Work before any truncation of vertices.
These are simultaneous uniform estimates on the near-identity two-link
coordinate ball; in LocalRows transfer to a separate patch gauge
for each read in the lower bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Ball
open Function Filter Set Metric Gauge Lattice Wilson RG Precision Work Exterior Pressure Bid Push.Uniform
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {G : Gauge} {c f n : Side}

abbrev Pair (G : Gauge) (f : Side) := Dir G f × Dir G f
def build (u : Pair G f) := increment (represent u.2) (collect G u.1)

def paint (G : Gauge) : G.Mat →L[ℝ] G.Color := G.projectColor.toContinuousLinearMap.comp
    ((1/2:ℝ) • (ContinuousLinearMap.id ℝ G.Mat - (starL' ℝ (A:=G.Mat)).toContinuousLinearMap))
lemma curvature_eq (u : G.El) : paint G (G.mat u) = G.curvature u := by rw [Gauge.curvature, G.mat_inv]; rfl

lemma input_jets {n : ℕ} {E : ℝ} (h : ExpReceipt G n E) (m : Side) :
    let C := composeCost n (composeCost n E 1) 1
    Push.Uniform.Inputs (build (G:=G) (f:=m)) n ((2^n)*C*C) := by
  intro C
  have ht := represented (n:=n) h m
  have hC : 0≤C := by unfold C composeCost; have := ht.2.1; dsimp only [composeCost] at this; positivity
  refine ⟨by unfold build; simp; exact link_one,by positivity,fun i x hx=> ?_⟩
  have he (L : Pair G m →L[ℝ] Dir G m) (hL : ‖L‖ ≤ 1) : Allows n (fun z=> G.mat (represent (L z) i)) x C := by
    have hl : ‖L x‖ ≤ 1 := (L.le_opNorm _).trans (mul_le_one₀ hL (norm_nonneg _) hx)
    exact (ht.2.2 i (L x) hl).comp (g:=fun v=>G.mat (represent v i)) (allows_linear hL hl)
  have hh := (he (.fst ℝ _ _) (ContinuousLinearMap.norm_fst_le ..)).times (he (.snd ℝ _ _) (ContinuousLinearMap.norm_snd_le ..))
  simpa only [build,increment, ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',represent,Pi.one_apply,mul_one] using! hh

def direct (p : Cell f) (x : Pair G f) := G.curvature (faceValue (build x) p)
def noise (S : StepData c f) (k : S.Choices) (p : Bond c) (x : Pair G f) := G.mat (S.prediction (build x) k p)

theorem allows (G : Gauge) (P : Patch) (K : KernelChoices) : ∃ δ C : ℝ, 0<δ ∧ 0<C ∧
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → ∀ x : Pair G f, ‖x‖<δ →
      (∀ p, Allows 2 (direct p) x C) ∧ (∀ k p, Allows 2 (noise S k p) x C) := by
  obtain ⟨E,hE,H⟩ := exp_receipt G 3
  obtain ⟨D,δ,hD⟩ := log_receipt G
  obtain ⟨F,r,hF,h⟩ := focus_receipt G 2
  have hu := input_jets H
  let C := composeCost 3 (composeCost 3 E 1) 1
  let R := predictionRadius P G K 2 E ((2:ℝ)^3*C*C) D δ r
  let S₀ : StepData 1 P.L := ⟨P,K,by simp⟩
  have hR := prediction_radius_pos S₀ (hu _) (le_refl 2) H hD h
  let norm' {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
  let A := norm' (E:=G.Mat) (F:=G.Color) (paint G) * travelCost G 3 4 ((2:ℝ)^3*C*C)
  let B := composeCost 2 F (connectorCost P G 2 E ((2:ℝ)^3*C*C))
  refine ⟨min 1 R,1+|A|+|B|,lt_min zero_lt_one hR,by positivity, fun {c f} S hP hK x hx=>?_⟩
  have hx1 := hx.trans_le (min_le_left ..); have hx2 := hx.trans_le (min_le_right ..)
  refine ⟨fun p=>?_,fun k p=> ?_⟩
  · have he := travel_jets (n:=f) (N:=3) (fun i => (hu f).2.2 i x hx1.le) p.1 (w:=square p.2.val.1 p.2.val.2) (a:=4) le_rfl
    unfold direct faceValue; simp_rw [← curvature_eq]
    exact ((he.linear (paint G) le_rfl).order (by decide)).mono (by change A ≤ _; linarith [le_abs_self A,abs_nonneg B])
  have hv := prediction_pay S (hu _) (le_refl 2) H hD h x (by rw [hP,hK,mem_ball_zero_iff]; exact hx2) k p
  rw [hP] at hv; exact hv.mono (by change B ≤ _; linarith [le_abs_self B,abs_nonneg A])

section slope
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r C : ℝ} {f : X×X → Y}
lemma gradient (h : ∀ x : X×X, ‖x‖ < r → Allows 2 f x C) (x : X×X) (hx : ‖x‖ < r) :
    ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ C*‖x‖ := by
  have hr := (norm_nonneg _).trans_lt hx
  simpa only [sub_zero] using (convex_ball (0:X × X) r).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=fderiv ℝ f)
      (fun i hi => ((h i (by simpa using hi)).analytic.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp))
      (C:=C) (fun i hi=> by rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact (h i (by simpa using hi)).norm_le _ le_rfl)
      (mem_ball_self hr) (show x∈ball 0 r by simpa)
lemma chart_diff (h : ∀ x : X×X, ‖x‖ < r → Allows 2 f x C) (x y : X) (hx : ‖x‖ < r) :
    HasDerivAt (fun t : ℝ => f (t • y,x)) (fderiv ℝ f (0,x) (y,0)) 0 := by
  have hp : ‖((0:ℝ) • y,x)‖ < r := by simpa [Prod.norm_def]
  simpa only [zero_smul,one_smul] using! ((h _ hp).analytic.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
    (((hasDerivAt_id' (0:ℝ)).smul_const y).prodMk (hasDerivAt_const (0:ℝ) x))
lemma fares (h : ∀ x : X×X, ‖x‖ < r → Allows 2 f x C) (x y : X) (hx : ‖x‖ < r) {z : Y}
    (he : HasDerivAt (fun t : ℝ => f (t • y,0)) z 0) :
    ‖z‖ ≤ ‖deriv (fun t : ℝ => f (t • y,x)) 0‖ + C*‖x‖*‖y‖ := by
  have hr := (norm_nonneg _).trans_lt hx
  rw [(chart_diff h _ _ hx).deriv, he.unique (chart_diff h _ _ (by simpa only [norm_zero]))]
  let A := fderiv ℝ f (0,x); let B := fderiv ℝ f (0,0)
  have ht : ‖B (y,0) - A (y,0)‖ ≤ C*‖x‖*‖y‖ := calc
    _ ≤ ‖B-A‖*‖(y,(0:X))‖ := (B-A).le_opNorm _
    _ ≤ _ := by rw [norm_sub_rev,Prod.norm_def]; simp only [norm_zero,max_eq_left (norm_nonneg _)]; exact mul_le_mul_of_nonneg_right
                    (by have he := gradient h ((0:X),x) (by simpa [Prod.norm_def]); rw [Prod.norm_def] at he; exact he.trans_eq (by simp)) (norm_nonneg y)
  exact le_trans (by simpa using norm_sub_le (A (y,0)) (A (y,0)-B (y,0))) (by rw [norm_sub_rev]; linarith only [ht])
end slope

lemma zero_direct (p : Cell f) (y : Dir G f) :
    HasDerivAt (fun t : ℝ => direct p (t • y,0)) (F03.faceCurl p y) 0 := by
  unfold direct build; simp_rw [link_one]; exact F03.curvature_of_hasDerivAt (F03.face_deriv p y)
lemma zero_noise (S : StepData c f) (h : S.patch.Branches S.kernel G) (k : S.Choices) (p : Bond c) (y : Dir G f) :
    HasDerivAt (fun t : ℝ => noise S k p (t • y,0)) (G.colorMat (bills S y (p.1,coord p.2))) 0 := by
  unfold noise build; simp_rw [link_one]; exact Push.prices S h p k y
end YM.Further.CurvedGaussianJets.Ball
