import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06
import YM.Work.F02.Series




/-!
# Dimension-independent jet estimates for the actual score project

Use at a point of a *real* analytic neighborhood on any of the actual finite
periods. Need counting curvature/gauge-coordinate derivatives, in particular
we cannot transfer arbitrary finite-dimensional equivalences into these bounds.
Here are tools to keep the norm in a hypothesis; for Pi, sup. For the path
terms with coefficients exponentially summable in their **true** lengths a
useful trick is to pass to entire ambient polynomial variables temporarily
(F02); then we want real jets and real implicit-function estimates in
subsequent calculations. Use un-divided iterated Fréchet derivatives.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric
open scoped Topology ContDiff BigOperators

section Jets

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Norms through n, *including the value*. Use on each read of a score (later
sum & derive localization of its tensors, don't claim a sup→scalar bound
uniform in volume on the summed score). -/
structure Allows (n : ℕ) (f : E → F) (x : E) (C : ℝ) : Prop where
  analytic : ContDiffAt ℝ ω f x
  norm_le (k : ℕ) : k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ C

variable {n k : ℕ} {x : E} {f f' : E → F} {g : F → G} {C K M : ℝ}

lemma Allows.nonneg (h : Allows n f x C) : 0 ≤ C := (norm_nonneg _).trans (h.norm_le 0 (Nat.zero_le _))
lemma Allows.value (h : Allows n f x C) : ‖f x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using h.norm_le 0 (Nat.zero_le _)

lemma Allows.mono (h : Allows n f x C) (hC : C ≤ M) : Allows n f x M :=
  ⟨h.analytic, fun _ hk => (h.norm_le _ hk).trans hC⟩
lemma Allows.order (h : Allows n f x C) (hk : k ≤ n) : Allows k f x C :=
  ⟨h.analytic, fun _ hj => h.norm_le _ (hj.trans hk)⟩
lemma Allows.germ (h : Allows n f x C) (he : f =ᶠ[𝓝 x] f') : Allows n f' x C := by
  refine ⟨h.analytic.congr_of_eventuallyEq he.symm, fun k hk => ?_⟩
  rw [← (he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]; exact h.norm_le _ hk

lemma allows_const (x : E) {v : F} (hv : ‖v‖ ≤ C) : Allows n (fun _ : E => v) x C := by
  refine ⟨contDiffAt_const, fun k _ => ?_⟩
  by_cases hk : k=0
  · subst k; rwa [norm_iteratedFDeriv_zero]
  rw [iteratedFDeriv_const_of_ne hk, Pi.zero_apply,norm_zero]
  exact (norm_nonneg _).trans hv

lemma allows_linear {L : E →L[ℝ] F} (h : ‖L‖ ≤ C) (h' : ‖L x‖ ≤ C) : Allows n L x C := by
  refine ⟨L.contDiff.contDiffAt, fun k _ => ?_⟩
  cases k with
  | zero => rwa [norm_iteratedFDeriv_zero]
  | succ k =>
    rw [iteratedFDeriv_succ_eq_comp_right,comp_apply, LinearIsometryEquiv.norm_map]
    simp_rw [L.fderiv]
    cases k with
    | zero => rwa [norm_iteratedFDeriv_zero]
    | succ k => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply]; change ‖(0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => E) (E →L[ℝ] F))‖ ≤ C; exact (@norm_zero (ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => E) (E →L[ℝ] F)) _).le.trans ((norm_nonneg L).trans h)

lemma Allows.add (h : Allows n f x C) (h' : Allows n f' x K) : Allows n (fun u => f u + f' u) x (C+K) := by
  refine ⟨h.analytic.add h'.analytic, fun k hk => ?_⟩
  change ‖iteratedFDeriv ℝ k (f + f') _‖ ≤ _
  rw [iteratedFDeriv_add_apply (h.analytic.of_le le_top) (h'.analytic.of_le le_top)]
  exact (norm_add_le ..).trans (add_le_add (h.norm_le _ hk) (h'.norm_le _ hk))

lemma Allows.smul (h : Allows n f x C) (a : ℝ) : Allows n (fun u => a • f u) x (|a| * C) := by
  refine ⟨h.analytic.const_smul _, fun k hk => ?_⟩
  change ‖iteratedFDeriv ℝ k (a • f) _‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (h.analytic.of_le le_top),norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h.norm_le _ hk) (abs_nonneg _)

lemma allows_sum {ι : Type*} {s : Finset ι} {f : ι → E → F} {C : ι → ℝ} (h : ∀ i∈s, Allows n (f i) x (C i)) :
    Allows n (fun u => ∑ i∈s, f i u) x (∑ i∈s, C i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using allows_const (n:=n) x (v:=(0:F)) (C:=0) (by simp)
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun _ hj => h _ (Finset.mem_insert_of_mem hj))

lemma Allows.pair {g : E → G} (h : Allows n f x C) (h' : Allows n g x C) : Allows n (fun u => (f u, g u)) x C := by
  refine ⟨h.analytic.prodMk h'.analytic, fun k hk => ?_⟩
  rw [iteratedFDeriv_prodMk h.analytic h'.analytic le_top,ContinuousMultilinearMap.opNorm_prod]
  exact max_le (h.norm_le _ hk) (h'.norm_le _ hk)

lemma allows_pi {ι : Type*} [Fintype ι] {f : E → (ι → F)} (hC : 0 ≤ C) (h : ∀ i, Allows n (fun x => f x i) x C) :
    Allows n f x C := by
  have he : ContDiffAt ℝ ω f x := contDiffAt_pi.mpr fun i => (h i).analytic
  refine ⟨he, fun k hk => ContinuousMultilinearMap.opNorm_le_bound hC (fun v => ?_)⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (by positivity))).mpr; intro i
  let L : (ι → F) →L[ℝ] F := ContinuousLinearMap.proj i
  have hh : iteratedFDeriv ℝ k f x v i = iteratedFDeriv ℝ k (fun u => f u i) x v := by
    change L _ = iteratedFDeriv ℝ k (L ∘ f) x v
    rw [L.iteratedFDeriv_comp_left he le_top]; rfl
  rw [hh]
  exact ((iteratedFDeriv ℝ k (fun u => f u i) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((h i).norm_le _ hk) (by positivity))

lemma Allows.linear (L : F →L[ℝ] G) (h : Allows n f x C) (hL : ‖L‖ ≤ K) : Allows n (fun u => L (f u)) x (K*C) := by
  refine ⟨L.contDiff.contDiffAt.comp x h.analytic, fun k hk => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left h.analytic (n:=k) le_top).trans
    (mul_le_mul hL (h.norm_le _ hk) (norm_nonneg _) ((norm_nonneg _).trans hL))

lemma open_patch {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : E} {f : E → F}
    (h : ContDiffAt 𝕜 ω f x) : ∃ s : Set E, x ∈ s ∧ IsOpen s ∧ ContDiffOn 𝕜 ω f s := by
  obtain ⟨u,hu,he⟩ := h.contDiffOn (m:=ω) le_rfl (fun _ => rfl)
  obtain ⟨s,hs,ht,hh⟩ := _root_.mem_nhds_iff.mp hu
  exact ⟨s,hh,ht,he.mono hs⟩

def composeCost (n : ℕ) (K C : ℝ) : ℝ := (n.factorial:ℝ) * K * (1+C)^n
lemma Allows.comp (hg : Allows n g (f x) K) (hf : Allows n f x C) : Allows n (fun u => g (f u)) x (composeCost n K C) := by
  have hs : ContDiffAt ℝ ω (g ∘ f) x := hg.analytic.comp x hf.analytic
  refine ⟨hs, fun k hk => ?_⟩
  obtain ⟨t,ht,ht',H⟩ := open_patch hg.analytic
  obtain ⟨u,hu,hu',H'⟩ := open_patch hf.analytic
  obtain ⟨s,he,he',hm⟩ := _root_.mem_nhds_iff.mp (inter_mem (hu'.mem_nhds hu)
    (hf.analytic.continuousAt.preimage_mem_nhds (ht'.mem_nhds ht)))
  have hx : 1 ≤ 1+C := le_add_of_nonneg_right hf.nonneg
  change ‖iteratedFDeriv ℝ k (g ∘ f) _‖ ≤ _
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv he'.uniqueDiffOn (hs.of_le le_top) hm]
  apply le_trans (norm_iteratedFDerivWithin_comp_le H (H'.mono fun i hi => (he hi).1) le_top ht'.uniqueDiffOn he'.uniqueDiffOn
    (fun y hy => (he hy).2) hm (C:=K) (D:=1+C) ?_ ?_) ?_
  · intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv ht'.uniqueDiffOn (hg.analytic.of_le le_top) ht]
    exact hg.norm_le i (hi.trans hk)
  · intro i hi hj
    rw [iteratedFDerivWithin_eq_iteratedFDeriv he'.uniqueDiffOn (hf.analytic.of_le le_top) hm]; apply (hf.norm_le _ (hj.trans hk)).trans
    exact le_trans (le_add_of_nonneg_left zero_le_one) (le_self_pow₀ hx (by omega))
  have hK := hg.nonneg
  unfold composeCost
  gcongr

lemma Allows.bilinear (L : F →L[ℝ] G →L[ℝ] D) {g : E → G} (hf : Allows n f x C) (hg : Allows n g x K) (h : ‖L‖ ≤ M) :
    Allows n (fun y => L (f y) (g y)) x (2^n * M * C * K) := by
  refine ⟨(L.contDiff.contDiffAt.comp x hf.analytic).clm_apply hg.analytic, fun k hk => ?_⟩
  have hm := (norm_nonneg L).trans h
  have hc := hf.nonneg
  have hh := hg.nonneg
  obtain ⟨u,hu,hu',H⟩ := open_patch hf.analytic
  obtain ⟨s,hs,hs',H'⟩ := open_patch hg.analytic
  have hsu : UniqueDiffOn ℝ (s ∩ u) := (hs'.inter hu').uniqueDiffOn
  have hx : x ∈ s∩u := ⟨hs,hu⟩
  have he : ContDiffAt ℝ ω (fun y => L (f y) (g y)) x :=
    (L.contDiff.contDiffAt.comp x hf.analytic).clm_apply hg.analytic
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hsu (he.of_le le_top) hx]
  apply le_trans (L.norm_iteratedFDerivWithin_le_of_bilinear (H.mono inter_subset_right) (H'.mono inter_subset_left) hsu hx le_top) ?_
  -- Leibniz bound
  calc
    _ ≤ M * ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ) * C * K := by
      refine mul_le_mul h (Finset.sum_le_sum fun i hi => ?_) ?_ hm
      · have hi := Finset.mem_range.mp hi
        rw [iteratedFDerivWithin_eq_iteratedFDeriv hsu (hf.analytic.of_le le_top) hx,
          iteratedFDerivWithin_eq_iteratedFDeriv hsu (hg.analytic.of_le le_top) hx]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hf.norm_le i (by omega)) (by positivity))
          (hg.norm_le _ (by omega)) (norm_nonneg _) (by positivity)
      positivity
    _ = 2^k * M * C * K := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]; ring
    _ ≤ _ := by gcongr; norm_num

/-- Dimensionful constant permissible here *only* on the local color/chart
inputs independent of L. No selecting this on volume-dependent domains. -/
lemma exists_allows {s : Set E} (hs : IsCompact s) (h : ∀ x∈s, ContDiffAt ℝ ω f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈s, Allows n f x C := by
  have he (k : ℕ) : ContinuousOn (fun x => iteratedFDeriv ℝ k f x) s := fun x hx =>
    ((h x hx).continuousAt_iteratedFDeriv le_top).continuousWithinAt
  choose C hC using fun k => hs.exists_bound_of_continuousOn (he k)
  let A := ∑ i ∈ Finset.range (n+1), |C i|
  refine ⟨A, by unfold A; positivity, fun x hx => ⟨h x hx, fun i hi => ?_⟩⟩
  exact (hC _ x hx).trans ((le_abs_self _).trans (Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_range.mpr (by omega))))
end Jets

section Cauchy

def cauchyCost : ℕ → ℝ → ℝ → ℝ
  | 0, _, M => M
  | n+1, R, M => cauchyCost n (R/2) (M/(R/2))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

-- universe equalities in induction
lemma entire_bound {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (k : ℕ)
    {f : E → F} {x : E} {R M : ℝ} (ht : ContDiff ℂ ω f)
    (hR : 0 < R) (h : ∀ y ∈ ball x R, ‖f y‖ ≤ M) :
    ‖iteratedFDeriv ℂ k f x‖ ≤ cauchyCost k R M := by
  induction k generalizing F R M with
  | zero => rw [norm_iteratedFDeriv_zero]; exact h _ (mem_ball_self hR)
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_right,comp_apply, LinearIsometryEquiv.norm_map,cauchyCost]; apply ih
    · exact ht.fderiv_right (by simp)
    · positivity
    intro y hy; exact Work.F02.fderiv_bound (ht.differentiable (by simp)) hR h hy

-- convenient looser explicit growth
lemma cauchyCost_le (k : ℕ) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    cauchyCost k R M ≤ M * (((2:ℝ)^k / R)^k) := by
  induction k generalizing M R with
  | zero => simp [cauchyCost]
  | succ k ih =>
    rw [cauchyCost]
    apply le_trans (ih (show 0 ≤ M/(R/2) by positivity) (half_pos hR))
    rw [show ((2:ℝ)^k/(R/2))= 2^(k+1)/R by rw [pow_succ]; ring]
    rw [pow_succ (a:=2^(k+1)/R)]
    rw [show M * ((2^(k+1)/R)^k * (2^(k+1)/R)) = (M*(2^(k+1)/R))* ((2^(k+1)/R)^k) by ring]
    rw [div_eq_mul_inv M]
    gcongr
    rw [show (R/2)⁻¹ = 2 / R by ring]
    gcongr
    exact le_self_pow₀ (by norm_num) (by omega)

lemma allows_real_of_entire {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (k : ℕ) {f : E → F} {x : E} {R M : ℝ} (ht : ContDiff ℂ ω f) (hR : 0 < R)
    (h : ∀ y ∈ ball x R, ‖f y‖ ≤ M) : Allows k f x (M * ((1+(2:ℝ)^k/R)^k)) := by
  have hm := (norm_nonneg _).trans (h _ (mem_ball_self hR))
  refine ⟨ht.contDiffAt.restrict_scalars ℝ, fun i hi => ?_⟩
  rw [← ((ht.of_le (m:= (i:ℕ∞ω)) le_top).contDiffAt).restrictScalars_iteratedFDeriv,
    Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars]
  apply le_trans ((entire_bound i ht hR h).trans (cauchyCost_le _ hm hR))
  apply mul_le_mul_of_nonneg_left _ hm
  apply le_trans ?_ (pow_le_pow_right₀ (show (1:ℝ) ≤ 1+2^k/R from le_add_of_nonneg_right (by positivity)) hi)
  gcongr
  apply le_trans ?_ (show (2:ℝ)^k/R ≤ 1+ (2:ℝ)^k/R from le_add_of_nonneg_left zero_le_one)
  gcongr
  norm_num
end Cauchy
end YM.Push.Uniform
