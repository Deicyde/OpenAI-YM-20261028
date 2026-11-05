import YM.Source.Construction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Finite-cutoff Wilson laws (independent bare coordinate)

For fixed continuous tests, including the literal C.O labels and their finite products frozen
at the successful real trial. This does not recalibrate to a new coarse target, nor give
cutoff-uniform complex-neighborhood bounds. Useful only locally at a given (N,p), or when
combined with information coordinating an effective trajectory across parameters/cutoffs.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Extension.UV.Bare
open Lattice Wilson MeasureTheory Topology Filter Set
open scoped BigOperators NNReal ENNReal
variable {G : Gauge} {n : Side}

def numerator (f : Config G n→ℂ) (s : ℂ) := ∫ U, Complex.exp (s*(-energy U)) * f U ∂prior G n

theorem entire (f : Config G n→ℂ) (hf : Continuous f) : AnalyticOnNhd ℂ (numerator f) univ := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  intro z hz
  let D := Config G n; let μ:=prior G n
  let w (s:ℂ) (x:D):= Complex.exp (s*(-energy x)) * f x
  let w' (s:ℂ) (x:D):= Complex.exp (s*(-energy x)) * (-energy x) * f x
  have hc s (x:D) : HasDerivAt (w · x) (w' s x) s := by
    unfold w w'; exact (((hasDerivAt_id' _).mul_const _).cexp.mul_const _).congr_deriv (by rw [one_mul]) -- order maybe comm
  have hi (s:ℂ): Continuous (w s):= by unfold w; fun_prop
  have hx (s:ℂ): Continuous (w' s):= by unfold w'; fun_prop
  have hj : Continuous fun p:ℂ×D=> w' p.1 p.2:= by unfold w'; fun_prop
  obtain ⟨C,hC⟩:= ((isCompact_closedBall z 1).prod (isCompact_univ (X:=D))).bddAbove_image hj.norm.continuousOn
  have hab := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall fun a=> (hi a).aestronglyMeasurable (μ:=μ)) ((hi z).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ:=μ)) (bound:=fun _:D=>C) (hx z).aestronglyMeasurable (Eventually.of_forall fun a y hy=> hC ⟨⟨y,a⟩,⟨Metric.ball_subset_closedBall hy,mem_univ _⟩,rfl⟩) (integrable_const _) (Eventually.of_forall fun _ _ _=> hc ..)
  exact hab.2.differentiableAt.differentiableWithinAt

lemma at_real {f : Config G n→ℂ} (s : ℝ) : numerator f (s:ℂ)= ∫ U, (bare s U:ℂ)*f U ∂prior G n := by
  apply integral_congr_ae; filter_upwards with U; rw [← Complex.ofReal_neg,← Complex.ofReal_mul,bare]; norm_cast; ring_nf

theorem partition_value (s : ℝ) : numerator (G:=G) (n:=n) 1 (s:ℂ) = partition G n s:= by rw [partition, ← integral_complex_ofReal]; simpa [partition] using at_real (f:=(1:Config G n→ℂ)) s
lemma partition_ne (s : ℝ) : numerator (G:=G) (n:=n) 1 (s:ℂ) ≠ 0:= by rw [partition_value]; exact_mod_cast (partition_pos s).ne'

def expectation (f : Config G n→ℂ) (s : ℂ) := numerator f s / numerator (G:=G) (n:=n) 1 s
lemma agrees (f : Config G n→ℂ) (hf : Continuous f) (s:ℝ) : expectation f (s:ℂ) = moment s f := by
  rw [moment_formula _ _ (continuous_integrable _ hf),expectation,partition_value, at_real]; ring

lemma zeroFree (t : ℝ) : ∃ r>0,∀ s∈Metric.ball (t:ℂ) r, numerator (n:=n) (G:=G) 1 s≠0:= by
  let c:= (t:ℂ)
  have h:= (entire (G:=G) (n:=n) 1 continuous_const c trivial).continuousAt
  have he := h (isOpen_ne.mem_nhds (partition_ne t)) -- need isOpen of complement
  obtain ⟨r,hr,ha⟩:= Metric.mem_nhds_iff.1 he
  exact ⟨r,hr,ha⟩

lemma continuation (t : ℝ) : ∃ r>0, ∀ f : Config G n→ℂ, Continuous f → AnalyticOnNhd ℂ (expectation f) (Metric.ball (t:ℂ) r) := by
    obtain ⟨r,hr,ha⟩:=zeroFree (G:=G) (n:=n) t
    exact ⟨r,hr,fun f hf s hs=> (entire f hf s trivial).div (entire 1 continuous_const s trivial) (ha _ hs)⟩

theorem physical (C : Family G) (N p : ℕ) : ∃ r>0, ∀ k : ℕ, ∀ d : Fin k→ℕ, ∀ x:(i:Fin k)→C.label (d i),∀ o:Fin k→Site (C.side N p), let f (U:Config G (C.side N p)):= ∏ i, C.O N p (x i) (o i) U
    AnalyticOnNhd ℂ (expectation f) (Metric.ball (C.beta N p:ℂ) r) ∧ (∀ s:ℝ, expectation f (s:ℂ)=moment s f) ∧ expectation f (C.beta N p)=C.omega N p f:= by
  obtain ⟨r,hr,H⟩ := continuation (G:=G) (n:=C.side N p) (C.beta N p)
  refine ⟨r,hr,fun k d x o=>?_⟩
  intro f; have h:Continuous f:=by unfold f; exact continuous_finsetProd _ (fun i _=> C.continuousO _ _ _ _ _)
  exact ⟨H _ h,agrees _ h, agrees _ h _⟩
end YM.Extension.UV.Bare
