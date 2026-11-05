import Mathlib.Analysis.Complex.Schwarz
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
import YM.Next.FOUNDATIONS.LinkBounds
import YM.Work.F02


/-!
# The leading projection of the unmasked correction

The nonlinear path products are not replaced by their curvature-linear evaluations.
This transition concerns Taylor jets only and uses actual analytic estimates at the
charged path widths. Averaging on reoriented inputs is on the actual formulas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Tensor Joint
open Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

section rays
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E → ℝ}

/-- Vanishing read along rays with sparse lower jets. -/
lemma ray_price (a : E) {k : ℕ} (h : ContDiffAt ℝ k F 0)
    (hg : ∀ i<k, Tensor.coeff F i 0=0) :
    Tendsto (fun t : ℝ => F (t • a)/t^k) (𝓝[≠] 0) (𝓝 (Tensor.diagonal (Tensor.coeff F k 0) a)) := by
  let Q := fun t : ℝ => F (t • a)
  let C := Tensor.diagonal (Tensor.coeff F k 0) a
  have he : ContDiffAt ℝ k Q 0 := by apply ContDiffAt.comp (g:=F) _ _ (contDiffAt_id.smul contDiffAt_const); simpa using h
  obtain ⟨s,hs,ht⟩ := he.contDiffOn (m:=↑k) le_rfl (by simp)
  obtain ⟨ε,hε,hb⟩ := Metric.mem_nhds_iff.mp hs
  let S := Metric.ball (0:ℝ) ε
  have hp : S∈𝓝 0 := Metric.ball_mem_nhds _ hε
  have hx := _root_.taylor_tendsto (convex_ball (0:ℝ) ε) (mem_of_mem_nhds hp) (ht.mono hb)
  rw [nhdsWithin_eq_nhds.mpr hp] at hx
  have hy (i : ℕ) (hi : i≤k) : Tensor.diagonal (Tensor.coeff F i 0) a =
      (Nat.factorial i : ℝ)⁻¹ * iteratedDerivWithin i Q S 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (Metric.isOpen_ball.uniqueDiffOn) (he.of_le (Nat.cast_le.mpr hi)) (mem_of_mem_nhds hp)]
    rw [show iteratedDeriv i Q 0=_ from Next.Foundations.iteratedDeriv_on_line (h.of_le (Nat.cast_le.mpr hi)) a]; rfl
  have hz (t : ℝ) : taylorWithinEval Q k S 0 t=t^k*C := by
    rw [taylor_within_apply]; simp only [smul_eq_mul,sub_zero]
    rw [Finset.sum_eq_single k]
    · unfold C; rw [hy k le_rfl]; ring
    · intro i hi h'
      have ha := Finset.mem_range.mp hi
      have he : i<k := by omega
      rw [mul_comm ((i.factorial:ℝ)⁻¹),mul_assoc,← hy i he.le, hg i he]; exact mul_zero _
    simp
  rw [show Tensor.diagonal (Tensor.coeff F k 0) a=0+C from (zero_add _).symm]
  refine ((hx.mono_left nhdsWithin_le_nhds).add (g:=fun _ => C) tendsto_const_nhds).congr' ?_
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0,t ≠ 0 from self_mem_nhdsWithin] with t hn
  change ((t-0)^k)⁻¹ • (Q t - taylorWithinEval Q k S 0 t)+C=Q t / t^k
  rw [hz t, smul_eq_mul]; field_simp; ring

lemma paid_projection {R : E → ℝ} {n : ℕ} (h : ContDiffAt ℝ n F 0)
    (hR : ∀ a : E, Tendsto (fun t : ℝ => F (t • a)/t^n) (𝓝[≠] 0) (𝓝 (R a))) :
    (∀ i<n, Tensor.coeff F i 0=0) ∧ Tensor.diagonal (Tensor.coeff F n 0)=R := by
  have hc : ∀ i<n, Tensor.coeff F i 0=0 := by
    intro i; induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      obtain ⟨p,hp⟩ : ∃ p,n=i+(p+1) := ⟨n-(i+1),by omega⟩
      have ht : ContDiffAt ℝ i F 0 := h.of_le (Nat.cast_le.mpr hi.le)
      refine Tensor.ext_diag _ _ (Tensor.coeff_symm ht) (fun _ _ => rfl) (funext fun a => ?_)
      have hh : Tendsto (fun t : ℝ => t^(p+1)) (𝓝[≠] 0) (𝓝 (0:ℝ)) := by
        simpa using! ((continuous_id.pow (p+1)).continuousAt (x:=(0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
      have hv := (hR a).mul hh
      rw [mul_zero] at hv
      refine tendsto_nhds_unique (ray_price a ht (fun j hj => ih _ hj (hj.trans hi))) (hv.congr' ?_)
      filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0,t ≠ 0 from self_mem_nhdsWithin] with t ht
      simp [hp,pow_add,div_eq_mul_inv]
      field_simp
  exact ⟨hc, funext fun a => tendsto_nhds_unique (ray_price a h hc) (hR a)⟩
end rays

section path
variable {G : Gauge} {c : Side} {n : ℕ}

def impact (B : ℕ → Atom G n) (a : Dir G c) := Patch.average (fun i : Signed => uncut B (pull i 0 (represent a)))
lemma impact_cont {B : ℕ → Atom G n} {σ C} (h : 0 < σ) (hx : SumBudget (fun k => (B k).budget σ) C) :
    ContDiffAt ℝ ω (impact (c:=c) B) 0 := by
  have he (i : Signed) : ContDiffAt ℝ ω (fun a : Dir G c => uncut B (pull i 0 (represent a))) 0 := by
    simp_rw [← rep_shifts]
    exact (show ContDiffAt ℝ ω (fun a : Dir G c => uncut B (represent a)) ((shifts i (0:Site c)) 0) from
      (map_zero (shifts i (0:Site c))).symm ▸ Work.F02.uncut_contDiffAt h hx
        (fun i => (represent_smooth i).contDiffAt)).comp 0 (shifts i (0:Site c)).contDiff.contDiffAt
  unfold impact Patch.average; exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => he i)

lemma impact_leading {B : ℕ → Atom G n} {σ C} (h : 0 < σ) (hx : SumBudget (fun k => (B k).budget σ) C) :
    let U := impact (c:=c) B
    (∀ i<n, Tensor.coeff U i 0=0) ∧ Tensor.diagonal (Tensor.coeff U n 0) = fun u => Patch.average fun s : Signed =>
      ∑ x : Site c, ∑' i, (B i).poly fun j => faceCurl (slotFace ((B i).leg j) x) (shifts s (0:Site c) u) := by
  intro U; refine paid_projection ((impact_cont h hx).of_le le_top) (fun u => ?_)
  unfold U impact Patch.average
  simp only [mul_div_assoc, Finset.sum_div]; apply Tendsto.const_mul _ (tendsto_finsetSum _ _); intro i _
  simp_rw [← rep_shifts, map_smul]; exact atoms_limit _ _ h hx

lemma coeff_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F L : E → ℝ} {n : ℕ}
    (h : Tensor.coeff F n 0=Tensor.coeff L n 0) : iteratedFDeriv ℝ n F 0=iteratedFDeriv ℝ n L 0 :=
    (smul_right_injective _ (show (Nat.factorial n : ℝ)⁻¹≠0 by positivity)) h
end path
end YM.AnalyticNext.QuarticMatch
