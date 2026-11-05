import YM.Hilbert.Kolmogorov
import YM.Paley.Line

/-!
# Uniqueness from continuous bottom values. Doesn't apply to distributional
values; separate reconstruction ticket.

For bounded holomorphic families, only need inverse Gaussian one variable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Paley
open Function Set Filter MeasureTheory Measure Complex Analysis 
open scoped Topology InnerProductSpace ComplexOrder ContDiff
variable {C D : ℝ} {F G : ℂ → ℂ}

lemma empty (h : Air F C) (hp : ∀ i : ℝ, F i=0) (p : ℂ) (he : p∈ high) : F p=0 := by
  let x := p.re; let s := p.im
  have hs : 0 ≤ s := he
  have hy : Z s x=p := re_add_im _
  -- Shift real input x; preserves Air. Integrate at s with b=-2ε*s
  let g (z : ℂ) := F (z+x)
  have hh : Air g C := {
    connects := h.connects.comp (continuous_id.add continuous_const).continuousOn fun z (hz : 0≤z.im) =>
      show _ from by change 0 ≤ (_+_ : ℂ).im; simpa using hz
    straight := h.straight.comp ((differentiable_id.add_const _).differentiableOn)
      fun z (hz : 0<z.im) => show _ from by change _ < (_+_ : ℂ).im; simpa using hz
    bounded z hz := h.bounded _ (show _ from by change 0 ≤ (z+↑x).im; simpa using (show 0 ≤ z.im from hz)) }
  have H (ε : ℝ) (hE : 0 < ε) : (∫ t : ℝ, ((↑(Real.exp (-ε*t^2))):ℂ)* g (Z s t))=0 := by
    have he := same hh s (-2*ε*s) ε hs hE
    have hu t : g (Z 0 t)=0 := by simp_rw [g,gap_zero, ← ofReal_add,hp]
    have hz t : probe (-2*ε*s) ε (Z s t) = (↑(Real.exp (-(ε*s^2))):ℂ)* (↑(Real.exp (-ε*t^2)):ℂ) := by
      rw [probe, ofReal_exp,ofReal_exp,← Complex.exp_add]; congr 1
      unfold Z; push_cast; ring_nf; simp [I_sq]
    simp_rw [hu,hz,zero_mul,integral_zero, mul_left_comm (g _),mul_comm (g _),integral_const_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (Complex.ofReal_ne_zero.mpr (by positivity)
      )
  -- scale u = ε t, integrate ε²
  have he (R : ℝ) (hr : 0 < R) : (∫ u : ℝ, ((↑(Real.exp (-u^2))):ℂ)*g (Z s (R*u)))=0 := by
    have hv := H (R⁻¹^2) (by positivity)
    let f (u : ℝ) := (↑(Real.exp (-R⁻¹^2*u^2)):ℂ)*g (Z s u)
    have hW u : R⁻¹^2*((R*u)^2)=u^2 := by field_simp
    suffices hh : (∫ u : ℝ, f (R*u))=0 from by
      simpa only [f,neg_mul,hW] using hh
    change (∫ u, f (R • u))=0
    rw [Measure.integral_comp_smul volume f R, show (∫ x, f x)=0 from hv, smul_zero]
  have hw : Tendsto (fun R : ℝ => (∫ u : ℝ, ((↑(Real.exp (-u^2))):ℂ)*g (Z s (R*u)))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.mono (show ∀ᶠ i : ℝ in 𝓝[>] (0:ℝ), 0 < i from self_mem_nhdsWithin) (fun i hi => (he i hi).symm))
  let v (u : ℝ) := Real.exp (-u^2)
  have hq := ((hh.cont s hs).continuousAt (x := 0)).tendsto
  have ht : Tendsto (fun R : ℝ => (∫ u : ℝ, (v u:ℂ)*g (Z s (R*u)))) (𝓝[>] 0) (𝓝 (∫ u : ℝ, (v u:ℂ)*g (Z s 0))) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun u => v u*C)
    · exact Eventually.of_forall fun i => (show Continuous fun u : ℝ => ((v u:ℂ)*g (Z s (i*u))) from
        (show Continuous (fun u : ℝ => (v u:ℂ)) from by unfold v;fun_prop).mul ((hh.cont s hs).comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · refine Eventually.of_forall fun i => ae_of_all _ fun u => ?_
      have hz := hh.bounded (Z s (i*u)) (show _ from by simp [high,hs])
      change ‖(v u:ℂ)*_‖ ≤ _
      rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ v u from Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    · suffices he : Integrable v from he.mul_const _; simpa [v] using integrable_exp_neg_mul_sq (show 0 < (1:ℝ) by norm_num)
    apply ae_of_all; intro u
    have hh : Tendsto (fun i : ℝ => i*u) (𝓝[>] 0) (𝓝 0) := by
      simpa only [id_eq,zero_mul] using ((continuous_id.mul_const u).continuousAt (x := (0:ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
    exact tendsto_const_nhds.mul (hq.comp hh)
  have he := tendsto_nhds_unique ht hw
  rw [integral_mul_const,integral_complex_ofReal, show (∫ u, v u)=√Real.pi from by
    simpa [v] using integral_gaussian (1:ℝ)] at he
  suffices hs : g (Z s 0)=F p by rw [hs] at he; exact (mul_eq_zero.mp he).resolve_left (ofReal_ne_zero.mpr (by positivity))
  unfold g; rw [← hy]
  congr 1; simp [Z]; ring

lemma along_edge (h : Air F C) (g : Air G D) (hp : ∀ i : ℝ, F i= G i) : EqOn F G high := by
  intro p hv
  have he : Air (F-G) (C+D) := ⟨h.connects.sub g.connects,h.straight.sub g.straight,fun x hx => (norm_sub_le (F x) (G x)).trans
    (add_le_add (h.bounded _ hx) (g.bounded _ hx))⟩
  exact sub_eq_zero.mp (empty he (fun i => by simp [hp]) p hv)
end YM.Paley
