import YM.SectorNext.VACUUM_NORMALIZATION.Laplace
import YM.Work.B06


/-!
# Pay per real link at its dimension ( and )

LocalRatio production is pre-L and the only chart used. Retains powers
of sqrt beta, no promoting a fixed-scale delay to a uniform-in-j statement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Precision MeasureTheory Metric
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations
variable {G : Gauge}
local notation "Δ" => Module.finrank ℝ G.Color
abbrev air (G : Gauge) := (volume (α:=G.Color)).real (Metric.ball 0 1)
lemma air_pos : 0<air G := ENNReal.toReal_pos (by exact (Measure.IsOpenPosMeasure.open_pos (Metric.ball (0:G.Color) 1) Metric.isOpen_ball (Metric.nonempty_ball.mpr zero_lt_one))) (measure_ball_lt_top.ne)

theorem shell_lower (A : ChartRatio G) (h : LocalRatio A) : ∃ r c : ℝ, 0<r ∧ 0<c ∧ ∀ s,0<s → s≤r →
    c*s^Δ ≤ G.probHaar.real (G.shell s) := by
  obtain ⟨B,r,hB,hr,hh⟩ := chord_chart_cost G
  obtain ⟨u,hu,he⟩ := Metric.nhds_basis_closedBall.eventually_iff.1
    ((h.germ 0 (Metric.mem_ball_self h.patch)).continuousAt.eventually
      (lt_mem_nhds (show (1/2:ℝ)< A.J 0 by rw [h.anchored]; norm_num)))
  let k := A.scale*(1/2)
  have hk : 0<k := mul_pos h.scale (by norm_num)
  let m := min r (min u (A.radius/2))
  have hm : 0<m := lt_min hr (lt_min hu (half_pos h.patch))
  refine ⟨B*m,k*air G/B^Δ,mul_pos hB hm,div_pos (mul_pos hk air_pos) (pow_pos hB _),?_⟩
  intro s h0 hs
  let v := s/B
  have hv : 0<v := div_pos h0 hB
  have hU : v ≤ m := (div_le_iff₀ hB).mpr (by linarith only [hs])
  have hv' : v < A.radius := lt_of_le_of_lt (hU.trans (le_trans (min_le_right ..) (min_le_right ..))) (half_lt_self h.patch)
  let T := closedBall (0:G.Color) v
  let Y := G.lieExp '' T
  have hT : MeasurableSet Y := ((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet
  have hy : G.probHaar.real Y = ∫ x in T, (A.scale*A.J x) := by simpa [T,Y] using kernel_integral A h hv' (fun _=>1) measurable_const
  have hl {x : G.Color} (hx : x∈T) : ‖x‖≤v := by simpa [T] using hx
  have hp {x : G.Color} (hx : x∈ T) : 1/2 ≤ A.J x := (show (1/2:ℝ)< A.J x from he (x:=x) (mem_closedBall.mpr (by
    rw [dist_zero_right]; apply (hl hx).trans
    exact hU.trans (le_trans (min_le_right ..) (min_le_left ..))))).le
  have hI : IntegrableOn (fun x : G.Color=> A.scale*A.J x) T volume :=
    ContinuousOn.integrableOn_compact (ProperSpace.isCompact_closedBall ..) fun x hx=> continuousWithinAt_const.mul ((h.germ x (by
      apply mem_ball.mpr; rw [dist_zero_right]; exact (hl hx).trans_lt hv')).continuousAt.continuousWithinAt)
  have hi : k*volume.real T ≤ G.probHaar.real Y := by
    have hμ : volume (α:=G.Color) T≠⊤ := (ProperSpace.isCompact_closedBall ..).measure_lt_top.ne
    have hg := setIntegral_mono_on (μ:=volume) (s:=T) (f:=fun _=>k) (integrableOn_const hμ) hI isClosed_closedBall.measurableSet (fun x hx=>mul_le_mul_of_nonneg_left (hp hx) h.scale.le)
    rwa [← hy,setIntegral_const,smul_eq_mul,mul_comm] at hg
  have hN : (volume (α:=G.Color)).real T=v^Δ*air G := by
    unfold Measure.real air
    rw [Measure.addHaar_closedBall volume _ hv.le,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
    rfl
  apply le_trans _ (hN ▸ hi.trans (measureReal_mono (μ:=G.probHaar) (s₁:=Y) (s₂:=G.shell s) (by
    rintro x ⟨w,hw,rfl⟩
    apply (hh _ ((hl hw).trans (hU.trans (min_le_left ..)))).trans; apply (mul_le_mul_of_nonneg_left (hl hw) hB.le).trans_eq
    unfold v; field_simp)))
  unfold v; apply le_of_eq; rw [div_pow]; ring

def draught (c : ℝ) (u : G.El) := Real.exp (-c*G.chord u)

-- finite constant for Japanese bracket majorization
private lemma relax {b : ℝ} (hb : 0 < b) (d : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ x≥0, x^d*Real.exp (-b*x) ≤ C := by
  have ht : Tendsto (fun x : ℝ=> x^d*Real.exp (-b*x)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp (tendsto_id.const_mul_atTop hb)
    have he : (fun x : ℝ=> x^d*Real.exp (-b*x)) = fun x=> (b^d)⁻¹*((b*x)^d*Real.exp (-(b*x))) := by funext x; rw [neg_mul,mul_pow]; field_simp
    rw [he]; simpa [Function.comp_def] using h.const_mul ((b^d)⁻¹)
  obtain ⟨u,hu⟩ := eventually_atTop.mp (ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)))
  refine ⟨(1+|u|)^d, pow_pos (by linarith [abs_nonneg u]) _,fun x hx=> ?_⟩
  by_cases h : u ≤ x
  · exact le_trans (hu x h) (one_le_pow₀ (by linarith [abs_nonneg u]))
  apply le_trans (mul_le_of_le_one_right (pow_nonneg hx _) (Real.exp_le_one_iff.mpr (by nlinarith)))
  exact pow_le_pow_left₀ hx (le_trans (le_of_not_ge h) (by linarith [le_abs_self u])) _

lemma flowing (b : ℝ) (hb : 0<b) : Integrable (fun x : G.Color=> Real.exp (-b*‖x‖)) volume := by
  let d := Δ+1
  obtain ⟨C,hC,hh⟩ := relax hb d
  have hi := (integrable_one_add_norm (show (Δ:ℝ)< d by unfold d; simp) (μ:= (volume (α:=G.Color)))).const_mul (C*Real.exp b)
  apply hi.mono' (by fun_prop)
  refine Eventually.of_forall fun i=> ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg (by positivity),Real.rpow_natCast, ← div_eq_mul_inv,le_div_iff₀ (by positivity)]
  have hk := mul_le_mul_of_nonneg_right (hh (1+‖i‖) (by positivity)) (Real.exp_pos b).le
  rw [mul_assoc,←Real.exp_add,show -b*(1+‖i‖)+b= -b*‖i‖ by ring] at hk
  linarith only [hk]

/-- Rates with t=sqrt β, even before dosing. -/
theorem chord_z (A : ChartRatio G) (H : LocalRatio A) (b : ℝ) (hb : 0<b) : ∃ L : ℝ,0<L ∧ ∀ t,1≤t →
    t^Δ * (∫ x,draught (t*b) x ∂G.probHaar) ≤ L := by
  obtain ⟨r,ε,D,hr,hl,he,hD,hv,hy⟩ := kernel_ball A H
  obtain ⟨k,hk,hh⟩ := relax (show 0<b*ε from mul_pos hb he) Δ
  let F := fun x : G.Color=> 2*A.scale * Real.exp (-(b/2)*‖x‖)
  let B := closedBall (0:G.Color) r
  let Y := G.lieExp '' B
  have hF : Integrable F := (flowing (b/2) (half_pos hb)).const_mul _
  have hN : 0 ≤ ∫ x,F x := integral_nonneg fun x=> by unfold F; have := H.scale; positivity
  refine ⟨(∫ x,F x)+k,by linarith,fun t ht=> ?_⟩
  have ht0 : 0<t := by linarith
  let f := draught (G:=G) (t*b)
  have hf : Continuous f := by unfold f draught; fun_prop
  have hg := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ:=G.probHaar)
  have hY : MeasurableSet Y := ((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  change t^_*(∫ x,f x ∂G.probHaar) ≤ _
  rw [← integral_add_compl hY hg,mul_add]
  apply add_le_add
  · rw [kernel_integral A H hl f hf.measurable,← integral_indicator hB (μ:=volume),← smul_eq_mul,
      ← Measure.integral_comp_inv_smul_of_nonneg volume _ ht0.le]
    let W := B.indicator (fun x : G.Color=> A.scale*A.J x*f (G.lieExp x))
    have hW : Measurable W := (((measurable_const.mul H.borel).mul (hf.comp G.lieExp_cont).measurable).indicator hB)
    let g := fun x : G.Color=> W (t⁻¹ • x)
    have hm x : ‖g x‖ ≤ F x := by
      let y := t⁻¹ • x
      change ‖W y‖ ≤ F x; unfold W; by_cases hr : y∈B
      · rw [indicator_of_mem hr]; obtain ⟨hh,h1,h2,h3⟩ := hv y (by simpa [B] using hr)
        have hx : t*‖y‖=‖x‖ := by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht0).le]; field_simp
        have hμ : f (G.lieExp y) ≤ Real.exp (-(b/2)*‖x‖) := Real.exp_le_exp.mpr (by
          have := mul_le_mul_of_nonneg_left h2 (show 0≤t*b by positivity)
          nlinarith only [this,mul_le_mul_of_nonneg_left (le_of_eq hx.symm) hb.le] -- need b*hx
          )
        have hh' := H.scale
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hh'.le hh) (show 0≤f (G.lieExp y) from (Real.exp_pos _).le))]
        exact mul_le_mul (by linarith only [mul_le_mul_of_nonneg_left h1 hh'.le]) hμ (Real.exp_pos _).le (by positivity)
      rw [indicator_of_notMem hr,norm_zero]; unfold F; have := H.scale; positivity
    have hM : Measurable g := hW.comp (show Continuous (fun x : G.Color=> t⁻¹ • x) by fun_prop).measurable
    exact integral_mono (hF.mono' hM.aestronglyMeasurable (Eventually.of_forall hm)) hF fun x=> (le_abs_self (g x)).trans (hm x)
  apply le_trans _ (hh t ht0.le)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hW (x : G.El) (hx : x∈Yᶜ) : f x ≤ Real.exp (-(b*ε)*t) := by
    apply Real.exp_le_exp.mpr
    have hu := G.chord_le_two x; have hκ := hy x hx
    have ht : ε ≤ G.chord x := by nlinarith [G.chord_price x,G.chord_nonneg x]
    nlinarith only [mul_le_mul_of_nonneg_left ht (show 0≤t*b by positivity)]
  apply (setIntegral_mono_on hg.integrableOn integrableOn_const (MeasurableSet.compl hY) hW).trans; rw [setIntegral_const,smul_eq_mul]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (measureReal_le_one ..)

end YM.SectorNext.Vacuum
