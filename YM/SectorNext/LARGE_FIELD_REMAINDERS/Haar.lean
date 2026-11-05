import YM.Next.FLUCTUATIONS.Charts
import YM.Next.FOUNDATIONS.Primary
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Upper bound on the true small-scale Haar mass

d0 ambient estimates would generally get the wrong power here. Work in the actual
log/small-patch convention on physical G, from Foundations & Fluctuations, and
do NOT put Lebesgue on the rest of the frozen positions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations  Scales Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ENNReal

variable (G : Gauge)

def dim := Module.finrank ℝ G.Color

private lemma chol : ∃ (D δ : ℝ), 0 < D ∧ 0 < δ ∧ ∀ r : ℝ, 0<r → r < δ →
    G.probHaar.real (G.shell r) ≤ D*r^dim G := by
  obtain ⟨C,R,hC,hR,H⟩ := log_chart_cost G
  let X := Next.Foundations.chart G
  have hX := Next.Foundations.chart_ok G
  let K := Metric.ball (0:G.Color) X.radius
  let V := G.lieExp '' K
  have h0 : (0:G.Color)∈K := mem_ball_self hX.patch
  have hJ : ∀ᶠ x in 𝓝 (0:G.Color), X.J x < 2 :=
    ((hX.germ 0 h0).continuousAt.tendsto).eventually (gt_mem_nhds (by rw [hX.anchored]; norm_num))
  obtain ⟨e,he,he'⟩ := Metric.nhds_basis_ball.eventually_iff.mp hJ
  let δ := min R (min X.radius e/C) -- precedence: min X.radius e / C
  have hk := hX.patch
  change 0<X.radius at hk
  have he : 0<e := he
  have hd : 0<δ := lt_min hR (div_pos (lt_min hk he) hC)
  have hS : 0<X.scale := hX.scale
  let E0 := Metric.ball (0:G.Color) 1
  let D := X.scale*2*((2*C)^dim G * volume.real E0)
  have hvol : 0 ≤ volume.real E0 := ENNReal.toReal_nonneg
  have hD : 0≤D := by unfold D; positivity
  refine ⟨D+1,δ,by linarith, hd,fun r hr hL => ?_⟩
  have hp : C*r < min X.radius e := by rw [mul_comm]; exact (lt_div_iff₀ hC).mp (hL.trans_le (min_le_right ..))
  have hp1 := hp.trans_le (min_le_left ..); have hp2 := hp.trans_le (min_le_right ..)
  have hv (u : G.El) (h : u ∈ G.shell r) :
      G.lieExp (G.plog (G.mat u))=u ∧ ‖G.plog (G.mat u)‖ ≤ C*r := by
    obtain ⟨ha,hb⟩ := H u (le_trans h (hL.trans_le (min_le_left ..)).le)
    exact ⟨ha,hb.trans (mul_le_mul_of_nonneg_left h hC.le)⟩
  let B := G.lieExp ⁻¹' (G.shell r) ∩ K
  have hm : MeasurableSet B := ((G.lieExp_cont.measurable) (G.shell_meas _)).inter Metric.isOpen_ball.measurableSet
  have hh1 (z : G.Color) (h : z ∈ B) : ‖z‖ ≤ C*r := by
    obtain ⟨ha,hb⟩ := hv (G.lieExp z) h.1
    have he : G.plog (G.mat (G.lieExp z))∈ K := by rw [mem_ball_zero_iff]; exact hb.trans_lt hp1
    rwa [hX.inject he h.2 ha] at hb
  have hb : G.shell r ⊆ V := fun i hi => by
    obtain ⟨ha,hb⟩ := hv i hi
    refine ⟨_,?_,ha⟩; rw [mem_ball_zero_iff]; exact hb.trans_lt hp1
  have hEq : G.probHaar (G.shell r) = ∫⁻ z in B, ENNReal.ofReal (X.scale*X.J z) := by
    nth_rw 1 [← Set.inter_eq_self_of_subset_left hb, ← Measure.restrict_apply (G.shell_meas r)]
    change G.probHaar.restrict (G.lieExp '' (ball 0 X.radius)) (G.shell r) = _
    have h := G.lieExp_cont.measurable
    rw [← hX.actual,Measure.map_apply h (G.shell_meas _), withDensity_apply _ (h (G.shell_meas _)),
      Measure.restrict_restrict (h (G.shell_meas _))]
  have hpos : 0<2*C*r := by positivity
  have hbound : G.probHaar (G.shell r) ≤ ENNReal.ofReal (X.scale*2)*
      (ENNReal.ofReal ((2*C*r)^dim G)*volume E0) := by
    rw [hEq]
    apply (setLIntegral_mono' hm (g:=fun _ => ENNReal.ofReal (X.scale*2)) _).trans
    · rw [setLIntegral_const]; unfold dim E0; rw [← Measure.addHaar_ball_of_pos volume (0:G.Color) hpos]
      gcongr _ * ?_; apply measure_mono
      intro u hu; rw [mem_ball_zero_iff]
      apply (hh1 u hu).trans_lt
      have h : 0<C*r := by positivity
      linarith
    intro a ha
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (he' ?_).le hS.le)
    rw [mem_ball_zero_iff]; exact (hh1 a ha).trans_lt hp2
  have hm' : volume E0 < ⊤ := measure_ball_lt_top
  have hh := ENNReal.toReal_mono (show ENNReal.ofReal (X.scale*2)*
      (ENNReal.ofReal ((2*C*r)^dim G)*volume E0) ≠ ⊤ from by finiteness) hbound
  rw [← measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_mul, ← measureReal_def,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hh
  refine hh.trans ?_
  unfold D; rw [mul_pow (2*C) r,add_mul]
  have hnn : 0 ≤ r^dim G := by positivity
  linarith only [hnn]

/-- s>0 only (sufficient also for Gaussian annuli); includes finite or disconnected
G, d possibly zero outside `Simple`. -/
lemma shell_billed : ∃ D : ℝ, 0<D ∧ ∀ s : ℝ, 0<s → G.probHaar.real (G.shell s) ≤ D*s^dim G := by
  obtain ⟨D,δ,hD,hδ,h⟩ := chol G
  refine ⟨max D ((δ^dim G)⁻¹),hD.trans_le (le_max_left ..),fun s hs => ?_⟩
  by_cases hx : s < δ
  · exact (h s hs hx).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
  have he : G.probHaar.real (G.shell s) ≤ 1 := (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)
  refine he.trans (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)))
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr (by rw [one_mul]; gcongr; linarith)
end YM.SectorNext.Remainder
