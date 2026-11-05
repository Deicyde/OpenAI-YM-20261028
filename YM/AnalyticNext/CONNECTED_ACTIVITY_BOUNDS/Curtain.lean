import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Odometer

/-!
# Enter a proved linear patch after dropping the other masks

Real relative exponential coordinates. Use BCH only on the queried Lie
balls, independent of orientation and global image. Field may leave the
input sector elsewhere. Tree/frame gauges chosen separately at each
query: do not spend cancellations across queries in different gauges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def together (G : Gauge) (x : G.Color × G.Color) := G.plog (G.mat (G.lieExp x.1 * G.lieExp x.2))

theorem together_cost (G : Gauge) : ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ x : G.Color × G.Color, ‖x‖≤r →
    G.lieExp (together G x) = G.lieExp x.1 * G.lieExp x.2 ∧ ‖together G x‖ ≤ C*‖x‖ ∧
      ‖together G x-(x.1+x.2)‖ ≤ C*‖x‖^2 := by
  let Y := G.Color × G.Color
  have hm : ContDiff ℝ ω fun x : Y => G.mat (G.lieExp x.1 * G.lieExp x.2) := by
    simp only [G.mat_mul]; exact (G.exp_jet.comp contDiff_fst).mul (G.exp_jet.comp contDiff_snd)
  have ht : AnalyticAt ℝ (together G) 0 := by
    apply ContDiffAt.analyticAt
    apply ContDiffAt.comp (f:=fun x : Y => _) _ _ hm.contDiffAt
    convert! G.plog_diff using 1; simp
  let L (p : Y) := p.1+p.2
  have he : ∀ᶠ x : Y in nhds 0, G.lieExp (together G x) = G.lieExp x.1 * G.lieExp x.2 := by
    have hh : Continuous fun x : G.Color×G.Color => G.lieExp x.1 * G.lieExp x.2 := by fun_prop
    have hh := hh.tendsto 0; simp only [Prod.fst_zero,Prod.snd_zero,G.mat_lieExp_zero,mul_one] at hh
    exact hh.eventually G.plog_right
  have hz : together G 0 = 0 := by simp [together]
  have hJ a : HasDerivAt (fun t : ℝ => together G (t • a)) (L a) 0 := by
    let f (t : ℝ) := together G (t • a)
    have hD := Push.side (together G) ht.differentiableAt a
    let x := deriv f 0
    have hf : HasDerivAt f x 0 := hD.differentiableAt.hasDerivAt
    have h0 : f 0=0 := by rw [show f 0=together G _ from rfl,zero_smul,hz]
    have hg : HasFDerivAt (fun a => G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap (f 0) := h0.symm ▸ G.expDiff_zero
    have hC : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (f t))) (G.colorMat x) 0 := hg.comp_hasDerivAt (0:ℝ) hf
    have hc : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • a.1)) * G.mat (G.lieExp (t • a.2))) (G.colorMat x) 0 := by
      apply hC.congr_of_eventuallyEq
      have hy : Tendsto (fun t : ℝ => t • a) (nhds 0) (nhds 0) := by simpa using! (show Continuous (fun t : ℝ => t • a) by fun_prop).tendsto (0:ℝ)
      filter_upwards [hy.eventually he] with t hh; unfold f; rw [hh,G.mat_mul]; rfl
    have hs (a : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • a))) (G.colorMat a) 0 := by
      simp only [G.mat_lieExp, map_smul]
      simpa using! hasDerivAt_exp_smul_const (G.colorMat a) (0:ℝ)
    apply hf.congr_deriv; apply G.colorMat_injective
    simpa only [Pi.mul_def,zero_smul, G.mat_lieExp_zero,G.mat_one,one_mul,mul_one,L,map_add] using!
      hc.unique ((hs a.1).mul (hs a.2))
  obtain ⟨C,r,hC,hr,H⟩ := chart_quadratic_cost (together G) L ht hJ
  obtain ⟨D,s,hD,hs,h⟩ := chart_linear_cost _ _ ht
  obtain ⟨u,hu,hb⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 he
  refine ⟨max C D,min (min r s) u,hC.trans_le (le_max_left ..),lt_min (lt_min hr hs) hu,?_⟩
  intro x hh
  obtain ⟨hh,hp⟩ := le_min_iff.mp hh
  obtain ⟨hx,hv⟩ := le_min_iff.mp hh
  have ht : ‖together G x‖ ≤ D*‖x‖ := by simpa [hz] using h x (by simpa using hv)
  have he : ‖together G x-L x‖ ≤ C*‖x‖^2 := by simpa [hz] using (H x).2 hx
  exact ⟨hb (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])),ht.trans (by gcongr; exact le_max_right ..), he.trans (by gcongr; exact le_max_left ..)⟩

lemma pressing (G : Gauge) (D : Patch) (p : ℕ) : ∀ᶠ x : ℝ in atTop, ∀ (n : Side) (a : Directions G n)
    (b : LogField G n), let r := allowance G D x 1 p
    (∀ i, ‖a i‖≤r) → ‖b‖≤r → ∃ s : LogField G n,
    increment (represent b) a=represent s ∧ ‖s‖≤allowance G D x 1 (p+1) ∧
      ‖s-(b+form a)‖≤allowance G D x 2 (p+p+1) := by
  obtain ⟨C,r,hC,hr,h⟩ := together_cost G
  filter_upwards [(vanishes G D p).eventually (ge_mem_nhds hr),grow G D C (by omega : p<p+1) 1,
    grow G D C (by omega : p+p<p+p+1) 2] with x hx he ht n a b Z ha hb
  let y (i : Body 1 n) := (form a i,b i)
  let t i := together G (y i)
  have hp i : ‖y i‖ ≤ Z := max_le (ha _) ((norm_le_pi_norm b i).trans hb)
  have hu i := h (y i) ((hp i).trans hx)
  refine ⟨t,?_,(pi_norm_le_iff_of_nonneg (allowance_nn ..)).mpr (fun i =>
    (hu i).2.1.trans ((mul_le_mul_of_nonneg_left (hp i) hC.le).trans he)),?_⟩
  · funext i; change G.lieExp (a i) * (G.lieExp (b (pole i))*1) = G.lieExp (t (pole i))*1; rw [(hu _).1]; simp only [mul_one]
    rw [show (y (pole i)).1=a i from congr_fun (collect_form ..) i]
  apply (pi_norm_le_iff_of_nonneg (allowance_nn ..)).mpr; intro i
  change ‖t i-(b i+form a i)‖ ≤ _; rw [add_comm]
  apply (hu i).2.2.trans
  have hv := pow_le_pow_left₀ (norm_nonneg _) (hp i) 2
  apply le_trans (mul_le_mul_of_nonneg_left hv hC.le)
  unfold Z; rw [pow_two, Rates.exchange]; exact ht

lemma increment_gauge (U : Config G n) (s : Directions G n) (z : Site n→G.El) :
    gauge z (increment U s) = increment (gauge z U) (rotateG s z) := by
  funext i; unfold Lattice.gauge increment rotateG; rw [exp_adjoint]; group

lemma shadows (b : LogField G c) {z : Site c→G.El} {W : Config G c} {U : Config G f} {R} {y : Site c} (a v : Directions G f)
    (he : AgreeNear id y R (gauge z W) (represent b)) (hp : AgreeNear S.ratio.parent y R U (increment (replica S.ratio W) a))
    (hv : ∀ i : Bond f, separation y (home S i) ≤ R → rotateG a (z ∘ S.ratio.parent) i = v i) :
    AgreeNear S.ratio.parent y R (gauge (z∘S.ratio.parent) U) (increment (replica S.ratio (represent b)) v) := by
  intro i hi
  let t := z ∘ S.ratio.parent; let Y := replica S.ratio W
  rw [show gauge (z∘S.ratio.parent) U i = gauge t (increment Y a) i from by simp only [t,Lattice.gauge,hp i hi]; rfl,
    increment_gauge, show gauge t Y = replica S.ratio (gauge z W) from copied S.ratio S.patch.odd_side ..] -- rw hv through increment?
  unfold increment; unfold t; rw [hv i hi,shares_copy S he i hi]
end YM.AnalyticNext.ConnectedActivity.Aff
