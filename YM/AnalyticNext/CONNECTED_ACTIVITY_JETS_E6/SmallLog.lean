import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rod
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weights

/-!
# Chord patch to linear comparison in logarithmic coordinates

Use `Clean` on V, not global V small; patch axial flatten on larger
bounded stencil with radius proof ( etc.). Materialize a whole
bounded log array agreeing on this hull only, so even computations that
must compare to **uncut** stacks within that orientation can do so at
one torus. Affine variation is in *left* chart; product of logs with
this V costs an additional first-order comparison here (not pretending
the input links are a tangent-space density).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel  Next.Fluctuations Work.E03
open Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

section origin

private def bch (x : G.Color × G.Color) := G.plog (G.mat (G.lieExp x.1*G.lieExp x.2))

private lemma prod_rate (p : G.Color × G.Color) : HasDerivAt (fun v : ℝ => bch (v • p)) (p.1+p.2) 0 := by
  let z (x : G.Color) (v : ℝ) := G.mat (G.lieExp (v • x))
  have he x : HasDerivAt (z x) (G.colorMat x) 0 := by
    unfold z; simp only [G.mat_lieExp,map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
  have hs x : z x 0=1 := by simp [z]
  have hp : HasFDerivAt G.plog (fderiv ℝ G.plog 1) 1 :=
    (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
  have hh x : fderiv ℝ G.plog 1 (G.colorMat x)=x := by
    have ht : HasDerivAt (G.plog ∘ z x) x 0 := by
      have hu : Tendsto (fun v : ℝ => v • x) (𝓝 0) (𝓝 0) := by
        simpa using! (continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)
      apply HasDerivAt.congr_of_eventuallyEq (f:=fun v : ℝ => v • x)
      · simpa using! (hasDerivAt_id (0:ℝ)).smul_const x
      exact hu.eventually G.plog_left
    have hg := (hp.comp_hasDerivAt_of_eq _ (he x) (hs x).symm).unique ht
    exact hg
  suffices hv : HasDerivAt (fun v => z p.1 v * z p.2 v) (G.colorMat (p.1+p.2)) 0 by
    have hf := hp.comp_hasDerivAt_of_eq _ hv (by simp only [hs,mul_one])
    have hf := hf.congr_deriv (hh (p.1+p.2))
    exact hf.congr_of_eventuallyEq (Eventually.of_forall fun v => by
      change G.plog (G.mat (_ * _)) = G.plog _; rw [G.mat_mul]; rfl)
  simpa only [hs,mul_one,one_mul,map_add] using! (he p.1).mul (he p.2)

/-- Product costs only quadratic above the linear sum. -/
private lemma bch_cost (G : Gauge) : ∃ K r : ℝ, 0<K ∧ 0<r ∧ ∀ (p : G.Color × G.Color), ‖p‖ ≤ r →
    G.lieExp (bch p)=G.lieExp p.1*G.lieExp p.2 ∧ ‖bch p - (p.1+p.2)‖ ≤ K*‖p‖^2 ∧ ‖bch p‖ ≤ K*‖p‖ := by
  let f : G.Color × G.Color → G.El := fun x => G.lieExp x.1 * G.lieExp x.2
  have he : f 0=1 := by simp [f]
  have hm : AnalyticAt ℝ (bch (G:=G)) 0 := by
    refine ContDiffAt.analyticAt ?_
    have hv : ContDiffAt ℝ ω (fun x => G.mat (f x)) 0 :=
      (((G.exp_jet.comp contDiff_fst).mul (G.exp_jet.comp contDiff_snd)).contDiffAt)
    exact ContDiffAt.comp (f:=fun x => G.mat (f x)) 0 (by simp only [he,G.mat_one]; exact G.plog_diff) hv
  obtain ⟨K,r,hK,hr,h⟩ := chart_quadratic_cost _ _ hm (fun x => prod_rate x)
  have ht : Tendsto f (𝓝 0) (𝓝 1) := by rw [← he]; exact (show Continuous f by unfold f; fun_prop).tendsto _
  obtain ⟨s,hs,hb⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (ht.eventually G.plog_right)
  refine ⟨K*2,min 1 (min r s), by positivity, lt_min zero_lt_one (lt_min hr hs),fun p he => ?_⟩
  have hv := hb (x:=p) (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (he.trans ((min_le_right ..).trans (min_le_right ..)))))
  have hh := (h p).2 (he.trans ((min_le_right ..).trans (min_le_left ..)))
  rw [show bch (0:G.Color × G.Color)=0 by simp [bch],zero_add] at hh
  refine ⟨hv,hh.trans (by gcongr; exact le_mul_of_one_le_right hK.le (by norm_num)),?_⟩
  have hy : ‖bch p‖ ≤ ‖bch p-(p.1+p.2)‖+‖p.1+p.2‖ := by
    simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (bch p) (p.1+p.2) 0
  apply (hy.trans (add_le_add hh (h p).1)).trans
  have he : ‖p‖ ≤ 1 := he.trans (min_le_left ..)
  nlinarith [mul_nonneg hK.le (mul_nonneg (norm_nonneg p) (show 0 ≤ 1-‖p‖ by linarith))]

lemma chart_bias (G : Gauge) : ∃ K r : ℝ, 0<K ∧ 0<r ∧ ∀ {n : Side} (X Y : Directions G n) (h : ℝ),
    ‖X‖ ≤ h → ‖Y‖ ≤ h → h≤r → ∃ z : Directions G n,
      increment (increment 1 Y) X=represent (toLog z) ∧ ‖z - (X+Y)‖ ≤ K*h^2 ∧ ‖z‖ ≤ K*h := by
  obtain ⟨K,r,hK,hr,h⟩ := bch_cost G
  refine ⟨K,r,hK,hr,?_⟩
  intro n X Y t ht hu hv
  let z i := bch (X i,Y i)
  have hk i : ‖(X i,Y i)‖ ≤ t := max_le ((norm_le_pi_norm X i).trans ht) ((norm_le_pi_norm Y i).trans hu)
  have hh i := h _ ((hk i).trans hv)
  have he : 0 ≤ t := (norm_nonneg _).trans ht
  refine ⟨z,?_, (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    (fun i => (hh i).2.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hk i) 2) hK.le)),
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => (hh i).2.2.trans (by gcongr; exact hk i))⟩
  rw [represent, collects]; funext i
  simp only [increment, Pi.one_apply,mul_one,z, (hh _).1]
end origin

lemma flattening (P : Teller G) (L : Side) : ∃ H : ℝ → ℝ, Rate G L (-(1/2)) H ∧
    ∀ᶠ x : ℝ in atTop, 0 ≤ H x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → Room P S T x →
    ∀ V : Config G c, ∀ (o : Site c) (d : ℕ), d ≤ 32 * radiusB x → Clean V x o (d+1) →
    ∃ (z : Site c → G.El) (b : LogField G c), AgreeNear id o d (gauge z V) (represent b) ∧ ‖b‖ ≤ H x := by
  obtain ⟨C,r,hC,hr,hk⟩ := extend_interior G
  let F x := 32*radiusB x+1
  let u x := 16*(2*(F x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have he : Rate G L (-(1/2)) u := by
    have h := ((((((Rate.transfers (G:=G) (L:=L) 32 1).mul_left 2).add (Rate.const 1)).pow 5).mul_left 16).mul_right
      (Fintype.card PlaqAxes:ℝ)).mul (Rate.flame.mul_left 2)
    simpa only [F,u,zero_mul,zero_add] using! h
  refine ⟨_, he.mul_left C, ?_⟩
  filter_upwards [he.below (by norm_num) _ hr, Delay.shift_pos G L] with x hx hy
  have h0 : 0 ≤ u x := by have hs : 0 < Pressure.fiery G x L := Work.E09.temp_pos hy; unfold u; positivity
  refine ⟨mul_nonneg hC.le h0,?_⟩
  intro c f S T hL hR V o d hd h
  have hv : 0 ≤ Pressure.temp x := by unfold Pressure.temp; positivity
  obtain ⟨z,hz⟩ := Work.E08.axial_patch o V d (d+1) le_rfl (by have hh := hR.buys; omega) _ hv
    (fun i hi j => h.toll (b := (i,j)) hi)
  have hb : ∀ i : Bond c, separation o i.1 ≤ d → G.chord (gauge z V i)≤u x := by
    intro i hi; apply (hz i hi).trans
    unfold u; gcongr
    · unfold F; omega
    · simpa only [hL] using! hR.temperatures
  obtain ⟨b,hy,hx⟩ := hk id o d (gauge z V) _ h0 ((le_abs_self _).trans hx) hb
  exact ⟨z,b,hx,hy⟩
end YM.ConnectedActivityE6.SliceRows
