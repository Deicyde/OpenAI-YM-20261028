import YM.Extra.FREE_DETECTOR_ALGEBRA.ProbeWeight
import YM.Further.THRESHOLD_SOURCE_RESTART.Glint
import YM.MergeProof.West.Ozone
import YM.UVNext.PHASE_COARSE_ERROR.Stations
-- following YM.Next.UV_STRESS.Plateau with `zone` replacing shell estimates
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb Work.A01 Work.A05
open YM.Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {W : DiffPlan S} {d n : ℕ}
private def capB : ContDiffBump (0 : E4) := ⟨(1:ℝ)/2,1,by norm_num,by norm_num⟩
private lemma stretch_window (x : Points (n+1)) (he : x 0=0) (r : ℝ) (hr : 0 < r) (hp : ∀ i : Fin n, r < ‖x i.succ‖) :
    Window x (stretch r capB) := by
  have hh : Window (r⁻¹ • x) capB := by
    refine ⟨capB.contDiff,capB.hasCompactSupport,?_,?_⟩
    · rw [PiLp.smul_apply,he,smul_zero]; exact capB.eventuallyEq_one
    intro i hx; rw [capB.tsupport_eq,Metric.mem_closedBall,dist_zero_right, PiLp.smul_apply,norm_smul,
      Real.norm_of_nonneg (inv_pos.mpr hr).le] at hx
    have ht : ‖x i.succ‖ ≤ r := calc
      _ = r * (r⁻¹ * ‖x i.succ‖) := (mul_inv_cancel_left₀ hr.ne' _).symm
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hx hr.le
      _ = _ := mul_one _
    exact not_lt_of_ge ht (hp i)
  simpa only [smul_inv_smul₀ hr.ne'] using window_stretch hr hh

private theorem within_cap (i : Axis) (r : ℝ) (hr : 0 < r) (y : E4) (hp : Analysis.D (basis i) capB y ≠ 0) :
    r • y ∈ annulus r := by
  have he : y∈tsupport capB := tsupport_fderiv_apply_subset ℝ _ (subset_closure hp)
  have hY : 1/2 ≤ ‖y‖ := by
    by_contra! hh
    have hv : capB =ᶠ[𝓝 y] (fun _ => 1) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show y∈ Metric.ball 0 capB.rIn by
        rw [Metric.mem_ball,dist_zero_right]; exact hh)] with x hx
      exact capB.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    exact hp (by rw [Analysis.D,hv.fderiv_eq]; simp)
  rw [capB.tsupport_eq,Metric.mem_closedBall,dist_zero_right] at he; change ‖y‖ ≤ 1 at he
  change r/4<‖r • y‖ ∧ ‖r • y‖ < 2*r
  rw [norm_smul,Real.norm_of_nonneg hr.le]; constructor <;> nlinarith

section pay
variable {G : Gauge} {C : Family G} {S : Table C.book} {V : DiffPlan S} {F : Extraction.Order}
variable {ι : Type*} [Fintype ι]

/-- Exact finite-geometry annihilation. All choices can depend on the finite
family I, but must include the same rooted estimate at every test of the chosen
fields. -/
theorem tenet (hC : C.Makes) (hq : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (h : V.Derivatives S) {J : S.Stress} (hc : Conserved V H.spin J) (v : S.Field d)
    (U : E4→E4) (hw : ∀ i : Axis,ContDiff ℝ ∞ (fun y => U y i)) (hl : killing U) (p : ℕ)
    (hg : ∀ y (r : ℝ),0<r → U (r • y)=r^p • U y)
    (D : ℕ) (hh : D+(3+p)=d+4) (HA:Aroma C) (I : ι→Watch C) (g : ι→ℂ)
    (ht : ∀ z : S.Field D, (∑ i : ι, g i * (I i).tester S D z)=0)
    (W : ι→E4→ℝ) (hy : ∀ i, Window (I i).held (W i)) :
    (∑ i : ι, g i * flux J (W i) U (I i).held (S.classTokens ∘ (I i).q) v)=0 := by
  classical
  let r:= fun i:ℕ=> Ribbons.fuga C.path.levels (i+1)
  have hr : ∀ i,0<r i:= HA.notes.pos
  have hwg:Tendsto r atTop (𝓝 0):= HA.notes.thins (by norm_num)
  let E (i j : Axis) (a : ι) l y := (r l:ℂ)^(3+p) * (I a).asked (J i j) v (r l • y)
  let M (i j : Axis) := weight capB i (fun y => U y j)
  let F (i j : Axis) l := ∫ y, ∑ a, g a*(M i j y * E i j a l y)
  have hf : ∀ᶠ l in atTop,∀ (i : ι) (j : Fin (I i).n), r l < ‖(I i).held j.succ‖ := by
    refine eventually_all.mpr (fun i => eventually_all.mpr (fun j => hwg.eventually (gt_mem_nhds (norm_pos_iff.mpr ?_))))
    intro he
    exact Fin.succ_ne_zero j ((I i).distinct (he.trans (I i).origin.symm))
  have hM (i j : Axis) : Integrable (fun y => ‖M i j y‖) := (integrable_weight capB.contDiff capB.hasCompactSupport i
    (hw j).continuous).norm
  have he (i j : Axis) : Tendsto (F i j) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr; intro ε hε
    let C' := ∫ y, ‖M i j y‖
    have hc': 0≤C' := integral_nonneg (fun _=> norm_nonneg _)
    let S' := ε/(C'+2)
    have he':0 < S':= div_pos hε (by linarith)
    have ht' : C'*S'<ε:= lt_of_lt_of_le (mul_lt_mul_of_pos_right (show C'<C'+2 by linarith) he') (le_of_eq (mul_div_cancel₀ _ (by linarith : C'+2≠0)))
    filter_upwards [hf,zone V hC hq ho H I g h HA hh (J i j) v ht he'] with l hh hx
    rw [dist_zero_right]
    calc
      _ ≤ ∫ y, ‖M i j y‖ * (S') := norm_integral_le_of_norm_le ((hM i j).mul_const _) (by
        filter_upwards with y
        change ‖∑ a, g a*(M i j y* E i j a l y)‖ ≤ _
        by_cases ht : Analysis.D (basis i) capB y = 0
        · have h : M i j y=0 := by simp [M,weight,ht]
          simp [h]
        have hP a : Points.cons (r l • y) (I a).held∈conf _ := separated_of_D (I a).distinct
          (stretch_window _ (I a).origin _ (hr l) (hh a)) (show Analysis.D (basis i) (stretch (r l) capB) _≠0 from by
            rw [D_stretch (hr l) capB.contDiff]; exact mul_ne_zero (inv_pos.mpr (hr l)).ne' ht)
        have he := hx _ (within_cap i _ (hr l) y ht)
        simp_rw [mul_left_comm (g _) (M i j y), ← Finset.mul_sum]; rw [norm_mul]
        exact mul_le_mul_of_nonneg_left he (norm_nonneg _))
      _ = _ := integral_mul_const ..
      _ < ε := ht'
  have hv := Tendsto.neg (tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun j _ => he i j)))
  -- all expressions are genuine integrals before distributing
  let f (i : ι) := flux J (W i) U (I i).held (S.classTokens ∘ (I i).q) v
  have hz : Tendsto (fun k : ℕ => -(∑ i : Axis, ∑ j : Axis,F i j k)) atTop (𝓝 0) :=
    (by simpa only [Finset.sum_const_zero,neg_zero] using hv)
  refine tendsto_nhds_unique_of_eventuallyEq (f:=fun _ : ℕ => ∑ i : ι,g i * f i) tendsto_const_nhds hz ?_
  filter_upwards [hf] with k hk
  let G (a : ι) (i j : Axis) y := M i j y * E i j a k y
  let c := stretch (r k) capB
  have hC a := stretch_window _ (I a).origin _ (hr k) (hk a)
  have hint (i j : Axis) (a : ι) : Integrable (G a i j) := by
    let T := term J c U (I a).held (S.classTokens ∘ (I a).q) v i j
    have ht (y : E4) : T (r k • y)= ((r k:ℂ)^4)⁻¹ * G a i j y := conversion_shell J U p hg capB.contDiff _ _ _ (hr k) _ _ y
    have hu : Integrable T := term_integrable J _ _ _ _ _ H.smooth (I a).distinct (hC a) _ _ (hw j).continuous
    have hz : G a i j=fun y => (r k:ℂ)^4 * T (r k • y) := by
      funext y
      rw [ht,mul_inv_cancel_left₀ (pow_ne_zero _ (by exact_mod_cast (hr k).ne'))]
    rw [hz]; exact (hu.comp_smul (hr k).ne').const_mul _
  have hF i j : F i j k=∑ a : ι,g a*(∫ y,G a i j y) := by
    unfold F; rw [integral_finsetSum _ (fun a _ => (hint i j a).const_mul _)]
    exact Finset.sum_congr rfl fun a _ => integral_const_mul (g a) (G a i j)
  have ht (a : ι) : f a= -(∑ i : Axis,∑ j : Axis,(∫ y,G a i j y)) := by
    unfold f; rw [unchanged_flux H h hc v U hw hl _ (I a).distinct (hy a) (hC a), flux]
    simp_rw [graded_integral J U p hg capB.contDiff _ _ _ (hr k)]; rfl
  simp_rw [ht,hF,mul_neg,Finset.mul_sum,Finset.sum_neg_distrib]
  refine congr_arg Neg.neg (Eq.trans (Finset.sum_comm) ?_)
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
end pay
end YM.MergeProof.Acme
