import YM.Next.FLUCTUATIONS.Defs
import YM.Work.E03

/-!
# Chart estimates for the unaffected defects

Gauge and real physical colors unchanged. Sizes here post-L only. All norm
estimates on actual paths, including repeated edges; no complex logarithm
choice around an entire configuration.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Pressure Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n c f : Side} {S : StepData c f}

section prices
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma chart_linear_cost (f : E → F) (x₀ : E) (h : AnalyticAt ℝ f x₀) : ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
    ∀ x : E, ‖x - x₀‖ ≤ r → ‖f x - f x₀‖ ≤ D * ‖x - x₀‖ := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨D,hD,hb⟩ := (hp.isBigO_sub_partialSum_pow 1).exists_pos
  obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hb.bound
  refine ⟨D,r,hD,hr, fun x hx => ?_⟩
  have hh := h (x:=x-x₀) (Metric.mem_closedBall.mpr (by rwa [dist_zero_right]))
  simpa only [FormalMultilinearSeries.partialSum, Finset.sum_range_one, hp.coeff_zero,
    add_sub_cancel, pow_one, Real.norm_of_nonneg (norm_nonneg _)] using! hh

/-- Use analytic jet through linear, both norm of linear and the
quadratic remainder uniform in a log ball. -/
lemma chart_quadratic_cost (f L : E → F) (h : AnalyticAt ℝ f 0)
    (hl : ∀ a : E, HasDerivAt (fun v : ℝ => f (v • a)) (L a) 0) :
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧ ∀ a : E,
      ‖L a‖ ≤ D * ‖a‖ ∧ (‖a‖ ≤ r → ‖f a - (f 0 + L a)‖ ≤ D * ‖a‖^2) := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨D,hD,hb⟩ := (hp.isBigO_sub_partialSum_pow 2).exists_pos
  let J := fderiv ℝ f 0
  have he (a) : J a = L a := (Push.side _ hp.hasFDerivAt.differentiableAt a).unique (hl a)
  have h1 (a : E) : p 1 (fun _ => a) = L a := by
    rw [← he]; unfold J; rw [hp.hasFDerivAt.fderiv]; rfl
  obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hb.bound
  refine ⟨max D ‖J‖,r,hD.trans_le (le_max_left ..),hr, fun a => ⟨?_,fun ha => ?_⟩⟩
  · rw [← he]
    exact (J.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
  have hx : ‖f a - (f 0 + L a)‖ ≤ D * ‖a‖^2 := by
    simpa only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, hp.coeff_zero, h1, Real.norm_of_nonneg (sq_nonneg _)] using!
        h (x:=a) (Metric.mem_closedBall.mpr (by rwa [dist_zero_right]))
  exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (sq_nonneg _))
end prices

lemma chord_dist (u : G.El) : G.colorScale * G.chord u = ‖G.mat u - 1‖ := by
  simpa using chord_gap u (1 : G.El)

lemma log_chart_cost (G : Gauge) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧
    ∀ u : G.El, G.chord u ≤ δ → G.lieExp (G.plog (G.mat u)) = u ∧
      ‖G.plog (G.mat u)‖ ≤ C * G.chord u := by
  obtain ⟨D,r,hD,hr,hd⟩ := chart_linear_cost _ _ G.plog_diff.analyticAt
  have h := G.plog_right
  obtain ⟨s,hs,hb⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 h
  have hp := G.colorScale_pos
  refine ⟨D*G.colorScale,(min r s)/G.colorScale, by positivity, div_pos (lt_min hr hs) hp,?_⟩
  intro u hu
  have hz : ‖G.mat u-1‖ ≤ min r s := by
    rw [← chord_dist, mul_comm]; exact (le_div_iff₀ hp).mp hu
  obtain ⟨h1,h2⟩ := le_min_iff.mp hz
  refine ⟨hb (Metric.mem_closedBall.mpr ?_),?_⟩
  · change dist (G.mat u) (1:G.Mat) ≤ s
    rwa [dist_eq_norm]
  have hh := hd _ h1
  rwa [G.plog_one,sub_zero, ← chord_dist, ← mul_assoc] at hh

lemma chord_chart_cost (G : Gauge) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧
    ∀ a : G.Color, ‖a‖ ≤ δ → G.chord (G.lieExp a) ≤ C * ‖a‖ := by
  obtain ⟨D,r,hD,hr,hd⟩ := chart_linear_cost (fun a => G.mat (G.lieExp a)) 0
    G.exp_jet.contDiffAt.analyticAt
  refine ⟨D/G.colorScale,r,div_pos hD G.colorScale_pos,hr,?_⟩
  intro a ha
  apply le_of_mul_le_mul_left _ G.colorScale_pos
  rw [chord_dist, ← mul_assoc, show G.colorScale * (D / G.colorScale) = D by rw [mul_comm]; exact div_mul_cancel₀ _ G.colorScale_pos.ne']
  simpa only [G.mat_lieExp_zero, G.mat_one, sub_zero] using hd a (by rwa [sub_zero])

/-- Extension of *these* links (only on the interior) to uniformly
small global log data. Both fine and coarse extension use the same cost. -/
lemma extend_interior (G : Gauge) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧
    ∀ {n m : Side} (p : Site n → Site m) (q : Site m) (D : ℕ) (W : Config G n) (h : ℝ), 0 ≤ h → h ≤ δ →
      (∀ i : Bond n, separation q (p i.1) ≤ D → G.chord (W i) ≤ h) →
        ∃ a : LogField G n, ‖a‖ ≤ C*h ∧ AgreeNear p q D W (represent a) := by
  obtain ⟨C,δ,hC,hr,he⟩ := log_chart_cost G
  refine ⟨C,δ,hC,hr,?_⟩
  intro n m p q D W h hh ht hD
  let e := Work.E03.poleEquiv n
  let a (i : Body 1 n) := if separation q (p (e.symm i).1) ≤ D then G.plog (G.mat (W (e.symm i))) else 0
  refine ⟨a, (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le hh)).mpr ?_,?_⟩
  · intro i
    dsimp only [a]; split
    next hi => exact ((he _ ((hD _ hi).trans ht)).2).trans (mul_le_mul_of_nonneg_left (hD _ hi) hC.le)
    next hi => rw [norm_zero]; positivity
  intro i hi
  change W i = G.lieExp (a (e i)) * 1
  dsimp only [a]; rw [Equiv.symm_apply_apply, if_pos hi, mul_one]
  exact (he _ ((hD _ hi).trans ht)).1.symm

/-- Cost of transport in physical color; no lower bound on the dimension
of `G.lie`. -/
lemma adjoint_norm_sub (u : G.El) (x : G.Color) :
    ‖G.adjoint u x - x‖ ≤ 2 * G.colorScale * G.chord u * ‖x‖ := by
  let U := G.mat u
  let X := G.colorMat x
  let V := star U
  have hv : ‖V-1‖ = ‖U-1‖ := by rw [show V-1=star (U-1) by rw [star_sub,star_one], norm_star]
  have hh : ‖U*X*V-X‖ ≤ ‖U-1‖*‖X‖+‖X‖*‖V-1‖ := calc
    _ = ‖(U-1)*X*V + X*(V-1)‖ := by rw [sub_mul,sub_mul,mul_sub,one_mul,mul_one]; abel_nf
    _ ≤ ‖(U-1)*X*V‖ + ‖X*(V-1)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [Gauge.frob_mul_eq _ _ (show V*star V=1 from by simp [V,U])]
      exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
  apply le_of_mul_le_mul_left _ G.colorScale_pos
  rw [← G.colorMat_norm, map_sub, G.mat_adjoint]; apply hh.trans
  rw [hv,show ‖U-1‖ = _ from (chord_dist u).symm, show ‖X‖ = _ from G.colorMat_norm x]; exact le_of_eq (by ring)

lemma travel_chord {n : Side} (W : Config G n) (w : Walk) (x : Site n) (h : ℝ)
    (hv : ∀ i, G.chord (W i) ≤ h) : G.chord (travel W x w) ≤ w.length*h := by
  induction w generalizing x with
  | nil => simp [travel]
  | cons d w ih =>
    have hb : G.chord (d.read W x) ≤ h := by
      unfold Step.read; split
      next hh => rw [G.chord_inv]; exact hv _
      next hh => exact hv _
    simp only [travel,List.length_cons,Nat.cast_add,Nat.cast_one, add_mul,one_mul]
    exact (G.chord_triangle ..).trans ((add_le_add hb (ih _)).trans_eq (add_comm ..))

section face
-- 4 terms with the two positive bonds for the return path read as inverses
-- (use site of the origin of their stored positive branch).
private abbrev quadSpace (G : Gauge) := Fin 4 → G.Color

private def read4 (a : quadSpace G) := G.lieExp (a 0) * G.lieExp (a 1) *
  (G.lieExp (a 2))⁻¹ * (G.lieExp (a 3))⁻¹

private def circulation4 (a : quadSpace G) := a 0 + a 1 - a 2 - a 3

private lemma circulation_deriv (a : quadSpace G) :
    HasDerivAt (fun t : ℝ => G.curvature (read4 (t • a))) (circulation4 a) 0 := by
  apply Work.F03.curvature_of_hasDerivAt (V:=fun t => read4 (t • a))
  have he (i : Fin 4) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • a i))) (G.colorMat (a i)) 0 := by
    simp only [G.mat_lieExp, map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat (a i)) (0:ℝ)
  simp only [read4, circulation4, Pi.smul_apply, G.mat_mul, G.mat_inv, map_add, map_sub]
  convert! ((((he 0).mul (he 1)).mul (he 2).star).mul (he 3).star) using 1
  simp only [Pi.mul_apply,zero_smul,G.mat_lieExp_zero,G.mat_one,G.colorMat_skew,star_one, one_mul,mul_one]
  abel

lemma curvature_diff_mat {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → G.El) (x : E)
    (h : ContDiffAt ℝ ω (fun v => G.mat (u v)) x) : ContDiffAt ℝ ω (fun v => G.curvature (u v)) x := by
  have he := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp x h
  simp only [Gauge.curvature, G.mat_inv]
  apply ContDiffAt.comp (g:=G.projectColor.toContinuousLinearMap) x
    G.projectColor.toContinuousLinearMap.contDiff.contDiffAt (f:=fun y => _ • (G.mat (u y)-star _))
  exact (h.sub he).const_smul _

private lemma read4_cost (G : Gauge) : ∃ C r : ℝ, 0<C ∧ 0<r ∧
    ∀ x : quadSpace G, ‖circulation4 x‖ ≤ C*‖x‖ ∧
      (‖x‖ ≤ r → ‖G.curvature (read4 x) - circulation4 x‖ ≤ C*‖x‖^2) := by
  have hu (i : Fin 4) : ContDiff ℝ ω fun x : quadSpace G => G.mat (G.lieExp (x i)) :=
    G.exp_jet.comp (contDiff_apply ℝ _ i)
  have hv (i : Fin 4) : ContDiff ℝ ω fun x : quadSpace G => star (G.mat (G.lieExp (x i))) :=
    (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (hu i)
  have hm : ContDiff ℝ ω fun x : quadSpace G => G.mat (read4 x) := by
    simp only [read4, G.mat_mul, G.mat_inv]; exact (((hu 0).mul (hu 1)).mul (hv 2)).mul (hv 3)
  have he := chart_quadratic_cost _ _
    (curvature_diff_mat _ (0:quadSpace G) hm.contDiffAt).analyticAt (fun a => circulation_deriv a)
  have hz : G.curvature (read4 (0:quadSpace G))=0 := by simp only [read4, Pi.zero_apply,
    G.mat_lieExp_zero, inv_one, one_mul, G.curvature_unit]
  simpa only [hz,zero_add] using! he

private def coords4 (a : LogField G n) (p : Cell n) : quadSpace G :=
  let x := p.1; let i := p.2.val.1; let j := p.2.val.2
  ![a (x, coord i), a (x+step i, coord j), a (x+step j, coord i), a (x, coord j)]

private lemma read_coords4 (a : LogField G n) (p : Cell n) :
    read4 (coords4 a p) = faceValue (represent a) p ∧
      circulation4 (coords4 a p) = Work.F03.faceCurl p a := by
  have h (x : Site n) (i j : Axis) : x + step i + step j - step i = x + step j := by abel
  have h' (x : Site n) (i j : Axis) : x + step i + step j + (- step i) = x + step j := by abel
  constructor
  · simp only [coords4, read4,faceValue, represent,square,travel,
      Step.vec_pos, Step.vec_neg,Step.pos_read,Step.neg_read, h,h',add_sub_cancel_right]
    simp [increment,collect,mul_assoc]
  unfold circulation4 coords4 Work.F03.faceCurl
  rw [← Exterior.fundamental]
  simp only [square, linkSum, Step.used,Step.vec, negDir,posDir, Bool.false_eq_true, ↓reduceIte,
    collect, add_zero, h,h',add_sub_cancel_right]; simp [sub_eq_add_neg]; abel

lemma face_chart_cost (G : Gauge) : ∃ C r : ℝ, 0<C ∧ 0<r ∧
    ∀ {n : Side} (a : LogField G n) (x : Cell n), ‖Work.F03.faceCurl x a‖ ≤ C*‖a‖ ∧
      (‖a‖ ≤ r → ‖G.curvature (faceValue (represent a) x) - Work.F03.faceCurl x a‖ ≤ C*‖a‖^2) := by
  obtain ⟨C,r,hC,hr,hb⟩ := read4_cost G
  refine ⟨C,r,hC,hr,?_⟩
  intro n a x
  rw [← (read_coords4 a x).1, ← (read_coords4 a x).2]
  let t := coords4 a x
  have hh : ‖t‖ ≤ ‖a‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i <;> exact norm_le_pi_norm a _
  refine ⟨((hb t).1).trans (mul_le_mul_of_nonneg_left hh hC.le), fun ht => ?_⟩
  exact (((hb t).2) (hh.trans ht)).trans (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hh) hC.le)
end face
end YM.Next.Fluctuations
