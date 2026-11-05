import YM.Pert.Fourier.Halo
/-! Compact continuum quadrature across heat removal. Upper (including UV) end is oscillatory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open YM.Next.Rank.Radian MeasureTheory Filter Lattice Topology Set Function Metric
open scoped ContDiff BigOperators RealInnerProductSpace FourierTransform Classical

def tonic (D : List Axis) (s b : ℝ) (z k : E4) := (wave z k * press D (liturgy b) k) * ((disk (radial D s k):ℝ):ℂ)
noncomputable def mild (D : List Axis) (s b : ℝ) (z : E4) := ∫ k, tonic D s b z k
lemma disk_always (q : E4) : ‖(↑(disk q) : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg disk.nonneg]; exact disk.le_one
lemma press_measurable (D : List Axis) (b : ℝ) : Measurable (press D (liturgy b)) := by induction D with | nil => unfold liturgy press; unfold major; simp only [List.foldr_nil]; fun_prop | cons i d ih => exact (by apply Measurable.mul _ ih; unfold chirp; fun_prop)
lemma press_cost (D : List Axis) (s b : ℝ) (hs : s>0) (hb : b≥0) (k : E4) (he : ‖radial D s k‖≤1) : ‖press D (liturgy b) k‖ ≤ Real.exp 1 * ‖press D (liturgy ((factor s)^2)) k‖ := by
  induction D with
  | nil => unfold press; dsimp only [List.foldr_nil]; simp only [YM.Next.Rank.Radian.lit_norm]
           generalize hn : ‖k‖ = h at *
           rw [radial_norm [] s hs,hn] at he
           have hv := factor_pos s hs
           change factor s * h≤1 at he
           have hh := mul_nonneg (factor_pos s hs).le (show 0≤h from hn ▸ norm_nonneg k)
           have ht : Real.exp (-b*h^2) ≤ Real.exp (-((factor s)^2)* h^2+1) := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hb (sq_nonneg h),he,hh])
           apply le_trans (b:=(Maxwell.normal/h^2)*(Real.exp _)) (le_of_eq (by ring))
           apply (mul_le_mul_of_nonneg_left ht (show 0≤Maxwell.normal/h^2 from by unfold Maxwell.normal; positivity)).trans (le_of_eq (by rw [Real.exp_add];ring))
  | cons i D ih => change ‖chirp i k * _‖ ≤ Real.exp 1 * ‖chirp i k * _‖; simp only [Complex.norm_mul]; rw [mul_left_comm _ ‖chirp i k‖]; exact mul_le_mul_of_nonneg_left (ih he) (norm_nonneg _)
lemma tonic_int (D : List Axis) (s b : ℝ) (hs : s>0) (hb : b≥0) (z : E4) : Integrable (tonic D s b z) := by
  have hs' : Measurable (fun k : E4=> (wave z k * press D (liturgy b) k) * ((disk (radial D s k):ℝ):ℂ)) := Measurable.mul (g:=fun k=> (disk (radial D s k):ℂ)) ((show Continuous (wave z) by unfold wave; fun_prop).measurable.mul (press_measurable _ _)) ((Complex.continuous_ofReal.comp (disk_alter _ hs).continuous).measurable) -- remove inst
  apply (((Moment.pressed D (passion (b:=(factor s)^2) (sq_pos_of_pos (factor_pos s hs)))).integral.norm.const_mul (Real.exp 1)).mono' hs'.aestronglyMeasurable)
  refine Eventually.of_forall fun k=> ?_
  by_cases hw : 1<‖radial D s k‖
  · change ‖tonic D s b z k‖ ≤ _; rw [tonic,disk_out hw.le]; simp; positivity
  change ‖tonic _ _ _ _ k‖≤_
  simp only [tonic,YM.Next.Rank.Radian.wave,Complex.norm_mul,Circle.norm_coe,one_mul]
  apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (disk_always _))
  exact press_cost D s b hs hb k (le_of_not_gt hw)

lemma mild_step (D : List Axis) (s b : ℝ) (hs : s>0) (hb : b≥0) (z : E4) : mild D (2*s) b z - mild D s b z = precious D s b z := by
  unfold mild; rw [← integral_sub (tonic_int D _ _ (mul_pos two_pos hs) hb z) (tonic_int D _ _ hs hb z)]; unfold precious
  apply MeasureTheory.integral_congr_ae (Eventually.of_forall fun k=>?_)
  have he : radial D (2*s) k = (1/2:ℝ) • radial D s k := by ext i; simp only [PiLp.smul_apply, radial_apply, smul_eq_mul, factor]; field_simp
  simp only [tonic,he, untab _ _ _ hs,carrier,middle,Complex.ofReal_sub]; ring
lemma mild_fresh (D : List Axis) (s b : ℝ) (hs : s>0) (hb : b>0) (z : E4) : Tendsto (fun (j:ℕ)=> mild D ((2:ℝ)^j*s) b z) atTop (𝓝 (harmon (press D (liturgy b)) z)) := by
  unfold mild; rw [wind]; let F:= press D (liturgy b)
  have hi := (Moment.pressed D (passion hb)).integral.norm
  refine tendsto_integral_of_dominated_convergence (μ:=volume) (fun k:E4=> ‖F k‖) (fun i=> (tonic_int D _ b (by positivity) hb.le z).aestronglyMeasurable) hi (fun i=>Eventually.of_forall fun k=> by rw [tonic]; simp only [YM.Next.Rank.Radian.wave,Complex.norm_mul,Circle.norm_coe,one_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (disk_always _)) ?_
  refine Eventually.of_forall fun k=> tendsto_const_nhds.congr' ?_
  have hm := (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℝ) by norm_num)).eventually (eventually_gt_atTop (2*turn*‖k‖/s))
  exact hm.mono fun i hi => (by change _ = tonic D ((2:ℝ)^i*s) b z k; rw [tonic,disk_one ?_,Complex.ofReal_one,mul_one]; rw [radial_norm D _ (by positivity),div_mul_eq_mul_div,div_le_iff₀ (by positivity)]; have H:=(div_lt_iff₀ hs).mp hi;linarith only [H])

lemma precious_scale (D : List Axis) (s b : ℝ) (hs : s>0) (z : E4) : precious D s b z = amp D s * ((factor s:ℂ)^4)⁻¹ * harmon (halo D (b/(factor s)^2)) ((factor s)⁻¹ • z) := by
  let f (k:E4):= wave ((factor s)⁻¹ • z) k * halo D (b/(factor s)^2) k
  have hf k : amp D s * f ((factor s) • k) = carrier D s 0 b z k := by
    have he : wave ((factor s)⁻¹ • z) ((factor s) • k) = wave z k := by simp only [wave,starRingEnd_apply,star_trivial,inner_neg_right,inner_smul_left,inner_smul_right]; field_simp [(factor_pos s hs).ne']
    unfold f halo carrier; rw [← show radial D s k=factor s • k from rfl, major_glow D s _ hs k]; unfold radial; rw [he];ring
  unfold precious; rw [← funext hf, integral_const_mul,Measure.integral_comp_smul_of_nonneg volume f _ (hR:=(factor_pos _ hs).le), Complex.real_smul]; push_cast; simp [mul_assoc,Axis,E4,f,wind]
lemma precious_upper (D : List Axis) (z : E4) (hz : z≠0) : ∃ C≥0, ∀ (s b : ℝ), s>0 → b≥0 → ‖precious D s b z‖ ≤ C/s := by
  obtain ⟨C,hC,H⟩ := cooling D (D.length+3)
  have hv : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have hp : 0<turn := by positivity
  let j:=D.length+3
  refine ⟨C*turn^j / (turn^4*‖z‖^j), by positivity,fun s b hs hb=>?_⟩
  rw [precious_scale _ _ _ hs]; simp only [Complex.norm_mul]; rw [amp_cost D s hs,norm_inv,Complex.norm_pow,Complex.norm_real]
  let T:=factor s; have ht : 0 < T := factor_pos s hs
  have hx : ‖T⁻¹ • z‖=‖z‖/T := by simp [norm_smul,norm_inv,Real.norm_of_nonneg ht.le,div_eq_mul_inv]; exact mul_comm ..
  let w: ℂ := harmon (halo D (b/(factor s)^2)) (T⁻¹ • z)
  have e : ‖T⁻¹ • z‖^j * ‖w‖ ≤ C := H (div_nonneg hb (sq_nonneg _)) _
  have ea : T ≠ 0 := ht.ne'; rw [show ‖factor s‖=T from Real.norm_of_nonneg ht.le]; change s^D.length*s⁻¹^2 * (T^4)⁻¹ * ‖w‖ ≤ _
  rw [show ‖w‖ = (‖z‖ / T)⁻¹^j * (‖T⁻¹ • z‖^j*‖w‖) by rw [inv_pow,hx,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (div_ne_zero hv ea)),one_mul]]
  grw [e]
  apply le_of_eq; dsimp only [j,T,factor]; rw [inv_div,div_pow,div_pow,div_pow, pow_add s]; field_simp
lemma precious_lower (D : List Axis) (s b : ℝ) (hs : s>0) (hb : b≥0) (z : E4) : ‖mild D s b z‖ ≤ s^(D.length+2) * (∫ k,Real.exp 1* ‖wave z k * press D (liturgy (turn^2)) k‖) := by
  let p := Real.exp 1
  let f k := p * ‖wave z k*press D (liturgy (factor s ^ 2)) k‖
  have eq k b : ‖wave z k*press D (liturgy b) k‖=‖press D (liturgy b) k‖ := by simp [YM.Next.Rank.Radian.wave]
  rw [mild]; refine le_trans (b:=∫ k,f k) (norm_integral_le_of_norm_le ?_ ?_) (le_of_eq ?_)
  · unfold f; simp only [eq]; exact ((Moment.pressed D (passion (sq_pos_of_pos (factor_pos _ hs)))).integral.norm.const_mul p)
  · refine Eventually.of_forall fun k=>?_ ; unfold tonic; rw [Complex.norm_mul]
    by_cases h : 1 < ‖radial D s k‖
    · rw [disk_out h.le]; simp [f,p]; positivity
    grw [disk_always]; simpa only [one_mul,mul_one, f,eq] using press_cost D s b hs hb k (le_of_not_gt h)
  let g k := p * ‖wave z k*press D (liturgy (turn^2)) k‖
  have e k : factor 1 • (s⁻¹ • k) = radial D s k := by simp [smul_smul,radial,factor,div_eq_mul_inv]
  have ew k : g (s⁻¹ • k) = (p * ‖major 1 (radial D s k)‖ * ‖symbol D 0 (radial D s k)‖) := by
    unfold g; rw [eq,base_glow D 1 (turn^2) zero_lt_one, show amp D 1=1 by simp [amp],one_mul,Complex.norm_mul, ←major_glow D 1 _ zero_lt_one,show turn^2 / (factor 1)^2=1 from by rw [show factor 1 = turn from by simp [factor]]; exact div_self (by positivity) -- hp not in scope
    ]; rw [show radial D 1 (s⁻¹ • k)=radial D s k from e k];ring
  have hp k : f k= g (s⁻¹ • k) * (s^D.length*s⁻¹^2) := by unfold f; rw [ew,eq,base_glow _ _ _ hs,←major_glow D s _ hs,div_self (sq_pos_of_pos (factor_pos s hs)).ne']; simp only [Complex.norm_mul]; rw [amp_cost _ _ hs];ring
  calc (∫ k,f k) = (∫ k, g (s⁻¹ • k))*(s^D.length*s⁻¹^2) := by simp_rw [hp,MeasureTheory.integral_mul_const]
       _ = _ := by rw [Measure.integral_comp_inv_smul_of_nonneg volume g hs.le]; change (s ^ Module.finrank ℝ E4 * _) * _ = _; have hr := YM.Next.Rank.Radian.spaceD; rw [hr]; change s^4*(∫ k, g k)*(s^D.length*s⁻¹^2) = _ * (∫ k,g k); rw [pow_add]; field_simp
end YM.Pert.Band
