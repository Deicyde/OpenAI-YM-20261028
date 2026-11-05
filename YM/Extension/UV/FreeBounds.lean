import YM.Next.FREE_KERNELS.Rack
/-!
Uniform pole comparison for trains sharing the first scales. Use the fourth-order small
momentum precision `K` elsewhere; only the D-card at punctured real frequencies here. Absolute
norms apply to the complete propagated covariance (including noise), not its summands near
separate complex pole cones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Filter Function Lattice YM RG Laurent Bloch Metric Next.Free
open scoped Topology BigOperators
variable {j : ℕ}

lemma length_bounds (p : Momentum) : ‖p‖^2 ≤ lengthSq p ∧ lengthSq p ≤ 4*‖p‖^2 := by
  have hn : ‖p‖ ≤ Real.sqrt (lengthSq p) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) ).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (show 0 ≤ lengthSq p from Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr; exact Finset.single_le_sum (f:=fun i : Axis=> ‖p i‖^2) (fun i _=> sq_nonneg _) (Finset.mem_univ _)
  refine ⟨by nlinarith [Real.sqrt_nonneg (lengthSq p),Real.sq_sqrt (x:=lengthSq p) (Finset.sum_nonneg fun j _=>sq_nonneg _) ,norm_nonneg p],?_⟩
  calc _ ≤ ∑ _i : Axis, ‖p‖^2 := Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm p i) _
       _ = _ := by simp [Axis]

lemma seed_linear_error (M : Side) (p : Momentum) (hp:p ∈ baseCube) (i : Axis) :
    ‖seedQ M p i - Complex.I * p i‖ ≤ (meter.high+1)*‖p i‖^2 := by
  have hp' : p ∈ cube zone := mem_cube_real (base_subset_realCube zone_pos hp) zone_pos
  have hh := meter.high_pos
  by_cases hk : ‖p i/(M.val : ℂ)‖ ≤ 1
  · have ht := Complex.norm_exp_sub_one_sub_id_le (x:=Complex.I * (p i / M.val)) (by rw [norm_mul,Complex.norm_I,one_mul]; exact hk)
    rw [norm_mul (Complex.I) (p i / (M.val:ℂ)),Complex.norm_I,one_mul,norm_div,Complex.norm_natCast] at ht
    unfold seedQ chip
    rw [show (M.val:ℂ)*(Complex.exp (Complex.I * narrow M p i) - 1) - Complex.I * p i=(M.val:ℂ)*(Complex.exp (Complex.I * narrow M p i)-1-Complex.I*narrow M p i) by rw [narrow_apply]; field_simp]
    rw [norm_mul,Complex.norm_natCast,narrow_apply]
    apply (mul_le_mul_of_nonneg_left ht (show 0≤(M.val:ℝ) by positivity)).trans
    have hm : 1 ≤ (M.val:ℝ) := by exact_mod_cast M.property
    field_simp
    have h : 1 ≤ (M.val:ℝ) * (meter.high+1) := one_le_mul_of_one_le_of_one_le hm (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ‖p i‖)]
  push Not at hk
  rw [norm_div,Complex.norm_natCast] at hk
  have ht := (seedQ_size M p hp' i).2
  calc _ ≤ ‖seedQ M p i‖ + ‖Complex.I*p i‖ := norm_sub_le ..
       _ = ‖seedQ M p i‖ + ‖p i‖ := by rw [norm_mul,Complex.norm_I,one_mul]
       _ ≤ (meter.high + 1)*‖p i‖ := by linarith
       _ ≤ _ := by
         have h := (lt_div_iff₀ (side_pos M)).mp hk
         have hm : 1 ≤ (M.val:ℝ) := by exact_mod_cast M.property
         gcongr
         nlinarith

lemma divisor_approx : ∃ b:ℝ,0<b ∧ ∀ (M : Side) (p : Momentum), p ∈ baseCube → ‖divisor M p-(lengthSq p:ℂ)‖ ≤ b*‖p‖*lengthSq p := by
  refine ⟨(meter.high+1)^2,(by have := meter.high_pos; positivity), fun M p hp => ?_⟩
  have hz := divisor_normSq M hp.1
  rw [hz, ← Complex.ofReal_sub, Complex.norm_real]
  unfold lengthSq
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro i _
  have hn := abs_norm_sub_norm_le (seedQ M p i) (Complex.I*p i)
  rw [norm_mul (Complex.I) (p i), Complex.norm_I, one_mul] at hn
  have ht := hn.trans (seed_linear_error M p hp i)
  have hu := seedQ_size M p (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) i
  rw [sq_sub_sq,norm_mul,mul_comm ‖‖seedQ M p i‖ + ‖p i‖‖]
  apply (mul_le_mul (b:= (meter.high+1) * ‖p i‖^2) (d:= (meter.high+1)*‖p‖) (show _ from ht) (show _ from ?_) (norm_nonneg _) (by have := meter.high_pos; positivity)).trans
  · exact (le_of_eq (by ring))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have he := norm_le_pi_norm p i
  have hh := meter.high_pos; nlinarith

lemma reciprocal_approx : ∃ b:ℝ,0<b ∧ ∀ (M : Side) (p : Momentum), p ∈ baseCube → p ≠ 0 → ‖(divisor M p)⁻¹ - ((lengthSq p:ℂ))⁻¹‖ ≤ b*(‖p‖)⁻¹ := by
  obtain ⟨b,hb,h⟩ := divisor_approx
  have hk := meter.low_pos
  refine ⟨b/(meter.low^2),(by positivity),fun M p hp he => ?_⟩
  have hz := norm_pos_iff.mpr he
  have hm := lengthSq_pos he
  have hd := divisor_ne M (base_subset_realCube zone_pos hp) he
  have hh := (divisor_real_bounds M (base_subset_realCube zone_pos hp)).1
  have hv := hh.trans (Complex.re_le_norm _)
  rw [show (divisor M p)⁻¹ - ((lengthSq p:ℂ))⁻¹ = -((divisor M p)-(lengthSq p:ℂ)) * ((divisor M p)^(-1:ℤ) * ((lengthSq p:ℂ))^(-1:ℤ)) by
    have hh' : (lengthSq p:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have h : (0:ℂ) = (0:ℂ) := rfl
    simp only [zpow_neg,zpow_one]; field_simp; ring]
  simp only [norm_mul,norm_neg,zpow_neg,zpow_one, norm_inv, Complex.norm_real,Real.norm_eq_abs, abs_of_pos hm]
  apply (mul_le_mul (h M p hp) (mul_le_mul_of_nonneg_right (by exact (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0<(meter.low)^2*lengthSq p) hv) (by positivity)).mpr hv) (by positivity : 0 ≤ (lengthSq p)⁻¹)) (by positivity) (by positivity)).trans
  rcases length_bounds p with ⟨hl,-⟩
  field_simp
  nlinarith -- normalization maybe products; handle explicitly later

lemma moderate_gap_low {ι : Type*} {f:ι→Momentum→ℂ} (h:Moderate (fun _ : ι=>1) f) (he:∀ i,f i 0=1) :
    ∃ c:ℝ,0<c∧ ∀ i p, p∈baseCube → ‖f i p-1‖≤ c*‖p‖ := by
  obtain ⟨η,c,hη,hc,hM⟩:=h
  refine ⟨(c+1)/(η/2), by positivity, fun i p hp => ?_⟩
  by_cases hz : p∈ball 0 (η/2)
  · have ht : ball (0:Momentum) (η/2) ⊆ cube η := by
      convert ball_inside_cube (cube_zero (η/2) (by positivity)) (η:=η) using 1; ring_nf
    have hx := Complex.dist_le_div_mul_dist_of_mapsTo_ball (f:=f i) (R₁:=η/2) (R₂:=c+1) (fun p hp=>((hM i).hol p (ht hp)).differentiableWithinAt) (show MapsTo (f i) (ball 0 _) _ from fun z hz' => by
      rw [mem_closedBall, dist_eq_norm,he]; exact (norm_sub_le ..).trans (by simpa using add_le_add_right ((hM i).bound z (ht hz')) (1:ℝ))) hz
    simpa only [he,dist_eq_norm,sub_zero] using hx
  have hx : η/2 ≤ ‖p‖ := by simpa using hz
  apply (norm_sub_le ..).trans
  apply le_trans (b:=c+1)
  · have h' := (hM i).bound p (mem_cube_real (base_subset_realCube hη hp) hη)
    simpa using add_le_add_right h' (1:ℝ)
  have h' := mul_le_mul_of_nonneg_left hx (show 0≤(c+1)/(η/2) by positivity)
  simpa [ne_of_gt hη] using h'

lemma about_onepole (k : ℝ) (hj: 4 ≤ j) : ∃ b:ℝ,0<b ∧ ∀ (v:Train j) a p, p∈baseCube → p≠0 →
    ‖Train.levelD k v a p-((lengthSq p:ℂ)⁻¹)‖ ≤ b*(1+ ‖p‖⁻¹) := by
  have hir := Train.lid_cost (j:=j) (fun x:Train j × Axis => x.1) fun x => x.2
  obtain ⟨c,hc,hL⟩ := moderate_gap_low hir fun ⟨v,a⟩=> by simp [Train.lid,Train.drive,yen,narrow]
  choose η d hη hd hD using Train.drain_reserve k (j:=j) hj (fun x:Train j × Axis=> x.1) fun x => x.2
  obtain ⟨b,hb,hB⟩ := reciprocal_approx
  have hu := meter.low_pos
  refine ⟨b+c*(meter.low^2)⁻¹+d, by positivity, fun v a p hp he => ?_⟩
  have h := base_subset_realCube zone_pos hp
  have ht := divisor_ne v.mass h he
  have hlen := lengthSq_pos he
  have hg := (divisor_real_bounds v.mass h).1.trans (Complex.re_le_norm _)
  have hm : meter.low^2*‖p‖^2 ≤ ‖divisor v.mass p‖ := le_trans (mul_le_mul_of_nonneg_left (length_bounds _).1 (sq_nonneg _)) hg
  have hZ := norm_pos_iff.mpr he
  have h1 : ‖Train.drain k v a p‖ ≤d := by simpa only [mul_one] using (hD (v,a)).bound p (mem_cube_real (base_subset_realCube hη hp) hη)
  have h2 := hL (v,a) p hp
  have h3 : ‖(divisor v.mass p)⁻¹‖ ≤ (meter.low^2*‖p‖^2)⁻¹ := by
    rw [norm_inv]; apply (inv_le_inv₀ (by positivity) (by positivity)).mpr hm
  rw [Train.pole_split]
  set vv : ℂ := (divisor v.mass p)⁻¹
  set U : ℂ := ((lengthSq p:ℂ))⁻¹
  have h4 := hB v.mass p hp he
  calc
    _ = ‖((Train.lid v a p-1)*vv +(vv-U)) + Train.drain k v a p‖ := by congr 1; ring
    _ ≤ ‖(Train.lid v a p-1)*vv‖ + ‖vv-U‖ + ‖Train.drain k v a p‖ := le_trans (norm_add_le ..) (by linarith [norm_add_le ((Train.lid v a p-1)*vv) (vv-U)])
    _ ≤ c*‖p‖*(meter.low^2*‖p‖^2)⁻¹+b*‖p‖⁻¹+d := by rw [norm_mul]; gcongr
    _ = (b+c*(meter.low^2)⁻¹)*‖p‖⁻¹+d := by field_simp; ring
    _ ≤ _ := by have := mul_nonneg (show 0≤d from hd.le) (show 0≤ ‖p‖⁻¹ by positivity); nlinarith [show 0 ≤ c * (meter.low^2)⁻¹ by positivity]

noncomputable def Dcost (k : ℝ) (j : ℕ) := if h:4≤j then (about_onepole k h).choose else (1:ℝ)

lemma Dcost_pos (k : ℝ) (j:ℕ) : 0 < Dcost k j := by
  unfold Dcost
  split
  next h => exact (about_onepole k h).choose_spec.1
  next => exact zero_lt_one

lemma diff_bound (k : ℝ) (hj : 4≤j) (v w : Train j) (a : Axis) (p : Momentum) (hp:p∈baseCube) (he:p≠0) :
    ‖Train.levelD k v a p - Train.levelD k w a p‖ ≤ (2*Dcost k j)*(1+‖p‖⁻¹) := by
  have h x := (about_onepole k hj).choose_spec.2 x a p hp he
  rw [show Dcost k j=(about_onepole k hj).choose from by rw [Dcost,dif_pos hj]]
  calc _ = ‖(Train.levelD k v a p-(lengthSq p:ℂ)⁻¹) - (Train.levelD k w a p-(lengthSq p:ℂ)⁻¹)‖ := by congr 1; abel
       _ ≤ _ := by linarith [norm_sub_le (Train.levelD k v a p - (lengthSq p:ℂ)⁻¹) (Train.levelD k w a p-(lengthSq p:ℂ)⁻¹),h v,h w]

/-- weighted alias average positivity bound by the feed applied to one. -/
lemma feed_control {j:ℕ} (v:Train j) (a : Axis) (p : Momentum) (hp:physical p) (f : Momentum→ℂ) {c:ℝ}
    (h:∀ i: Site v.mass, ‖f (aliasAt p i)‖ ≤ c) : ‖feed v a f p‖ ≤ ‖feed v a (fun _=>1) p‖*c := by
  have hi (i:Site v.mass) := v.drive_price a (aliasAt p i) (alias_real hp i)
  let z (i : Site v.mass):=aliasAt p i
  let d := fun i=> yen (v.drive a) (z i)
  have hc (i) : d i = (‖d i‖ : ℝ) := by dsimp only [d,z]; rw [(hi i).norm,(hi i).of_real]
  unfold feed shuttle
  rw [norm_mul, norm_mul, mul_assoc]
  gcongr
  apply (norm_sum_le ..).trans
  simp_rw [norm_mul]
  calc
    _ ≤ ∑ i, ‖yen (v.drive a) (aliasAt p i)‖*c := Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
    _ = _ := by simp_rw [mul_one, ← Finset.sum_mul]; change _ = ‖∑ i, d i‖*c; rw [show (∑ i, d i)= ((∑ i, ‖yen (v.drive a) (aliasAt p i)‖:ℝ):ℂ) by exact_mod_cast Finset.sum_congr rfl (fun i _=>hc i)]; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
end YM.Extension.UV.Linear
