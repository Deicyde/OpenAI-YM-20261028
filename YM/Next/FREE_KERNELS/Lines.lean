import YM.Next.FREE_KERNELS.Chip

/-!
# The line and box filters

Counting normalization is kept explicit: `rail` and `plank` are normalized
only as *averages* (thus still need powers of L in the cochain sums).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

def twirl (z : ℂ) (j : ℤ) := Complex.exp (j*(Complex.I*z))

@[simp] lemma twirl_origin (j : ℤ) : twirl 0 j=1 := by simp [twirl]
@[simp] lemma twirl_nil (z : ℂ) : twirl z 0=1 := by simp [twirl]

lemma twirl_add (z : ℂ) (i j : ℤ) : twirl z (i+j)=twirl z i*twirl z j := by
  simp [twirl,Complex.exp_add,add_mul]
lemma twirl_scale (z : ℂ) (m i : ℤ) : twirl ((m:ℂ)*z) i=twirl z (m*i) := by unfold twirl; push_cast; congr 1; ring
lemma twirl_neg (z : ℂ) (i : ℤ) : twirl (-z) i=twirl z (-i) := by simp [twirl]
lemma twirl_bar (z : ℂ) (i : ℤ) : star (twirl z i)=twirl (-star z) i := by
  unfold twirl; simp only [Complex.star_def,← Complex.exp_conj, map_mul, map_intCast, Complex.conj_I,
    mul_neg,neg_mul]
lemma twirl_period (z : ℂ) (i j : ℤ) : twirl (z+2*(Real.pi:ℂ)*i) j=twirl z j := by
  unfold twirl
  rw [show (j:ℂ)*(Complex.I*(z+2*(Real.pi:ℂ)*i))=(j:ℂ)*(Complex.I*z)+(i*j:ℤ)*(2*Real.pi*Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,mul_one]
lemma twirl_norm (z : ℂ) (j : ℤ) : ‖twirl z j‖=Real.exp (-(j*z.im)) := by simp [twirl,Complex.norm_exp]

def rail (M : Side) (z : ℂ) : ℂ := (M.val:ℂ)⁻¹ * ∑ i∈Finset.range M.val, twirl z i

def mid (M : Side) : ℤ := (M.val/2 : ℕ)

def plank (M : Side) (z : ℂ) := twirl z (-mid M)*rail M z

@[simp] lemma rail_origin (M : Side) : rail M 0=1 := by simp [rail]
@[simp] lemma plank_origin (M : Side) : plank M 0=1 := by simp [plank]
@[simp] lemma rail_unit (z : ℂ) : rail 1 z=1 := by simp [rail]
@[simp] lemma plank_unit (z : ℂ) : plank 1 z=1 := by simp [plank,mid]

lemma rail_chip (M : Side) (z : ℂ) : (M.val:ℂ)*rail M z*chip z=chip ((M.val:ℂ)*z) := by
  unfold rail chip
  rw [← mul_assoc,mul_inv_cancel₀ (side_ne M),one_mul,
    mul_left_comm Complex.I,Complex.exp_nat_mul]
  unfold twirl; simp_rw [Int.cast_natCast,Complex.exp_nat_mul,geom_sum_mul]

lemma rail_bind (L M : Side) (z : ℂ) : rail L ((M.val:ℂ)*z) * rail M z=rail (L*M) z := by
  by_cases h : chip z=0
  · have hz := rail_chip M z
    rw [h,mul_zero] at hz
    have he (z : ℂ) (hz : chip z=0) (L : Side) : rail L z=1 := by
      have ht := sub_eq_zero.mp hz
      unfold rail twirl; simp only [Int.cast_natCast,Complex.exp_nat_mul, ht]; simp [side_ne L]
    rw [he z h,he z h,he _ hz.symm, one_mul]
  apply mul_left_cancel₀ (side_ne (L*M)); apply mul_right_cancel₀ h
  rw [rail_chip,mul_side_complex]
  rw [show (↑L.val:ℂ)*M.val*(rail L ((M.val:ℂ)*z)*rail M z)*chip z=
    (↑L.val:ℂ)*rail L ((M.val:ℂ)*z)*((↑M.val:ℂ)*rail M z*chip z) by ring, rail_chip, rail_chip,mul_assoc]

lemma mid_double (L : Side) (ho : Odd L.val) : 2*mid L+1=L.val := by
  unfold mid
  rcases ho with ⟨v,hv⟩
  omega
lemma plank_bind (L M : Side) (ho : Odd L.val) (ho' : Odd M.val) (z : ℂ) :
    plank L ((M.val:ℂ)*z) * plank M z=plank (L*M) z := by
  have ht : Odd (L*M).val := ho.mul ho'
  have he : (M.val:ℤ)*mid L+mid M = mid (L*M) := by
    have hx := mid_double L ho; have hy := mid_double M ho'; have hz := mid_double (L*M) ht
    rw [PNat.mul_coe,Nat.cast_mul] at hz; nlinarith
  unfold plank
  rw [mul_mul_mul_comm,rail_bind,show twirl ((M.val:ℂ)*z) (-mid L)=twirl z (M.val*(-mid L)) by
    exact_mod_cast twirl_scale z M.val (-mid L),← twirl_add,← he]; simp [add_comm]

lemma plank_centers (M : Side) (z : ℂ) :
    plank M z=(M.val:ℂ)⁻¹ * ∑ i∈Finset.range M.val, twirl z (i-mid M) := by
  unfold plank rail
  rw [mul_left_comm,Finset.mul_sum]; simp_rw [← twirl_add]
  have h (i : ℤ) : -mid M+i=i-mid M := by abel
  simp_rw [h]

lemma plank_even (M : Side) (ho : Odd M.val) (z : ℂ) : plank M (-z)=plank M z := by
  simp_rw [plank_centers,twirl_neg]
  congr 1
  rw [← Finset.sum_range_reflect (fun i : ℕ => twirl z ((i:ℤ)-mid M))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hx := Finset.mem_range.mp hi
  have hy := mid_double M ho
  congr 1; omega

lemma rail_bar (M : Side) (z : ℂ) : star (rail M z)=rail M (-star z) := by
  unfold rail; simp only [star_mul, star_sum, twirl_bar]; simp [mul_comm]
lemma plank_bar (M : Side) (z : ℂ) : star (plank M z)=plank M (-star z) := by
  unfold plank; simp only [star_mul, twirl_bar, rail_bar]; ring

lemma rail_repeat (M : Side) (z : ℂ) (i : ℤ) : rail M (z+2*(Real.pi:ℂ)*i)=rail M z := by simp only [rail,twirl_period]
lemma plank_repeat (M : Side) (z : ℂ) (i : ℤ) : plank M (z+2*(Real.pi:ℂ)*i)=plank M z := by simp only [plank,twirl_period,rail_repeat]
lemma chip_repeat (z : ℂ) (i : ℤ) : chip (z+2*(Real.pi:ℂ)*i)=chip z := by
  unfold chip; have he := twirl_period z i 1; simp [twirl] at he; rw [he]

lemma rail_differentiable (M : Side) : Differentiable ℂ (rail M) := by unfold rail twirl; fun_prop


lemma average_bound (M : Side) {B : ℝ} (f : ℕ → ℂ) (hf : ∀ i∈Finset.range M.val, ‖f i‖ ≤ B) :
    ‖(M.val:ℂ)⁻¹ * ∑ i∈Finset.range M.val, f i‖ ≤ B := by
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (M.val:ℝ)⁻¹ *(M.val * B) := mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ((Finset.sum_le_sum hf).trans_eq (by simp))) (by positivity)
    _ = _ := inv_mul_cancel_left₀ (side_pos M).ne' _

lemma rail_height (M : Side) (z : ℂ) : ‖rail M z‖ ≤ Real.exp (M.val*|z.im|) := by
  apply average_bound _ _
  intro i hi
  rw [twirl_norm]; apply Real.exp_le_exp.mpr
  rw [Int.cast_natCast]
  calc
    _ = (i:ℝ)*-z.im := by ring
    _ ≤ (i:ℝ)*|z.im| := mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hi).le) (abs_nonneg _)

lemma all_centers (M : Side) (i : ℕ) (hi : i<M.val) :
    |((i:ℤ)-mid M:ℤ)| ≤ M.val := by rw [abs_le]; unfold mid; omega

lemma plank_height (M : Side) (z : ℂ) : ‖plank M z‖ ≤ Real.exp (M.val*|z.im|) := by
  rw [plank_centers]; apply average_bound _ _
  intro i hi
  rw [twirl_norm]; apply Real.exp_le_exp.mpr
  calc
    _ ≤ |(((((i:ℤ)-mid M):ℤ):ℝ)*z.im)| := neg_le_abs _
    _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast all_centers M i (Finset.mem_range.mp hi)) (abs_nonneg _)

lemma narrow_norm {M : Side} (z : ℂ) (h : (M.val:ℝ)*‖z‖ ≤ domainRadius) : ‖z‖≤domainRadius := by
  exact ((le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast M.property)).trans h)

def plankMin := min 1 (meter.low / meter.high)
lemma plankMin_pos : 0<plankMin := lt_min one_pos (div_pos meter.low_pos meter.high_pos)
lemma rail_lower (M : Side) (z : ℂ) (h : (M.val:ℝ)*‖z‖ ≤ domainRadius) : plankMin ≤ ‖rail M z‖ := by
  by_cases he : z=0
  · rw [he,rail_origin,norm_one]; exact min_le_left ..
  have hh : ‖(M.val:ℂ)*z‖=(M.val:ℝ)*‖z‖ := by rw [norm_mul,Complex.norm_natCast]
  have hb := meter.below ((M.val:ℂ)*z) (hh.trans_le h)
  rw [hh,← rail_chip,norm_mul,norm_mul,Complex.norm_natCast] at hb
  have hc := meter.above z (narrow_norm z h)
  apply (min_le_right ..).trans
  apply (div_le_iff₀ meter.high_pos).mpr
  apply le_of_mul_le_mul_left _ (side_pos M)
  apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr he)
  have hx := hb.trans (mul_le_mul_of_nonneg_left hc (mul_nonneg (side_pos M).le (norm_nonneg _)))
  linarith

lemma plank_lower (M : Side) (z : ℂ) (h : (M.val:ℝ)*‖z‖ ≤ domainRadius) (hi : z.im=0) :
    plankMin ≤ ‖plank M z‖ := by rw [plank,norm_mul,twirl_norm,hi]; simpa using rail_lower M z h

def plankCost := meter.high * domainRadius / plankMin
lemma plankCost_pos : 0 < plankCost := div_pos (mul_pos meter.high_pos domainRadius_pos) plankMin_pos

/-- Form used on a principal cumulative alias; coefficient 1 (not C) matters
when consuming this estimate repeatedly over a history. -/
lemma principal_plank (M L : Side) (hm : M.val≤L.val) (z : ℂ) (hi : z.im=0)
    (h : (L.val:ℝ)*‖z‖ ≤ domainRadius) : Real.exp (-(plankCost*(M.val/L.val))) ≤ ‖plank M z‖ := by
  have hM := side_pos M; have hL := side_pos L
  let x := (M.val:ℝ)/L.val
  have hm' : (M.val:ℝ)≤L.val := by exact_mod_cast hm
  have hx : x ≤ 1 := by unfold x; rw [div_le_one hL]; exact hm'
  let k := meter.high * domainRadius
  have hk : 0 < k := mul_pos meter.high_pos domainRadius_pos
  have hg : (M.val:ℝ)*‖z‖ ≤ x*domainRadius := by
    have he : ‖z‖ ≤ domainRadius/(L.val:ℝ) := (le_div_iff₀ hL).mpr (mul_comm ‖z‖ _ |>.trans_le h)
    exact (mul_le_mul_of_nonneg_left he hM.le).trans_eq (by unfold x; ring)
  have hg' := hg.trans (mul_le_of_le_one_left domainRadius_pos.le hx)
  have he := plank_lower M z hg' hi
  have hv : ‖plank M z-1‖ ≤ k*x := by
    let f (i : ℕ) := twirl z ((i:ℤ)-mid M)
    have he : plank M z-1=(M.val:ℂ)⁻¹*∑ i∈Finset.range M.val, (f i-1) := by
      rw [plank_centers,Finset.sum_sub_distrib,mul_sub]; unfold f; simp
    rw [he]; apply average_bound _ _
    intro i hi
    let q : ℤ := (i:ℤ)-mid M
    have hb : |(q:ℝ)| ≤ M.val := by exact_mod_cast all_centers M i (Finset.mem_range.mp hi)
    have hh : ‖(q:ℂ)*z‖ ≤ (M.val:ℝ)*‖z‖ := by rw [norm_mul,Complex.norm_intCast]; exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    change ‖twirl z q - 1‖ ≤ _
    rw [show twirl z q-1=chip ((q:ℂ)*z) by unfold chip twirl; ring_nf]
    exact (meter.above _ (hh.trans hg')).trans ((mul_le_mul_of_nonneg_left (hh.trans hg) meter.high_pos.le).trans_eq (by unfold k; ring))
  have hh : 1 ≤ ‖plank M z‖+k*x := by
    have ht := norm_sub_norm_le (1:ℂ) (plank M z)
    rw [norm_one,norm_sub_rev] at ht; linarith
  change Real.exp (-(k/plankMin*x)) ≤ _
  rw [Real.exp_neg,inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have hu := Real.add_one_le_exp (k/plankMin*x)
  have hx' : 0 < x := div_pos hM hL
  have hn := mul_le_mul_of_nonneg_right he (show 0 ≤ k/plankMin*x by exact mul_nonneg (div_nonneg hk.le plankMin_pos.le) hx'.le)
  have hb : plankMin*(k/plankMin*x)=k*x := by field_simp [plankMin_pos.ne']
  linarith [mul_le_mul_of_nonneg_left hu (norm_nonneg (plank M z))]

/-- High-alias upper bound per axis. Retain the full power of the
product of the four coordinate weights. -/
lemma alias_rail : ∃ B : ℝ, 0<B ∧ ∀ L : Side, Odd L.val → ∀ p ∈ cube zone,
    ∀ (l : Site L) (i : Axis), ‖rail L (aliasAt p l i)‖ ≤ B*(up l i)⁻¹ ∧
    ‖plank L (aliasAt p l i)‖ ≤ B*(up l i)⁻¹ := by
  let k := meter.high * domainRadius / (meter.low * zone)
  let h := Real.exp zone
  have hk : 0<k := div_pos (mul_pos meter.high_pos domainRadius_pos) (mul_pos meter.low_pos zone_pos)
  have hh : 1≤h := by unfold h; exact Real.one_le_exp zone_pos.le
  refine ⟨max h (h*k),lt_max_of_lt_left (by unfold h; positivity),fun L ho p hp l i => ?_⟩
  let z := aliasAt p l i
  have hL := side_pos L
  have hq := alias_in_cube_precise hp l ho
  have hc : (L.val:ℝ)*|z.im| ≤ zone := by rw [mul_comm]; exact (le_div_iff₀ hL).mp (hq.1 i).le
  have ht := up_pos l i
  change ‖rail L z‖ ≤ _ ∧ ‖plank L z‖ ≤ _
  by_cases hv : lift l i=0
  · have he : up l i=1 := by simp [up,hv]
    rw [he,inv_one,mul_one]
    exact ⟨((rail_height L z).trans (Real.exp_le_exp.mpr hc)).trans (le_max_left ..),((plank_height L z).trans
      (Real.exp_le_exp.mpr hc)).trans (le_max_left ..)⟩
  have hs := meter.below z (zone_in_disk _ (alias_in_cube zone_pos hp l ho) i)
  have hs' := scaled_alias_lower l hp i hv
  have hr := rail_chip L z
  have hn := congr_arg (fun p : Momentum => p i) (alias_scale p l)
  change (L.val • aliasAt p l) i=_ at hn
  simp only [Pi.smul_apply,nsmul_eq_mul,Pi.add_apply,reciprocal] at hn
  rw [hn, chip_repeat] at hr
  have he : ‖rail L z‖ ≤ k*(up l i)⁻¹ := by
    have hx := zone_in_disk p hp i
    have hy := (meter.above (p i) hx).trans (mul_le_mul_of_nonneg_left hx meter.high_pos.le)
    rw [← hr,norm_mul,norm_mul,Complex.norm_natCast] at hy
    rw [← div_eq_mul_inv,le_div_iff₀ ht]
    apply (le_div_iff₀ (mul_pos meter.low_pos zone_pos)).mpr
    have hg := calc
        meter.low*(zone * up l i) ≤ meter.low*((L.val:ℝ)*‖z‖) := mul_le_mul_of_nonneg_left hs' meter.low_pos.le
        _ ≤ (L.val:ℝ)*‖chip z‖ := by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hs hL.le
    linarith [mul_le_mul_of_nonneg_left hg (norm_nonneg (rail L z))]
  refine ⟨he.trans (mul_le_mul_of_nonneg_right ((le_mul_of_one_le_left hk.le hh).trans (le_max_right ..)) (inv_nonneg.mpr ht.le)),?_⟩
  have hb : ‖twirl z (-mid L)‖ ≤ h := by
    rw [twirl_norm]; apply Real.exp_le_exp.mpr
    have ht : |(-(mid L):ℝ)| ≤ L.val := by exact_mod_cast (show |(-mid L)| ≤ L.val from by obtain hx := all_centers L 0 L.property; simpa using hx)
    push_cast
    calc
      _ ≤ |(-(mid L:ℝ))*z.im| := neg_le_abs _
      _ ≤ _ := (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans hc)
  rw [plank,norm_mul]; apply (mul_le_mul hb he (norm_nonneg _) (one_pos.trans_le hh).le).trans
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (inv_nonneg.mpr ht.le)
end YM.Next.Free
