import YM.Exterior.Initial
import YM.Next.FREE_KERNELS.AliasWeights


/-!
# The scaled Laplacian denominator

Real ellipticity on the punctured cube, uniform analytic inverse *only on
higher aliases*. No statement inferring absence of a complex null cone from
real ellipticity. Cumulative singular symbols themselves will not be used as
genuine Gaussians at the harmonic mesh point.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

/-- Width of an initial complex cube. -/
def zone := Real.pi/4
lemma zone_pos : 0 < zone := by unfold zone; positivity

def domainRadius := 3*Real.pi/2
lemma domainRadius_pos : 0 < domainRadius := by unfold domainRadius; positivity
lemma zone_in_disk (p : Momentum) (hp : p ∈ cube zone) (i : Axis) : ‖p i‖ ≤ domainRadius := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have h1 := hp.1 i; have h2 := hp.2 i
  unfold zone at *; unfold domainRadius; linarith

def chip (z : ℂ) := Complex.exp (Complex.I*z)-1

@[simp] lemma chip_origin : chip 0 = 0 := by simp [chip]

structure Tracker where
  low : ℝ
  high : ℝ
  low_pos : 0<low
  high_pos : 0<high
  below z : ‖z‖ ≤ domainRadius → low*‖z‖ ≤ ‖chip z‖
  above z : ‖z‖ ≤ domainRadius → ‖chip z‖ ≤ high*‖z‖

private lemma trackable : Nonempty Tracker := by
  let K := closedBall (0 : ℂ) domainRadius
  have hx : K ∈ 𝓝 0 := closedBall_mem_nhds _ domainRadius_pos
  have hc : IsCompact K := isCompact_closedBall ..
  have hi : Differentiable ℂ chip := by unfold chip; fun_prop
  have hs : ContinuousOn (dslope chip 0) K := (continuousOn_dslope hx).mpr ⟨hi.continuous.continuousOn,hi 0⟩
  have he (z : ℂ) : z * dslope chip 0 z = chip z := by simpa using sub_smul_dslope chip 0 z
  have hn (z : ℂ) (hz : z ∈ K) : dslope chip 0 z ≠ 0 := by
    by_cases h : z=0
    · subst z
      have he : HasDerivAt chip Complex.I 0 := by
        have hh := ((hasDerivAt_id' (0 : ℂ)).const_mul Complex.I).cexp.sub_const 1
        unfold chip; simpa only [mul_one,one_mul,mul_zero,zero_mul,Complex.exp_zero] using hh
      rw [dslope_same,he.deriv]; exact Complex.I_ne_zero
    intro hb
    have hh := he z
    rw [hb,mul_zero,chip] at hh
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp hh.symm)
    have hv : k ≠ 0 := by
      intro h0; rw [h0] at hk
      simp only [Int.cast_zero,zero_mul] at hk; exact mul_ne_zero Complex.I_ne_zero h hk
    have ht : ‖z‖ = (k.natAbs:ℝ)*(2*Real.pi) := by
      have hm := congr_arg (‖·‖) hk
      simpa only [norm_mul,Complex.norm_I,Real.norm_eq_abs,Complex.norm_real,
        Complex.norm_ofNat,Complex.norm_intCast,abs_of_pos Real.pi_pos, abs_nat,mul_one,one_mul] using hm
    have hu : 1 ≤ k.natAbs := by omega
    have hw : (1:ℝ) ≤ k.natAbs := by exact_mod_cast hu
    have hw' := mul_le_mul_of_nonneg_right hw (by positivity : 0 ≤ 2 * Real.pi)
    have hq : ‖z‖≤domainRadius := by simpa [K] using hz
    have hπ := Real.pi_pos; unfold domainRadius at hq; linarith
  let f := dslope chip 0
  have hh : K.Nonempty := ⟨0,mem_of_mem_nhds hx⟩
  obtain ⟨a,ha,ha'⟩ := hc.exists_isMinOn hh hs.norm
  obtain ⟨b,hb,hb'⟩ := hc.exists_isMaxOn hh hs.norm
  refine ⟨⟨‖f a‖,‖f b‖,norm_pos_iff.mpr (hn a ha),norm_pos_iff.mpr (hn b hb),fun z hz => ?_,fun z hz => ?_⟩⟩
  · rw [← he, norm_mul,mul_comm]
    exact mul_le_mul_of_nonneg_left (ha' (show z∈K by simpa [K] using hz)) (norm_nonneg z)
  rw [← he,norm_mul,mul_comm]; exact mul_le_mul_of_nonneg_right (hb' (show z∈K by simpa [K] using hz)) (norm_nonneg z)

def meter : Tracker := Classical.choice trackable

lemma flip_chip (z : ℂ) : star (chip z)=chip (-star z) := by
  unfold chip; simp only [Complex.star_def, map_sub,map_one,← Complex.exp_conj, map_mul,Complex.conj_I,
    neg_mul,mul_neg]

lemma scaled_alias_upper {L : Side} (l : Site L) {p : Momentum} (hp : p ∈ cube zone) (i : Axis) :
    (L.val:ℝ)*‖aliasAt p l i‖ ≤ (2*Real.pi)*up l i := by
  rw [alias_value,norm_div,Complex.norm_natCast, mul_div_cancel₀ _ (side_pos L).ne']
  calc
    _ ≤ ‖p i‖+‖2*(Real.pi:ℂ)*(lift l i)‖ := norm_add_le ..
    _ ≤ _ := by
      have he := zone_in_disk p hp i
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos,Complex.norm_intCast, abs_nat]
      unfold up domainRadius at *; norm_num; nlinarith [Real.pi_pos]

lemma scaled_alias_lower {L : Side} (l : Site L) {p : Momentum} (hp : p ∈ cube zone) (i : Axis)
    (hi : lift l i ≠ 0) : (Real.pi/4)*up l i ≤ (L.val:ℝ)*‖aliasAt p l i‖ := by
  have he := alias_re p l i
  let x := (lift l i:ℝ)
  have ht : (2*Real.pi)*|x| ≤ (L.val:ℝ)*‖aliasAt p l i‖ + |(p i).re| := calc
    _ = |(L.val:ℝ)*(aliasAt p l i).re-(p i).re| := by rw [he,add_sub_cancel_left,abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    _ ≤ _ := (abs_sub ..).trans (by rw [abs_mul,abs_of_pos (side_pos L)]; exact add_le_add_left (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (side_pos L).le) _)
  unfold x at *; rw [abs_nat] at ht
  have h1 : (1:ℝ)≤ (lift l i).natAbs := by exact_mod_cast (show 1≤ (lift l i).natAbs by omega)
  have hq := hp.2 i; unfold up; unfold zone at hq; nlinarith [Real.pi_pos]

def narrow (M : Side) (p : Momentum) : Momentum := (M.val:ℂ)⁻¹ • p

lemma alias_zero_eq (p : Momentum) (M : Side) : aliasAt p (0 : Site M)=narrow M p := by
  simp [aliasAt,narrow]

lemma narrow_apply (M : Side) (p : Momentum) (i : Axis) : narrow M p i=p i/(M.val:ℂ) := by
  simp [narrow,div_eq_mul_inv,mul_comm]

def seedQ (M : Side) (p : Momentum) (i : Axis) : ℂ := (M.val:ℂ)*chip (narrow M p i)

def divisor (M : Side) (p : Momentum) := ∑ i, seedQ M p i * seedQ M (-p) i

lemma seedQ_cont (M : Side) (i : Axis) : Differentiable ℂ (fun p => seedQ M p i) := by
  unfold seedQ narrow chip; fun_prop

lemma seedQ_size (M : Side) (p : Momentum) (hp : p ∈ cube zone) (i : Axis) :
    meter.low*‖p i‖ ≤ ‖seedQ M p i‖ ∧ ‖seedQ M p i‖ ≤ meter.high*‖p i‖ := by
  have hM := side_pos M
  have ht : ‖narrow M p i‖ = ‖p i‖/(M.val:ℝ) := by rw [narrow_apply,norm_div,Complex.norm_natCast]
  have he : ‖p i‖ ≤ domainRadius := zone_in_disk p hp i
  have hm : ‖narrow M p i‖ ≤ domainRadius := by rw [ht]; exact (div_le_self (by positivity) (by exact_mod_cast M.property)).trans he
  have hu : ‖p i‖=(M.val:ℝ)*‖narrow M p i‖ := by rw [ht,mul_div_cancel₀ _ hM.ne']
  unfold seedQ
  rw [hu,norm_mul,Complex.norm_natCast,mul_left_comm,mul_left_comm meter.high];
  exact ⟨mul_le_mul_of_nonneg_left (meter.below _ hm) hM.le,mul_le_mul_of_nonneg_left (meter.above _ hm) hM.le⟩

lemma seedQ_flip (M : Side) (p : Momentum) (i : Axis) : seedQ M (-star p) i = star (seedQ M p i) := by
  simp only [seedQ,narrow_apply,star_mul,flip_chip]
  simp [mul_comm,neg_div]

def lengthSq (p : Momentum) : ℝ := ∑ i, ‖p i‖ ^ 2

lemma lengthSq_pos {p : Momentum} (hp : p≠0) : 0 < lengthSq p := by
  unfold lengthSq
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hp
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum (f:=fun i : Axis => ‖p i‖^2) (fun i _ => by positivity) (Finset.mem_univ i))

lemma divisor_normSq (M : Side) {p : Momentum} (hp : physical p) :
    divisor M p=((∑ i : Axis, ‖seedQ M p i‖^2 : ℝ):ℂ) := by
  unfold divisor
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show seedQ M (-p) i=star (seedQ M p i) from (by have h := seedQ_flip M p i; rw [show star p=p from hp] at h; exact h), Complex.star_def, Complex.mul_conj,← Complex.sq_norm]
  norm_cast

lemma divisor_real_bounds (M : Side) {p : Momentum} (hp : p ∈ realCube zone) :
    meter.low^2*lengthSq p ≤ (divisor M p).re ∧ (divisor M p).re ≤ meter.high^2*lengthSq p := by
  rw [divisor_normSq M hp.1,Complex.ofReal_re]
  unfold lengthSq; rw [Finset.mul_sum,Finset.mul_sum]
  have he (i : Axis) := seedQ_size M p (mem_cube_real hp zone_pos) i
  constructor
  · exact Finset.sum_le_sum fun i _ => by rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg meter.low_pos.le (norm_nonneg _)) (he i).1 2
  exact Finset.sum_le_sum fun i _ => by rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (he i).2 2

lemma divisor_ne (M : Side) {p : Momentum} (hp : p ∈ realCube zone) (he : p ≠ 0) :
    divisor M p ≠ 0 := by
  have hh := lt_of_lt_of_le (mul_pos (pow_pos meter.low_pos 2) (lengthSq_pos he)) (divisor_real_bounds M hp).1
  exact fun h => by simp_all

@[simp] lemma divisor_origin (M : Side) : divisor M 0 = 0 := by simp [divisor,seedQ,narrow]



/-- Denominator at a one-step scaled alias with an additional prior
dilation (set M=1 for the first blocking). -/
def blow (M : Side) (p : Momentum) {L : Side} (l : Site L) := (L.val:ℂ)^2*divisor M (aliasAt p l)

lemma blow_zero (p : Momentum) (M L : Side) : blow M p (0 : Site L)=divisor (L*M) p := by
  unfold blow divisor seedQ
  simp_rw [alias_zero_eq,narrow_apply]
  simp only [Pi.neg_apply,mul_side_complex]
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [narrow_apply]
  simp_rw [show ∀ a b : ℂ, -(a/b)=-a/b from fun _ _ => (neg_div ..).symm,div_div]
  ring

variable {ι : Type*}

lemma seed_control (M : ι → Side) (a : ι → Axis) : Moderate (fun _ : ι => 1) fun i p => seedQ (M i) p (a i) := by
  refine ⟨zone,meter.high*domainRadius,zone_pos,mul_pos meter.high_pos domainRadius_pos,
    fun i => ⟨fun p _ => seedQ_cont _ _ p,fun p h => ?_⟩⟩
  rw [mul_one]; exact (seedQ_size _ p h _).2.trans (mul_le_mul_of_nonneg_left (zone_in_disk p h _) meter.high_pos.le)

lemma divisor_control (M : ι → Side) : Moderate (fun _ : ι => 1) fun i p => divisor (M i) p := by
  unfold divisor
  apply Moderate.sum _ _ (fun _ => zero_le_one)
  intro a _; have he := seed_control M (fun _ => a)
  simpa only [mul_one] using he.mul he.reverse

lemma scaled_seed (L M : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) (a : ι → Axis) :
    Moderate (fun i => up (l i) (a i)) fun i p => ((L i).val:ℂ)*seedQ (M i) (aliasAt p (l i)) (a i) := by
  refine ⟨zone,meter.high*(2*Real.pi),zone_pos,mul_pos meter.high_pos (by positivity),fun i => ⟨fun p _ => ?_,fun p h => ?_⟩⟩
  · exact DifferentiableAt.const_mul (((seedQ_cont (M i) _).differentiableAt).comp p (by unfold aliasAt; fun_prop)) _
  have hb := (seedQ_size (M i) _ (alias_in_cube zone_pos h (l i) (ho i)) (a i)).2
  dsimp only
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ ((L i).val:ℝ)*(meter.high * ‖aliasAt p (l i) (a i)‖) := mul_le_mul_of_nonneg_left hb (side_pos _).le
    _ ≤ _ := by rw [mul_left_comm,mul_assoc]; exact mul_le_mul_of_nonneg_left (scaled_alias_upper (l i) h _) meter.high_pos.le

lemma blow_control (L M : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) :
    Moderate (fun i => grade (l i) ^ 2) fun i p => blow (M i) p (l i) := by
  have he (i : ι) (p) : blow (M i) p (l i) =
      ∑ a, (((L i).val:ℂ)*seedQ (M i) (aliasAt p (l i)) a) * (((L i).val:ℂ)*seedQ (M i) (-aliasAt p (l i)) a) := by
    unfold blow divisor; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
  simp_rw [he,pow_two]
  apply Moderate.sum _ _ (fun i => mul_nonneg (grade_pos _).le (grade_pos _).le)
  intro a _
  apply Moderate.mul ((scaled_seed L M ho l (fun _ => a)).raise_price (fun i => up_le ..))
  have he := ((scaled_seed L M ho (fun i => -l i) (fun _ => a)).raise_price (fun i => up_le ..)).reverse
  simpa only [alias_reverse _ (ho _),grade,pdist_neg] using he

lemma blow_firm (L M : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) (hi : ∀ i, l i ≠ 0) :
    Firm (fun i => grade (l i)^2) fun i p => blow (M i) p (l i) := by
  refine ⟨zone,(meter.low*zone)^2,zone_pos,pow_pos (mul_pos meter.low_pos zone_pos) _,fun i p hp => ?_⟩
  let q := aliasAt p (l i)
  have hh : q ∈ realCube zone := alias_in_real zone_pos hp _ (ho i)
  have hk := (divisor_real_bounds (M i) hh).1
  obtain ⟨a,ha⟩ := hit_grade (l i)
  let r : ℝ := ((L i).val:ℝ)
  have hu := grade_gt (hi i)
  have hx := scaled_alias_lower (l i) (mem_cube_real hp zone_pos) a (by intro h; simp_all [up])
  change zone*up (l i) a ≤ r * ‖q a‖ at hx
  unfold blow
  dsimp only
  rw [ha,norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ = meter.low^2*((zone*up (l i) a)^2) := by ring
    _ ≤ meter.low^2*((r * ‖q a‖)^2) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos zone_pos (up_pos ..)).le hx _) (by positivity)
    _ = r^2*(meter.low^2* ‖q a‖^2) := by ring
    _ ≤ r^2 * (meter.low^2*lengthSq q) := by
      gcongr; exact Finset.single_le_sum (f:=fun i : Axis => ‖q i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hk.trans (Complex.re_le_norm _)) (by positivity)
end YM.Next.Free
