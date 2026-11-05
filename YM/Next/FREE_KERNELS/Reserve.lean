import YM.Next.FREE_KERNELS.Feed

/-!
# Uniform cube estimates for the split covariance

Count actual alias and earlier depth contributions. These estimates depend on
the smoothing index, never on history length or period; no scheduling
inequality on the L sizes (beyond odd and ≥3) needed yet.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

lemma decay_negate {L : Side} (ho : Odd L.val) (t : ℕ) (l : Site L) : decay t (-l)=decay t l := by
  unfold decay mix up; simp only [lift_negate _ ho, Pi.neg_apply, Int.natAbs_neg]
@[simp] lemma decay_zero (L : Side) (t : ℕ) : decay t (0 : Site L)=1 := by simp [decay,mix,up]
lemma narrow_neg (p : Momentum) (M : Side) : narrow M (-p)=-narrow M p := by simp [narrow]
lemma narrow_real (M : Side) {p : Momentum} (hp : physical p) : physical (narrow M p) := by
  rw [← alias_zero_eq]; exact alias_real hp _

variable {ι : Type*}

lemma rail_cost (L : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) (a : ι → Axis) :
    Moderate (fun i => (up (l i) (a i))⁻¹) fun i p => rail (L i) (aliasAt p (l i) (a i)) := by
  obtain ⟨B,hB,h⟩ := alias_rail
  refine ⟨zone,B,zone_pos,hB,fun i => ⟨fun p _ => ?_, fun p hp => (h (L i) (ho i) p hp _ _).1⟩⟩
  exact ((rail_differentiable (L i)).differentiableAt).comp p (by unfold aliasAt; fun_prop)
lemma rail_root (L : ι → Side) (a : ι → Axis) : Firm (fun _ : ι => 1) fun i p => rail (L i) (narrow (L i) p (a i)) := by
  refine ⟨zone,plankMin,zone_pos,plankMin_pos,fun i p hp => ?_⟩
  dsimp only
  rw [mul_one]; apply rail_lower
  rw [narrow_apply, norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos _).ne']; exact zone_in_disk _ (mem_cube_real hp zone_pos) _

namespace Train
variable {j : ℕ}

lemma drive_prop (v : ι → Train j) (l : ∀ i, Site (v i).mass) (a : ι → Axis) :
    Moderate (fun i => decay j (l i)) fun i p => (v i).drive (a i) (aliasAt p (l i)) := by
  unfold drive
  apply ((smooth_cost v l).mul (rail_cost (fun i => (v i).mass) (fun i => (v i).mass_odd) l a)).raise_price
  exact fun i => mul_le_of_le_one_right (decay_pos ..).le (inv_le_one_of_one_le₀ (up_ge ..))

lemma drive_yen (v : ι → Train j) (l : ∀ i, Site (v i).mass) (a : ι → Axis) :
    Moderate (fun i => decay j (l i)) fun i p => yen ((v i).drive (a i)) (aliasAt p (l i)) := by
  have he := drive_prop v l a
  have hh := (drive_prop v (fun i => -l i) a).reverse
  have hh' : Moderate (fun i => decay j (l i)) (fun i p => (v i).drive (a i) (-aliasAt p (l i))) := by
    simpa only [decay_negate ((v _).mass_odd),alias_reverse _ ((v _).mass_odd)] using hh
  exact (he.mul hh').raise_price fun i => mul_le_of_le_one_right (decay_pos ..).le (decay_le_one ..)

lemma gaps (v : ι → Train j) : Moderate (fun _ : ι => 1) fun i p => (v i).smooth (narrow (v i).mass p) := by
  simpa only [alias_zero_eq,decay_zero] using smooth_cost v fun i => 0
lemma gaps_root (v : ι → Train j) : Firm (fun _ : ι => 1) fun i p => (v i).smooth (narrow (v i).mass p) := by
  obtain ⟨c,hc,he⟩ := smooth_lower j
  exact ⟨zone,c,zone_pos,hc,fun i p h => (mul_one c).trans_le (he _ p h)⟩

lemma lid_cost (v : ι → Train j) (a : ι → Axis) : Moderate (fun _ : ι => 1) fun i => (v i).lid (a i) := by
  have he := drive_yen v (fun i => 0) a
  unfold lid
  simpa only [alias_zero_eq,decay_zero] using he
lemma lid_root (v : ι → Train j) (a : ι → Axis) : Firm (fun _ : ι => 1) fun i => (v i).lid (a i) := by
  obtain ⟨η,c,hp,hc,h⟩ := gaps_root v
  obtain ⟨θ,b,hq,hb,g⟩ := rail_root (fun i => (v i).mass) a
  refine ⟨min η θ,(c*b)^2,lt_min hp hq,pow_pos (mul_pos hc hb) _,fun i p hy => ?_⟩
  have hh (p : Momentum) (hh : p ∈ realCube (min η θ)) : c*b ≤ ‖(v i).drive (a i) (narrow (v i).mass p)‖ := by
    obtain he := h i p (realCube_mono (min_le_left ..) hh)
    obtain hd := g i p (realCube_mono (min_le_right ..) hh)
    unfold drive; rw [norm_mul]; apply mul_le_mul _ _ hb.le (norm_nonneg _)
    · simpa only [mul_one] using he
    simpa only [mul_one] using hd
  unfold lid yen
  dsimp only; rw [mul_one,norm_mul,pow_two,← narrow_neg]; exact mul_le_mul (hh p hy) (hh _ (realCube_neg hy)) (mul_pos hc hb).le (norm_nonneg _)

lemma high_cube (hj : 4≤j) (v : ι → Train j) (a : ι → Axis) : Moderate (fun _ : ι => 1) fun i => (v i).high (a i) := by
  unfold high
  let L := fun i => (v i).mass
  let s := fun i : ι => Finset.univ.erase (0 : Site (L i))
  have hm : ∃ B : ℝ, 0<B ∧ ∀ i, ∑ l∈s i, decay 2 l ≤ B*1 := by
    obtain ⟨C,hC,h⟩ := decay_cost; refine ⟨C,hC,fun i => ?_⟩
    rw [mul_one]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (s i)) (fun l _ _ => (decay_pos ..).le)).trans (h _)
  let π := fun x : Σ i, {k // k ∈ s i} => x.1
  let L' := L ∘ π
  let F (x : ι) (l : Site (L x)) (p : Momentum) := yen ((v x).drive (a x)) (aliasAt p l)*(blow 1 p l)⁻¹
  apply Moderate.sum_family s (fun _ => decay 2) hm F
  let u := fun x : Σ i, {k // k∈s i} => x.2.val
  have hx (i) : Odd (L' i).val := (v (π i)).mass_odd
  have ht (i) : u i ≠ 0 := (Finset.mem_erase.mp i.2.property).1
  have hb := (blow_control L' (fun _ => 1) hx u).inv (blow_firm L' (fun _ => 1) hx u ht)
    (fun i => pow_pos (grade_pos (u i)) _)
  apply ((drive_yen (v ∘ π) u (a ∘ π)).mul hb).raise_price
  intro i
  exact (mul_le_of_le_one_right (decay_pos ..).le (inv_le_one_of_one_le₀ (one_le_pow₀ (grade_ge _)))).trans (decay_anti _ (by omega))

lemma feed_budget (hj : 4≤j) (v : ι → Train j) (a : ι → Axis) : Moderate (fun i => (((v i).mass.val:ℝ)^2)⁻¹)
    fun i => feed (v i) (a i) (fun _ => 1) := by
  unfold feed shuttle; simp only [mul_one]
  let L := fun i => (v i).mass
  have hm : ∃ B : ℝ, 0<B ∧ ∀ i : ι, ∑ l : Site (L i), decay 2 l ≤ B*1 := by
    obtain ⟨C,hC,h⟩ := decay_cost; exact ⟨C,hC,fun i => by rw [mul_one]; exact h _⟩
  let F (i : ι) (l : Site (L i)) (p : Momentum) := yen ((v i).drive (a i)) (aliasAt p l)
  have hb : Moderate (fun _ : ι => 1) fun i p => ∑ l, F i l p := by
    apply Moderate.sum_family (fun _ => Finset.univ) (fun _ => decay 2) hm
    let π := fun x : Σ i, {l : Site (L i) // l ∈ (Finset.univ : Finset _)} => x.1
    exact (drive_yen (v ∘ π) (fun i => i.2.val) (a ∘ π)).raise_price fun i => decay_anti _ (by omega)
  have hu : Moderate (fun i => (((L i).val:ℝ)^2)⁻¹) fun i (_ : Momentum) => (((L i).val:ℂ)^2)⁻¹ := by
    apply Moderate.bounded_const _ 1 one_pos; intro i; rw [norm_inv,norm_pow,Complex.norm_natCast]; simp
  simpa only [F, mul_one] using hu.mul hb

def tapMoney (l : List (Train j)) := (l.map fun i => ((i.mass.val:ℝ)^2)⁻¹).sum
lemma hopMoney (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (l : List (Train P.J)) :
    tapMoney (l.map (hop P h h'))=((P.L.val:ℝ)^2)⁻¹ * tapMoney l := by
  induction l with
  | nil => simp [tapMoney]
  | cons b l ih =>
    change ((((P.L*b.mass).val:ℝ)^2)⁻¹ + tapMoney (l.map (hop P h h')))=((P.L.val:ℝ)^2)⁻¹ * (((b.mass.val:ℝ)^2)⁻¹ + tapMoney l)
    rw [mul_side_real,ih,mul_pow,mul_inv]; ring
lemma tap_safe (v : Train j) : tapMoney v.nozzle ≤ 2 := by
  induction v with
  | top _ => simp [tapMoney,nozzle]
  | hop P h h' v ih =>
    rw [nozzle]
    change (((((1:Side).val):ℝ)^2)⁻¹ + tapMoney (v.nozzle.map (hop P h h'))) ≤ _
    rw [hopMoney]
    have he : (3:ℝ) ≤ P.L.val := by exact_mod_cast P.coarse
    have hl : 9 ≤ (P.L.val:ℝ)^2 := by nlinarith
    have hu := mul_le_mul_of_nonneg_left ih (show 0≤((P.L.val:ℝ)^2)⁻¹ by positivity)
    norm_num
    have ht : ((P.L.val:ℝ)^2)⁻¹*2 ≤ 1 := by rw [inv_mul_eq_div, div_le_one (by positivity)]; linarith
    linarith

lemma noise_budget (hj : 4≤j) (v : ι → Train j) (a : ι → Axis) : Moderate (fun _ : ι => 1) fun i => levelNoise (v i) (a i) := by
  obtain ⟨η,C,he,hc,h⟩ := feed_budget hj (fun i : (Train j) × Axis => i.1) (fun i => i.2)
  refine ⟨η,C*2,he,by positivity,fun i => ?_⟩
  have hm (l : List (Train j)) : SafeCube η (C*tapMoney l) (stream l (a i)) := by
    induction l with
    | nil => simp [tapMoney]; exact ⟨fun _ _ => differentiableAt_const _,fun _ _ => (norm_zero).le⟩
    | cons b l ih =>
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · have heq (l a') : stream (b :: l) a'=fun p => feed b a' (fun _ => 1) p+stream l a' p := by funext p; simp [stream]
        rw [heq]
        exact ((h (b,a i)).hol p hp).add (ih.hol p hp)
      change ‖feed b (a i) (fun _ => 1) p + stream l (a i) p‖ ≤ C*(((b.mass.val:ℝ)^2)⁻¹ + tapMoney l)
      rw [mul_add]; exact (norm_add_le ..).trans (add_le_add ((h (b,a i)).bound p hp) (ih.bound p hp))
  exact (hm (v i).nozzle).mono le_rfl ((mul_le_mul_of_nonneg_left (tap_safe (v i)) hc.le).trans (mul_one _).ge)

lemma drain_reserve (k : ℝ) (hj : 4≤j) (v : ι → Train j) (a : ι → Axis) : Moderate (fun _ : ι => 1) fun i => drain k (v i) (a i) := by
  unfold drain
  have hm := (Moderate.const ((k:ℂ)⁻¹)).mul (noise_budget hj v a)
  simp only [mul_one] at hm; exact (high_cube hj v a).add hm
end Train
end YM.Next.Free
