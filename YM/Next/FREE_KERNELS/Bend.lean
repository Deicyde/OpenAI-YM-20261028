import YM.Next.FREE_KERNELS.Reserve

/-!
# Filling the metric symbol through the Laplacian cone

`bulb = G` and `bend = h`. Positivity & overlap identities proved on the
real enlarged cube including harmonic convention (D excluded at poles). No
attempt to put `1/(sum q²...)` itself in a Width; only the filled
combinations are analytic.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

variable {j : ℕ}

def jewel (M : Side) (p : Momentum) (i : Axis) := seedQ M p i * seedQ M (-p) i

lemma jewel_price (M : Side) (i : Axis) {p : Momentum} (hp : physical p) : Silver (jewel M p i) := by
  have h := seedQ_flip M p i; rw [show star p=p from hp] at h
  rw [jewel,h]; exact Silver.gram _
lemma jewel_one (p : Momentum) (i : Axis) : jewel 1 p i = chip (p i)*chip (-p i) := by
  simp [jewel,seedQ,narrow_apply]

namespace Silver
variable {x y : ℂ}

lemma real_mul (h : Silver x) (y : ℂ) : (x*y).re=x.re*y.re := by rw [← h.of_real]; simp
lemma real_inv (h : Silver x) : x⁻¹.re=x.re⁻¹ := by rw [← h.of_real]; simp
lemma real_div (y : ℂ) (h : Silver x) : (y/x).re = y.re/x.re := by
  rw [div_eq_mul_inv,mul_comm,h.inv.real_mul,h.real_inv]; ring
end Silver

namespace Train

def bulb (k : ℝ) (v : Train j) (p : Momentum) (a : Axis) := v.lid a p+divisor v.mass p*drain k v a p

def halo (v : Train j) (p : Momentum) := yen v.smooth (narrow v.mass p)

def bend (k : ℝ) (v : Train j) (p : Momentum) := (v.halo p)⁻¹-∑ a,
    jewel 1 p a * drain k v a p / (v.lid a p*bulb k v p a)

def rho (k : ℝ) (v : Train j) (p : Momentum) := ∑ a, jewel 1 p a / levelD k v a p

lemma reserve_link (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) :
    (v.halo p≠0 ∧ ∀ a, v.lid a p ≠ 0) := by
  let M := v.mass
  have he (p : Momentum) (h : p ∈ realCube zone) : v.smooth (narrow M p)≠0 ∧ ∀ a, v.drive a (narrow M p)≠0 := by
    obtain ⟨c,hc,hh⟩ := smooth_lower j
    have hg := norm_pos_iff.mp (hc.trans_le (hh v _ h))
    refine ⟨hg, fun a => mul_ne_zero hg ?_⟩
    apply norm_pos_iff.mp; apply plankMin_pos.trans_le (rail_lower M _ _)
    rw [narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos _).ne']; exact zone_in_disk _ (mem_cube_real h zone_pos) _
  obtain ⟨h1,h2⟩ := he _ hp; obtain ⟨h3,h4⟩ := he _ (realCube_neg hp)
  rw [narrow_neg] at h3
  simp_rw [narrow_neg] at h4
  exact ⟨mul_ne_zero h1 h3,fun a => mul_ne_zero (h2 a) (h4 a)⟩

lemma lid_price (v : Train j) (a) {p : Momentum} (hp : physical p) : Silver (v.lid a p) := v.drive_price _ _ (narrow_real v.mass hp)
lemma bulb_cost (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : physical p) (a) : Silver (bulb k v p a) :=
  (v.lid_price _ hp).add ((Silver.chipSq _ hp).mul (drain_cost k hk v _ hp))
lemma bulb_growth (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : physical p) (a : Axis) :
    ‖v.lid a p‖ ≤ ‖bulb k v p a‖ := by
  rw [(v.lid_price _ hp).norm,(bulb_cost k hk _ hp _).norm]
  unfold bulb; rw [Complex.add_re,le_add_iff_nonneg_right]; exact ((Silver.chipSq _ hp).mul (drain_cost k hk _ _ hp)).re_nonneg
lemma bulb_glows (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) (a) : bulb k v p a≠0 :=
    norm_pos_iff.mp ((norm_pos_iff.mpr ((v.reserve_link hp).2 a)).trans_le (bulb_growth k hk _ hp.1 _))

lemma D_bulb (k : ℝ) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) (a) :
    levelD k v a p = bulb k v p a/divisor v.mass p := by
  rw [pole_split,bulb]
  have hh := divisor_ne v.mass hp he; field_simp
lemma D_live (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p∈realCube zone) (he : p≠0) (a) : levelD k v a p ≠0 := by
  rw [D_bulb k v hp he]; exact div_ne_zero (bulb_glows k hk v hp a) (divisor_ne _ hp he)

lemma sourceQ (M : Side) (p : Momentum) (a : Axis) : chip (p a)=rail M (narrow M p a)*seedQ M p a := by
  have he := rail_chip M (narrow M p a); rw [narrow_apply,mul_div_cancel₀ _ (side_ne _)] at he
  rw [seedQ,narrow_apply,← he]; ring
lemma price_sources (v : Train j) (p : Momentum) (a) : jewel 1 p a * v.halo p = jewel v.mass p a * v.lid a p := by
  have he : chip (-p a) = rail v.mass (narrow v.mass (-p) a)*seedQ v.mass (-p) a := sourceQ v.mass (-p) a
  rw [jewel_one, he, sourceQ v.mass p a]
  unfold jewel halo lid yen drive
  -- `seedQ v.mass (-p)` not touched
  rw [show narrow v.mass (-p) a=(-(narrow v.mass p)) a by rw [narrow_neg]]; ring
lemma lift_bend (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) :
    divisor v.mass p*bend k v p=∑ i, jewel 1 p i / bulb k v p i := by
  let M := v.mass
  have he (i : Axis) : jewel M p i*(v.halo p)⁻¹-divisor M p*(
      jewel 1 p i * drain k v i p / (v.lid i p*bulb k v p i)) = jewel 1 p i / bulb k v p i := by
    obtain ⟨hh,hb⟩ := v.reserve_link hp
    have hg := hb i; have hd := bulb_glows k hk v hp i
    rw [show jewel M p i*(v.halo p)⁻¹=jewel 1 p i/v.lid i p by
      field_simp; exact (price_sources v p i).symm.trans (mul_comm ..)]
    field_simp; unfold bulb; ring
  have hu : divisor M p*(v.halo p)⁻¹ = ∑ i, jewel M p i*(v.halo p)⁻¹ := by rw [← Finset.sum_mul]; rfl
  change divisor M p*_=_
  rw [bend,mul_sub,hu,Finset.mul_sum,← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => he i

@[simp] lemma halo_zero (v : Train j) : v.halo 0=1 := by simp [halo,yen,narrow]
@[simp] lemma bulb_zero (k : ℝ) (v : Train j) (a) : bulb k v 0 a=1 := by simp [bulb,lid,yen,narrow,drive]
@[simp] lemma bend_zero (k : ℝ) (v : Train j) : bend k v 0=1 := by simp [bend,jewel_one]

lemma bend_price (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) : Silver (bend k v p) := by
  by_cases he : p=0
  · rw [he,bend_zero]; exact Silver.one
  have hs := divisor_ne v.mass hp he
  have h := lift_bend k hk v hp
  rw [← inv_mul_cancel_left₀ hs (bend k v p), h]
  apply (Silver.chipSq _ hp.1).inv.mul
  exact Silver.sum _ _ (fun i _ => (jewel_price 1 i hp.1).div (bulb_cost k hk v hp.1 i))

/-- A numerical lower bound; only K bounds on the regular `bulb` needed on real cube. -/
lemma bend_strength (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone)
    {C : ℝ} (hC : 0<C) (hh : ∀ i, ‖bulb k v p i‖≤C) :
    min 1 (meter.low^2 / (C*meter.high^2)) ≤ ‖bend k v p‖ := by
  by_cases he : p=0
  · rw [he,bend_zero,norm_one]; exact min_le_left ..
  rw [(bend_price k hk _ hp).norm]
  let g i := bulb k v p i
  let x i := jewel 1 p i
  have hl := (divisor_real_bounds 1 hp).1
  have hu := (divisor_real_bounds v.mass hp).2
  have hb : (divisor 1 p).re = ∑ i, (x i).re := by unfold divisor; rw [Complex.re_sum]; rfl
  have hc := congr_arg Complex.re (lift_bend k hk v hp)
  rw [(Silver.chipSq _ hp.1).real_mul, Complex.re_sum] at hc
  have hd (i : Axis) : (x i).re ≤ C*(x i/g i).re := by
    have hx := jewel_price 1 i hp.1
    have hg : Silver (g i) := bulb_cost k hk _ hp.1 _
    have he' := hg.re_ne (bulb_glows k hk _ hp _)
    rw [hg.real_div,← mul_div_assoc]; apply (le_div_iff₀ he').mpr; rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (hg.norm ▸ hh i) hx.re_nonneg
  have hm := calc
    meter.low^2*lengthSq p ≤ ∑ i, (x i).re := hb ▸ hl
    _ ≤ ∑ i, C*(x i / g i).re := Finset.sum_le_sum fun i _ => hd i
    _ = C*((divisor v.mass p).re * (bend k v p).re) := by rw [← Finset.mul_sum]; exact congr_arg (C*·) hc.symm
    _ ≤ C*(meter.high^2*lengthSq p*(bend k v p).re) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (bend_price k hk _ hp).re_nonneg) hC.le
  apply (min_le_right ..).trans
  apply (div_le_iff₀ (mul_pos hC (pow_pos meter.high_pos 2))).mpr
  apply le_of_mul_le_mul_right _ (lengthSq_pos he)
  linarith
lemma bend_live (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) : bend k v p ≠ 0 := by
  let C := 1+∑ i, ‖bulb k v p i‖
  have hc : 0<C := by unfold C; positivity
  apply norm_pos_iff.mp
  have he (i : Axis) : ‖bulb k v p i‖ ≤ C :=
    (Finset.single_le_sum (f:=fun i => ‖bulb k v p i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans (le_add_of_nonneg_left (by norm_num))
  exact (lt_min one_pos (div_pos (pow_pos meter.low_pos _) (mul_pos hc (pow_pos meter.high_pos _)))).trans_le (bend_strength k hk v hp hc he)
lemma recover_rho (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) :
    rho k v p=divisor v.mass p^2 * bend k v p := by
  rw [pow_two,mul_assoc,lift_bend k hk v hp,Finset.mul_sum]
  unfold rho; refine Finset.sum_congr rfl fun i _ => ?_; rw [D_bulb k v hp he]; simp only [div_div_eq_mul_div]; ring

variable {ι : Type*}
lemma bulb_budget (k : ℝ) (hj : 4 ≤ j) (v : ι → Train j) (a : ι → Axis) :
    Moderate (fun _ : ι => 1) fun i p => bulb k (v i) p (a i) := by
  have he := (divisor_control (fun i => (v i).mass)).mul (drain_reserve k hj v a)
  simp only [mul_one] at he; exact (lid_cost v a).add he
lemma bulb_firm (k : ℝ) (hk : 0<k) (v : ι → Train j) (a : ι → Axis) :
    Firm (fun _ : ι => 1) fun i p => bulb k (v i) p (a i) := by
  obtain ⟨η,c,hp,hb,h⟩ := lid_root v a
  exact ⟨η,c,hp,hb,fun i p hh => (h i _ hh).trans (bulb_growth k hk _ hh.1 _)⟩

lemma halo_pay (v : ι → Train j) : Moderate (fun _ : ι => 1) fun i p => halo (v i) p := by
  have he := gaps v
  simpa only [halo,yen, ← narrow_neg, mul_one] using he.mul he.reverse
lemma halo_firm (v : ι → Train j) : Firm (fun _ : ι => 1) fun i p => halo (v i) p := by
  obtain ⟨η,c,hp,hb,h⟩ := gaps_root v
  refine ⟨η,c*c,hp,mul_pos hb hb,fun i p hh => ?_⟩
  unfold halo yen
  have h1 := h i p hh; have h2 := h i (-p) (realCube_neg hh)
  simp only [mul_one,norm_mul, ← narrow_neg] at *
  exact mul_le_mul h1 h2 hb.le (norm_nonneg _)
lemma bend_budget (k : ℝ) (hk : 0<k) (hj : 4≤j) (v : ι → Train j) :
    Moderate (fun _ : ι => 1) fun i => bend k (v i) := by
  have he := (halo_pay v).inv (halo_firm v) (fun _ => one_pos)
  simp only [inv_one] at he
  unfold bend; apply he.sub
  apply Moderate.sum _ _ (fun _ => zero_le_one)
  intro i _
  let a (_ : ι) := i
  have hjQ := seed_control (fun _ : ι => (1:Side)) a
  have hl := (lid_cost v a).inv (lid_root v a) (fun _ => one_pos)
  have hb := (bulb_budget k hj v a).inv (bulb_firm k hk v a) (fun _ => one_pos)
  have hh := ((hjQ.mul hjQ.reverse).mul (drain_reserve k hj v a)).mul (hb.mul hl)
  simpa only [a, inv_one, mul_one, jewel, div_eq_mul_inv, mul_inv_rev] using hh
lemma bend_firm (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (v : ι → Train j) :
    Firm (fun _ : ι => 1) fun i => bend k (v i) := by
  obtain ⟨η,C,he,hC,h⟩ := bulb_budget k hj (fun x : ι×Axis => v x.1) (fun x => x.2)
  refine ⟨min zone η,min 1 (meter.low^2/(C*meter.high^2)),lt_min zone_pos he,
    lt_min one_pos (div_pos (pow_pos meter.low_pos _) (mul_pos hC (pow_pos meter.high_pos _))),fun i p hh => ?_⟩
  rw [mul_one]; apply bend_strength k hk _ (realCube_mono (min_le_left ..) hh) hC
  exact fun a => ((h (i,a)).bound _ (mem_cube_real (realCube_mono (min_le_right ..) hh) he)).trans_eq (mul_one _)
end Train
end YM.Next.Free
