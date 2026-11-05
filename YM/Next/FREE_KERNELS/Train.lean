import YM.Next.FREE_KERNELS.Lines


/-!
# Uniform cumulative filters (variable J)

Every finite history from the given index, no bound on dilation product or
number of steps. Extra smoothing boxes enter the filter product at smaller
and smaller scaled lengths; this is important also on complex poles.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

def area (L : Side) (p : Momentum) := ∏ i, plank L (p i)

/-- A raw linear history; before any profile prices, delays or choice
of contours for the nonlinearity. -/
inductive Train : ℕ → Type where
| top (j : ℕ) : Train j
| hop {j : ℕ} (P : RG.Patch) (mono : j≤P.J) (gentle : P.J≤j+1) (uphill : Train P.J) : Train j

namespace Train

def mass {j} : Train j → Side
| top _ => 1
| hop P _ _ v => P.L*v.mass

def extra {j} (v : Train j) (p : Momentum) : ℂ := match v with
| top _ => 1
| hop P _ _ v => area (P.L*v.mass) p ^ (P.J-j)*extra v p

def smooth {j} (v : Train j) (p : Momentum) := (area v.mass p)^j * v.extra p

lemma mass_odd {j} (v : Train j) : Odd v.mass.val := by
  induction v with
  | top j => exact odd_one
  | hop P _ _ v ih => exact P.odd_side.mul ih

lemma bind {j : ℕ} (P : RG.Patch) (h : j ≤ P.J) (h' : P.J ≤ j+1) (v : Train P.J) (p : Momentum) :
    (hop P h h' v).smooth p=area P.L (v.mass.val • p)^P.J * v.smooth p := by
  have he : area (P.L*v.mass) p= area P.L (v.mass.val • p)*area v.mass p := by
    unfold area; rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply,nsmul_eq_mul]; exact (plank_bind _ _ P.odd_side v.mass_odd _).symm
  simp only [smooth,mass,extra, ← mul_assoc,← pow_add, Nat.add_sub_of_le h]; rw [he,mul_pow]

lemma area_period (L : Side) (p : Momentum) (x : Cover) : area L (p+reciprocal x)=area L p := by
  simp only [area,Pi.add_apply,reciprocal, plank_repeat]
lemma smooth_period {j} (v : Train j) (p : Momentum) (x : Cover) : v.smooth (p+reciprocal x)=v.smooth p := by
  have he : v.extra (p+reciprocal x)=v.extra p := by
    induction v with
    | top _ => rfl
    | hop P h h' v ih => rw [extra, extra, ih,area_period]
  rw [smooth,smooth,he,area_period]

lemma area_signed (L : Side) (ho : Odd L.val) (p : Momentum) (s : Signed) : area L (s.act p)=area L p := by
  unfold area; rw [← Equiv.prod_comp s.perm (fun i => plank L (s.act p i))]
  refine Finset.prod_congr rfl fun i _ => ?_; rw [Signed.act_at]; split <;> simp [plank_even L ho]
lemma smooth_signed {j} (v : Train j) (p : Momentum) (s : Signed) : v.smooth (s.act p)=v.smooth p := by
  have he : v.extra (s.act p)=v.extra p := by
    induction v with
    | top _ => rfl
    | hop P h h' v ih => rw [extra,extra,ih,area_signed (P.L*v.mass) (P.odd_side.mul v.mass_odd)]
  rw [smooth,smooth,he,area_signed _ v.mass_odd]

lemma area_conj (L : Side) (p : Momentum) : star (area L p)=area L (-star p) := by
  unfold area; simp only [Pi.neg_apply,Pi.star_apply,star_prod,plank_bar]
lemma smooth_conj {j} (v : Train j) (p : Momentum) : star (v.smooth p)=v.smooth (-star p) := by
  have he : star (v.extra p)=v.extra (-star p) := by
    induction v with
    | top _ => simp [extra]
    | hop P h h' v ih => rw [extra,extra,star_mul,star_pow,area_conj,ih]; ring
  rw [smooth,smooth,star_mul,star_pow,he,area_conj]; ring
@[simp] lemma area_zero (L : Side) : area L 0=1 := by simp [area]
@[simp] lemma area_unit (p : Momentum) : area 1 p=1 := by simp [area]
@[simp] lemma smooth_top (j : ℕ) (p : Momentum) : (top j).smooth p=1 := by simp [smooth,mass,extra]
@[simp] lemma smooth_zero {j} (v : Train j) : v.smooth 0=1 := by
  induction v with
  | top j => simp
  | hop P h h' v ih => rw [bind]; simp only [smul_zero,area_zero,one_pow,ih,mul_one]

lemma area_diff (L : Side) : Differentiable ℂ (area L) := by unfold area plank rail twirl; fun_prop
lemma smooth_diff {j} (v : Train j) : Differentiable ℂ v.smooth := by
  have he : Differentiable ℂ v.extra := by
    induction v with
    | top _ => exact differentiable_const _
    | hop P h h' v ih => exact ((area_diff _).pow _).mul ih
  exact ((area_diff _).pow _).mul he

lemma area_height {L M : Side} (p : Momentum) (hp : p ∈ strip (zone/L.val)) :
    ‖area M p‖ ≤ Real.exp (4*zone*(M.val/L.val)) := by
  have hM := side_pos M
  unfold area; rw [norm_prod]
  let a := zone*(M.val/L.val)
  have he (i : Axis) : ‖plank M (p i)‖ ≤ Real.exp a := by
    apply (plank_height M _).trans
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (hp i).le hM.le).trans_eq (by unfold a; ring)
  calc
    _ ≤ ∏ _ : Axis, Real.exp a := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => he i)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]; unfold a; congr 1; norm_num; ring

lemma area_at_root (M L : Side) (hm : M.val ≤ L.val) (p : Momentum) (hp : p ∈ realCube zone) :
    Real.exp (-(4*plankCost*(M.val/L.val))) ≤ ‖area M (narrow L p)‖ := by
  have hL := side_pos L
  let b := -(plankCost*(M.val/L.val))
  have ht (i : Axis) : (narrow L p i).im=0 := by
    apply (physical_iff _).mp _ i
    rw [← alias_zero_eq]; exact alias_real hp.1 _
  have hk (i : Axis) : (L.val:ℝ)*‖narrow L p i‖ ≤ domainRadius := by
    rw [narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ hL.ne']; exact zone_in_disk p (mem_cube_real hp zone_pos) _
  have he (i : Axis) : Real.exp b ≤ ‖plank M (narrow L p i)‖ := principal_plank M L hm _ (ht i) (hk i)
  unfold area; rw [norm_prod]
  calc
    _ = ∏ _ : Axis, Real.exp b := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]; unfold b; congr 1; norm_num; ring
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) (fun i _ => he i)

lemma smaller_mass (L : Side) (P : RG.Patch) {j} (v : Train j) :
    3*(v.mass.val/(L.val:ℝ)) ≤ (P.L*v.mass).val/(L.val:ℝ) := by
  rw [← mul_div_assoc, mul_side_real]
  apply div_le_div_of_nonneg_right _ (side_pos L).le
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast P.coarse) (side_pos _).le
lemma prev_mass (P : RG.Patch) {j} (v : Train j) : v.mass.val ≤ (P.L*v.mass).val := by
  rw [PNat.mul_coe]; exact Nat.le_mul_of_pos_left _ P.L.property

lemma extra_cube {j} (v : Train j) (L : Side) (hL : v.mass.val ≤ L.val)
    (p : Momentum) (hp : p∈ strip (zone/L.val)) : ‖v.extra p‖ ≤ Real.exp (8*zone*(v.mass.val/L.val)) := by
  induction v with
  | top j => simp only [extra,norm_one,Real.one_le_exp_iff]; exact mul_nonneg (mul_nonneg (by norm_num) zone_pos.le) (div_nonneg (by positivity) (by positivity))
  | @hop j P h h' v ih =>
    have hu := smaller_mass L P v
    let K := P.L*v.mass
    have hm := ih ((prev_mass P v).trans hL)
    have hZ := zone_pos
    simp only [extra,mass]
    rcases (show P.J-j=0 ∨ P.J-j=1 by omega) with he|he
    · rw [he,pow_zero,one_mul]
      apply hm.trans (Real.exp_le_exp.mpr ?_); gcongr; exact prev_mass P v
    rw [he,pow_one,norm_mul]
    apply (mul_le_mul (area_height (M:=K) p hp) hm (norm_nonneg _) (Real.exp_pos _).le).trans
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    change 4*zone*(K.val/L.val)+_ ≤ 8*zone*(K.val/L.val)
    change _ ≤ K.val/(L.val:ℝ) at hu
    nlinarith [mul_nonneg hZ.le (show 0≤v.mass.val/(L.val:ℝ) by positivity)]

lemma extra_root {j} (v : Train j) (L : Side) (hL : v.mass.val≤L.val) (p : Momentum) (hp : p∈ realCube zone) :
    Real.exp (-(8*plankCost*(v.mass.val/L.val))) ≤ ‖v.extra (narrow L p)‖ := by
  induction v with
  | top j => simp only [extra,norm_one,Real.exp_le_one_iff]; apply neg_nonpos.mpr; exact mul_nonneg (mul_nonneg (by norm_num) plankCost_pos.le) (by positivity)
  | @hop j P h h' v ih =>
    have hu := smaller_mass L P v
    let K := P.L*v.mass
    have hm := ih ((prev_mass P v).trans hL)
    have hZ := plankCost_pos
    simp only [extra,mass]
    rcases (show P.J-j=0 ∨ P.J-j=1 by omega) with he|he
    · rw [he,pow_zero,one_mul]
      apply (Real.exp_le_exp.mpr ?_).trans hm; gcongr; exact prev_mass P v
    rw [he,pow_one,norm_mul]
    apply (mul_le_mul (area_at_root K L hL p hp) hm (Real.exp_pos _).le (norm_nonneg _)).trans'
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    change -(8*plankCost*(K.val/L.val)) ≤ -(4*plankCost*(K.val/L.val))+_
    change _ ≤ K.val/(L.val:ℝ) at hu
    nlinarith [mul_nonneg hZ.le (show 0≤v.mass.val/(L.val:ℝ) by positivity)]

lemma smooth_upper (j : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (v : Train j) p, p∈cube zone →
    ∀ l : Site v.mass, ‖v.smooth (aliasAt p l)‖ ≤ C*decay j l := by
  obtain ⟨B,hB,h⟩ := alias_rail
  let D := B^4
  have hD : 0 < D := pow_pos hB _
  refine ⟨D^j * Real.exp (8*zone),mul_pos (pow_pos hD _) (Real.exp_pos _),fun v p hp l => ?_⟩
  have ha := extra_cube v _ le_rfl _ (alias_in_cube_precise hp l v.mass_odd).1
  rw [div_self (side_pos _).ne', mul_one] at ha
  have hi : ‖area v.mass (aliasAt p l)‖ ≤ D*(mix l)⁻¹ := by
    unfold area; rw [norm_prod]
    apply (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i (_:i∈Finset.univ) => (h v.mass v.mass_odd p hp l i).2)).trans
    simp [Finset.prod_mul_distrib,D, Axis, mix]
  unfold smooth decay
  rw [norm_mul,norm_pow]
  apply (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hi j) ha (norm_nonneg _) (pow_nonneg (le_trans (norm_nonneg _) hi) _)).trans
  rw [mul_pow, inv_pow]; exact le_of_eq (by ring)

lemma smooth_lower (j : ℕ) : ∃ c : ℝ, 0<c ∧ ∀ (v : Train j) (p : Momentum), p∈realCube zone → c ≤ ‖v.smooth (narrow v.mass p)‖ := by
  let t := Real.exp (-(4*plankCost))
  let u := Real.exp (-(8*plankCost))
  refine ⟨t^j*u,mul_pos (pow_pos (Real.exp_pos _) _) (Real.exp_pos _),fun v p hp => ?_⟩
  have he := extra_root v _ le_rfl p hp
  have hh := area_at_root v.mass v.mass le_rfl p hp
  rw [div_self (side_pos _).ne', mul_one] at he hh
  rw [smooth,norm_mul,norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le hh _) he (Real.exp_pos _).le (pow_nonneg (norm_nonneg _) _)

variable {ι : Type*}

lemma smooth_cost {j : ℕ} (v : ι → Train j) (l : ∀ i, Site (v i).mass) :
    Moderate (fun i => decay j (l i)) fun i p => (v i).smooth (aliasAt p (l i)) := by
  obtain ⟨C,hC,h⟩ := smooth_upper j
  refine ⟨zone,C,zone_pos,hC,fun i => ⟨fun p _ => ?_,fun p hp => h (v i) p hp _⟩⟩
  exact ((smooth_diff (v i)).differentiableAt).comp p (by unfold aliasAt; fun_prop)

end Train
end YM.Next.Free
