import YM.Pert.Fourier.Economy
/-! Shell response for field differences, at nonzero root separation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Finset Lattice Full Metric
open scoped BigOperators
variable {n : Side}
def claw (D : List Axis) (p : Site n) : ℂ := (D.map (fun k=> char p (step k)-1)).prod
lemma multiplier (D : List Axis) (x : Site n) (t : ℝ) (ht : t>0) :
    (topWeight n x * claw D x) = ((n.val:ℂ)^(-4:ℤ)*(t:ℂ)^((D.length:ℤ)-2)) * symbol D t (stretch t x) := by
  have e1 (i : Axis) := (numerator_redef (n:=n) (Lattice.lift x) i t ht)
  have e2 := denominator_eq (n:=n) (Lattice.lift x) t ht
  simp only [wrap_lift] at e1 e2
  have h1 (i : Axis) : (t:ℂ) * numerator t (stretch t x) i = char x (step i) - 1 := e1 i
  change (t:ℂ)^2 * latticeD t (stretch t x) = (delta (moment x):ℂ) at e2
  have eq : ∀ l : List Axis, claw l x= (t:ℂ)^(l.length) * (l.map (numerator t (stretch t x))).prod := by
    intro l; induction l with
    | nil => simp [claw]
    | cons i l ih => change ((char x (step i)-1)*claw l x) = (t:ℂ)^(l.length+1) * (numerator t (stretch t x) i * ((l.map (numerator t (stretch t x))).prod)); rw [ih,←h1,pow_succ]; ring
  rw [topWeight,eq,←e2]
  have ht' : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [zpow_sub₀ ht',zpow_natCast,show ((t:ℂ)^(2:ℤ)) = (t:ℂ)^2 from by norm_cast]
  unfold symbol; rw [mul_inv]; ring

-- Normalized direct fields including contact, before adding the image line.
def joint (h : ℝ) (D : List Axis) (x : Site n) : ℂ := ((h:ℂ)^(-(D.length+2:ℤ))) * ∑ p : Site n, char p x * (topWeight n p * claw D p)
def piece (h s : ℝ) (D : List Axis) (x : Site n) : ℂ := ((h:ℂ)^(-(D.length+2:ℤ))) * ∑ p : Site n, char p x * (topWeight n p * claw D p) * (crop (h*s) p)
def outsideP (h s : ℝ) (D : List Axis) (x : Site n) : ℂ := ((h:ℂ)^(-(D.length+2:ℤ))) * ∑ p : Site n, char p x * (topWeight n p * claw D p) * (1-crop (h*s) p)
lemma clear_joint (h s : ℝ) (D : List Axis) (x : Site n) : joint h D x = piece h s D x + outsideP h s D x := by
  unfold joint piece outsideP; simp only [←mul_add,←Finset.sum_add_distrib]; congr 1; exact Finset.sum_congr rfl (fun i _ => by ring)
def corona (h s : ℝ) (D : List Axis) (x : Site n) := piece h (2*s) D x - piece h s D x
lemma ringM_expand (x : Site n) (D : List Axis) (t : ℝ) (ht : 0<t) : ringM D t x = (↑(crop (2*t) x) - ↑(crop t x)) * symbol D t (stretch t x) := by simp only [ringM,middle,crop,stretch_double ht,Complex.ofReal_sub]
lemma roof_expand (x : Site n) (D : List Axis) (t : ℝ) : roof D t x = (1 - (crop t x:ℂ)) * symbol D t (stretch t x) := by simp only [roof,last,crop,Complex.ofReal_sub,Complex.ofReal_one]
lemma norm_factor {h s : ℝ} (hh : h>0) (hs : s>0) (d : ℕ) : (↑(h:ℝ) : ℂ)^(-((d:ℤ)+2)) * ((n.val:ℂ)^(-4:ℤ)*(↑((h*s:ℝ)):ℂ)^((d:ℤ)-2)) = ((n.val:ℂ)*h)⁻¹^4 * (s:ℂ)^((d:ℤ)-2) := by
  push_cast; rw [show ((n.val:ℂ)^(-4:ℤ))=(n.val:ℂ)⁻¹^4 from by rw [zpow_neg]; exact (inv_pow ..).symm,mul_inv,mul_zpow,mul_pow]
  have e : -(d+2:ℤ)+(d-2)= -4 := by ring
  rw [show ((h:ℂ)^(-((d:ℤ)+2))*((n.val:ℂ)⁻¹^4*((h:ℂ)^((d:ℤ)-2)*(s:ℂ)^((d:ℤ)-2)))) = (h:ℂ)^(-((d:ℤ)+2))*(h:ℂ)^((d:ℤ)-2) * ((n.val:ℂ)⁻¹^4 *(s:ℂ)^((d:ℤ)-2)) from by ring, ←zpow_add₀ (Complex.ofReal_ne_zero.mpr hh.ne'),e,zpow_neg]; rw [show ((h:ℂ)^(4:ℤ))=(h:ℂ)^4 from by norm_cast,inv_pow]; ring
lemma corona_expand (h s : ℝ) (hh : h>0) (hs : s>0) (D : List Axis) (x : Site n) : corona h s D x = (((n.val:ℂ)*h)⁻¹^4*(s:ℂ)^((D.length:ℤ)-2)) * ∑ p : Site n, char p x * ringM D (h*s) p := by
  unfold corona piece; have he := multiplier (n:=n) D (t:=h*s); have hh1 := norm_factor (n:=n) hh hs D.length
  rw [←mul_sub, ←sum_sub_distrib];
  simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl fun p _ => ?_
  rw [he p (mul_pos hh hs),ringM_expand _ _ _ (mul_pos hh hs),←hh1, show h*(2*s)=2*(h*s) from by ring]; ring
lemma outside_expand (h s : ℝ) (hh : h>0) (hs : s>0) (D : List Axis) (x : Site n) : outsideP h s D x = (((n.val:ℂ)*h)⁻¹^4*(s:ℂ)^((D.length:ℤ)-2)) * ∑ p, char p x * roof D (h*s) p := by
  unfold outsideP
  simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl fun p hp => ?_; rw [multiplier _ _ (h*s) (mul_pos hh hs),roof_expand, ←norm_factor hh hs D.length]; ring
lemma max_coord (q : E4) : ∃ i : Axis, ‖q‖ ≤ 2*|q i| := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image (β:=Axis) univ (fun i=> |q i|) univ_nonempty
  refine ⟨i,?_⟩; apply le_of_sq_le_sq _ (by positivity)
  rw [Full.norm_four]; apply le_trans (Finset.sum_le_sum (g:=fun _ => |q i|^2) ?_) _
  · intro j _; exact (show q j^2 ≤ |q i|^2 from by rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (hi _ (mem_univ _)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]; norm_cast; ring_nf; simp
lemma signal (x : Site n) (h : ℝ) (hh : h>0) : ∃ i : Axis, ‖incVec h (Lattice.lift x)‖*(n.val * h)⁻¹ ≤ ‖char (step i) x - 1‖ := by
  let N : ℝ := n.val; have Nh : 0 < N * h := mul_pos (Full.val_pos _) hh
  obtain ⟨i,hi⟩ := max_coord (incVec h (Lattice.lift x))
  refine ⟨i,?_⟩; let r : ℝ := (incVec h (Lattice.lift x)) i
  have hr : r = h*(Lattice.lift x i : ℤ) := rfl
  have hi' : moment x i = (mesh n / h * r) := by rw [moment_apply,hr]; field_simp
  have hr' : |mesh n / h * r| ≤ Real.pi := hi' ▸ Full.moment_cube x i
  rw [Full.swap, Full.char_step,hi',mul_comm (↑(mesh n / h * r):ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hb := Real.mul_le_sin (x:=|mesh n / h * r / 2|) (abs_nonneg _) (by rw [abs_div,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]; exact div_le_div_of_nonneg_right hr' (by norm_num))
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))];
  have hv : Real.sin (|mesh n / h * r / 2|) ≤ |Real.sin (mesh n / h * r / 2)| := by
    generalize mesh n / h * r / 2 = w
    by_cases hw : w<0
    · rw [abs_of_neg hw,Real.sin_neg]; exact neg_le_abs (Real.sin w)
    rw [abs_of_nonneg (le_of_not_gt hw)]; exact le_abs_self _
  grw [← hv, ← hb, hi]
  have he := mesh_val (n:=n)
  rw [abs_div, abs_mul,abs_div,abs_of_pos mesh_pos,abs_of_pos hh, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]; change 2*|r| * (↑n.val * h)⁻¹ ≤ _; dsimp only [mesh]; field_simp; ring_nf; linarith only [abs_nonneg r]
end YM.Pert.Band
