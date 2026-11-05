import YM.Pert.Fourier.Power
/-! Uniform IR pole budget and finite count on centered grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Lattice Full Finset Set
open scoped BigOperators
variable {n : Side}

def inside (n : Side) (m : ℕ) := univ.filter fun p : Site n => pdist p ≤ m
def talc (m : ℕ) (n : Side) := ∑ p ∈ inside n m, (‖incVec 1 (Lattice.lift p)‖^2)⁻¹
lemma pdist_small (x : Site n) (k : ℕ) (h : x ∈ inside n k) (i : Axis) : |Lattice.lift x i| ≤ (k:ℤ) := by
  have hp : pdist x ≤ k := (mem_filter.mp h).2; have := component_le x i; rw [Int.abs_eq_natAbs]; exact_mod_cast this.trans hp
lemma inside_count (m : ℕ) : ((inside n m).card) ≤ (2*m+1)^4 := by
  apply le_trans (counts (n:=n) (m:ℤ) (fun p hp => pdist_small p m hp))
  have e : (((m:ℤ)+1+(m:ℤ))).toNat = (2*m+1) := by omega
  rw [e]
lemma inside_diff (m : ℕ) (x : Site n) (hx : x ∉ inside n (m/2)) (hm : m>0) :
   (‖incVec 1 (Lattice.lift x)‖^2)⁻¹ ≤ 4/(m:ℝ)^2 := by
  obtain ⟨i,hi⟩ : ∃ i, (m/2:ℕ) < (Lattice.lift x i).natAbs := by by_contra! hi; exact hx (mem_filter.mpr ⟨mem_univ _,Finset.sup_le (fun i _ => hi i)⟩)
  have hQ : (m:ℝ) < 2*‖incVec 1 (Lattice.lift x)‖ := by
    have hh := coordinate_le (incVec 1 (Lattice.lift x)) i; rw [incVec_apply,one_mul] at hh
    have he : m < 2 * (Lattice.lift x i).natAbs := by omega
    apply lt_of_lt_of_le (b:=2 * |(Lattice.lift x i:ℝ)|) _ (by linarith); rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast he
  apply (le_div_iff₀ (by positivity : 0 < (m:ℝ)^2)).mpr
  have h0 : 0 < ‖incVec 1 (Lattice.lift x)‖ := by linarith
  rw [inv_mul_eq_div, div_le_iff₀ (sq_pos_of_pos h0)]
  nlinarith only [hQ, show 0 < (m:ℝ) by exact_mod_cast hm]
lemma inner_weight (m : ℕ) : talc m n ≤ 432*(m:ℝ)^2 := by
  induction m using Nat.strongRec with
  | ind m h =>
   by_cases hm:m=0
   · subst m
     have he (x : Site n) (hx : x ∈ inside n 0) : ‖incVec 1 (Lattice.lift x)‖=0 := by rw [norm_eq_zero]; ext i; have hh := pdist_small x _ hx i; have hf := abs_nonneg (lift x i); have ht := (abs_eq_zero.mp (by omega : |Lattice.lift x i|=0)); simp [incVec_apply,ht]
     unfold talc; rw [show (∑ p ∈ inside n 0, (‖incVec 1 (Lattice.lift p)‖^2)⁻¹)=0 from sum_eq_zero (fun i hi => by rw [he i hi]; norm_num)]; positivity
   have hm0 : 0<m := Nat.pos_of_ne_zero hm
   let A := inside n (m/2)
   have hi : A ⊆ inside n m := fun x hx=>mem_filter.mpr ⟨mem_univ _, le_trans (mem_filter.mp hx).2 (Nat.div_le_self _ _)⟩
   have hhalf := h (m/2) (by omega)
   have hs := inside_count (m) (n:=n)
   have hdiff : ((inside n m \ A).card : ℝ) ≤ (3*(m:ℝ))^4 := by
     calc _ ≤ ((2*m+1:ℕ):ℝ)^4 := by exact_mod_cast le_trans (Finset.card_le_card (Finset.sdiff_subset (s:=inside n m))) hs
          _ ≤ _ := by
            gcongr; push_cast
            suffices _h : (2:ℕ)*m+1≤3*m by exact_mod_cast _h
            omega
   unfold talc
   rw [← Finset.sum_sdiff hi]
   change _ + talc (m/2) n ≤ _
   grw [Finset.sum_le_sum (g:=fun _=>4/(m:ℝ)^2) (fun x hx=> inside_diff m x (mem_sdiff.mp hx).2 hm0),hhalf]
   have hv : (2:ℕ)*(m/2) ≤ m := by omega
   have e : ((m/2:ℕ):ℝ)^2 ≤ (m/2:ℝ)^2 := by
      have hf : 2*((m/2:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast hv
      have hg : 0 ≤ ((m/2:ℕ):ℝ) := by positivity
      nlinarith only [hf,hg]
   rw [Finset.sum_const,nsmul_eq_mul]; grw [e,hdiff]; field_simp; nlinarith

lemma piece_unwrap {h s : ℝ} (hh : h>0) (hs : s>0) (D : List Axis) (x : Site n) : piece h s D x = (((n.val:ℂ)*h)⁻¹^4*(s:ℂ)^((D.length:ℤ)-2)) * ∑ p : Site n, char p x * symbol D (h*s) (stretch (h*s) p) * ↑(crop (h*s) p) := by
  unfold piece; simp_rw [Finset.mul_sum,multiplier D _ (h*s) (mul_pos hh hs),← norm_factor hh hs D.length]; exact Finset.sum_congr rfl (fun p hp => by ring)
lemma sinc1 {x : ℝ} (h : |x| ≤ 1) : 2/Real.pi ≤ sinQ x := by
  by_cases hz : x=0
  · subst x; rw [sinQ_zero]; exact div_le_one Real.pi_pos|>.mpr Real.two_le_pi
  have hx := abs_pos.mpr hz
  have ht := Real.mul_le_sin (x:=|x|) hx.le (h.trans (by linarith [Real.two_le_pi]))
  have he : Real.sin |x| = sinQ x * |x| := by by_cases xh : 0≤x
                                              · simpa only [abs_of_nonneg xh,mul_comm] using (sinQ_mul x).symm
                                              simpa only [abs_of_neg (lt_of_not_ge xh),Real.sin_neg,neg_mul,mul_neg,mul_comm, neg_inj] using! (sinQ_mul x).symm
  rw [he] at ht; exact le_of_mul_le_mul_right ht hx
lemma lattice_approx {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 2) {x : E4} (hx : ‖x‖≤1) : ‖x‖^2 * (2/Real.pi)^2 ≤ latticeD t x := by
  rw [norm_four,Finset.sum_mul,latticeD]; apply Finset.sum_le_sum; intro i hi
  have hh := coordinate_le x i; have hp : |t*x i/2|≤1 := by simpa [abs_div,abs_mul,abs_of_nonneg ht.1] using (show t*|x i|/|2|≤1 by have := mul_le_mul ht.2 (hh.trans hx) (abs_nonneg (x i)) (le_of_lt (by norm_num : (0:ℝ)<2)); rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith)
  have h := sinc1 hp; have hpi : 0≤(2/Real.pi) := by positivity
  have h2 : (2/Real.pi)^2 ≤ (sinQ (t*x i/2))^2 := by have := Real.pi_pos; nlinarith only [h,hpi]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left h2 (sq_nonneg (x i))
lemma lattice_inv {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 2) {x : E4} (hn : ‖x‖≤1) : (latticeD t x)⁻¹ ≤ (‖x‖^2)⁻¹*(Real.pi/2)^2 := by
  by_cases hx : x=0; · simp [hx,latticeD]
  by_cases hd : latticeD t x=0; · rw [hd,inv_zero]; positivity
  have hy := lattice_approx ht hn
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : 0<latticeD t x := (show 0 < ‖x‖^2*(2/Real.pi)^2 by positivity).trans_le hy
  convert! (one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos (div_pos zero_lt_two Real.pi_pos))) hy) using 1 <;> field_simp
end YM.Pert.Band
