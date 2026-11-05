import YM.Next.STATIONARY.Spectral.Folding

/-! Distances for estimating translation-invariant full-cover RG pullbacks; inputs are genuine lifted sites, row stencils will use `Stationary.rent`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Stationary Laurent
open scoped Topology BigOperators Classical

abbrev length (x : Cover) := (Laurent.size x : ℝ)
def sep (x y : Cover) := length (x-y)
lemma sep_nonneg (x y : Cover) : 0 ≤ sep x y := by unfold sep; positivity
lemma length_add (x y : Cover) : length (x+y) ≤ length x + length y := by exact_mod_cast size_add x y
lemma length_neg (x : Cover) : length (-x) = length x := by rw [length,size_neg]
lemma sep_comm (x y : Cover) : sep x y=sep y x := by rw [sep,sep,← length_neg,neg_sub]
lemma sep_self (x : Cover) : sep x x = 0 := by simp [sep,length,Laurent.size]
lemma sep_triangle (x y z : Cover) : sep x z ≤ sep x y + sep y z := by
  unfold sep
  exact Eq.mpr (by rw [sub_add_sub_cancel]) (length_add (x-y) (y-z))
lemma sep_shift (x y z : Cover) : sep (x+z) (y+z)=sep x y := by simp [sep]
lemma length_nsmul (x : Cover) (n:ℕ) : length (n • x) = (n:ℝ)*length x := by
  unfold length; rw [show Laurent.size (n • x)=n*Laurent.size x by unfold Laurent.size; simp_rw [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast,Finset.mul_sum]]; exact Nat.cast_mul ..
lemma scale_sep (x y : Cover) (n:ℕ) : sep (n • x) (n • y)=(n:ℝ)*sep x y := by rw [sep,← smul_sub,length_nsmul,sep]
lemma length_lift (L : Side) (x : Site L) : length (lift x) / (L.val:ℝ) ≤4 := by
  have ht := plank_charge L x
  simpa only [inch,div_eq_inv_mul] using ht
-- scale-matched mixed separation
def delta (L : Side) (x y : Cover) := sep x (L.val • y)/(L.val:ℝ)
lemma delta_nonneg (L) (x y : Cover) : 0 ≤ delta L x y := div_nonneg (sep_nonneg ..) (by positivity)
lemma inv_scaled (L : Side) (x y v z : Cover) : sep y z ≤ delta L x y + sep x v/(L.val:ℝ) + delta L v z := by
  have h1 := sep_triangle (L.val • y) v (L.val • z)
  have h2 := sep_triangle (L.val • y) x v
  rw [scale_sep] at h1
  rw [sep_comm _ x] at h2
  unfold delta
  have h3 : (L.val:ℝ)*sep y z ≤ sep x (L.val • y)+sep x v+sep v (L.val • z) := by linarith only [h1,h2]
  have he := div_le_div_of_nonneg_right h3 (show 0≤(L.val:ℝ) by positivity)
  rwa [add_div,add_div,mul_div_cancel_left₀ _ (by positivity : (L.val:ℝ) ≠0)] at he
lemma delta_fine (L) (x v y : Cover) : delta L x y ≤ sep x v / (L.val:ℝ) + delta L v y := by
  rw [delta,delta]; simpa only [add_div] using (div_le_div_of_nonneg_right (sep_triangle x v (L.val • y)) (show 0≤(L.val:ℝ) by positivity))
lemma delta_coarse (L) (x v y : Cover) : delta L x y ≤ delta L x v + sep v y := by
  rw [delta,delta]; simpa only [add_div,scale_sep,mul_div_cancel_left₀ _ (by positivity : (L.val:ℝ) ≠0)] using (div_le_div_of_nonneg_right (sep_triangle x (L.val • v) (L.val • y)) (show 0≤(L.val:ℝ) by positivity))
lemma delta_coarse' (L) (x v y : Cover) : delta L x y ≤ sep v y + delta L x v := add_comm _ (sep v y) ▸ delta_coarse L x v y
lemma length_step (i : Axis) : length (step i) = 1 := by
  change (↑(Laurent.size _) : ℝ)=_
  suffices h : Laurent.size (step i : Cover)=1 by simp [h]
  unfold Laurent.size
  simp [apply_ite Int.natAbs]
lemma len_path_plus (x : Cover) (i : Axis) : sep (x+step i) x=1 := by rw [sep,add_sub_cancel_left, length_step]
end YM.Pert.Bulk
