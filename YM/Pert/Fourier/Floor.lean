import YM.Pert.Fourier.Capacity

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Lattice Full Topology
open scoped BigOperators
variable {n : Side}
def window (t : ℝ) (n : Side) := Finset.univ.filter fun p : Site n => ‖stretch t p‖≤1
def purse := (2/Real.pi)⁻¹ ^2 * (432:ℝ) / (2*Real.pi)^4
lemma numerator_bd (t : ℝ) (k : E4) (hk : ‖k‖≤1) (f : Axis) : ‖numerator t k f‖ ≤ 1 := by
  suffices H : ‖phaseQ (t*k f)‖ ≤ 1 by
    rw [numerator,Complex.norm_mul,Complex.norm_real, Real.norm_eq_abs]; grw [coordinate_le, hk,H]; simp
  generalize t*k f = r
  by_cases ht : r=0; · simp [ht,phaseQ_zero]
  apply le_of_mul_le_mul_left (a:=|r|) _ (abs_pos.mpr ht)
  rw [← Real.norm_eq_abs, ← norm_smul,phaseQ_mul,phase,mul_comm (↑r:ℂ) Complex.I]; simp only [mul_one]; exact Real.norm_exp_I_mul_ofReal_sub_one_le
lemma point_tax (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 2) (D : List Axis) (p : Site n) : ‖↑(crop t p)*symbol D t (stretch t p)‖ ≤
   (2/Real.pi)⁻¹ ^2 * if p∈window t n then (‖stretch t p‖^2)⁻¹ else 0 := by
  by_cases h : p∈window t n; swap
  · rw [if_neg h,crop,disk_out (le_of_not_ge (fun hx=>h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)))]; simp
  have htq : ‖stretch t p‖ ≤ 1 := Finset.mem_filter.mp h|>.2; let q:= stretch t p
  have hp : ‖(D.map (numerator t q)).prod‖≤1 := by induction D with | nil => simp | cons a D e=> dsimp only [List.map_cons,List.prod_cons]; rw [Complex.norm_mul]; exact mul_le_one₀ (numerator_bd _ _ htq a) (norm_nonneg _) e
  have e : 0 ≤ latticeD t q := by unfold latticeD; exact Finset.sum_nonneg fun i hi=>sq_nonneg _
  rw [if_pos h,Complex.norm_mul,symbol, Complex.norm_mul,norm_inv,Complex.norm_real,Complex.norm_real, Real.norm_of_nonneg (by unfold crop; exact disk.nonneg)]
  have : 0≤crop t p := disk.nonneg
  grw [hp]; rw [Real.norm_of_nonneg e,mul_one]; grw [show crop t p≤1 from disk.le_one,one_mul, lattice_inv ht htq]; ring_nf; simp only [inv_inv, le_refl]
lemma total_pole (t : ℝ) (ht : 0 < t) : ∑ p∈window t n, (‖stretch t p‖^2)⁻¹ ≤ (432:ℝ) * (mesh n/t)⁻¹ ^4 := by
  let Y := t/mesh n
  have hy : 0<Y := div_pos ht mesh_pos
  have e (p : Site n) : ‖stretch t p‖ = Y⁻¹ * ‖incVec 1 (lift p)‖ := by
    have hx : incVec (mesh n) (lift p) = (mesh n) • incVec 1 (lift p) := by ext i; simp [incVec_apply]
    unfold stretch moment; rw [hx,smul_smul,norm_smul]; congr 1; rw [←div_eq_inv_mul]; dsimp only [Y]; rw [inv_div,Real.norm_of_nonneg (by exact (div_pos mesh_pos ht).le)]
  have hx : ∑ p∈window t n, (‖incVec 1 (lift p)‖^2)⁻¹ ≤ talc (⌊Y⌋₊) n := Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun i _ _ => by positivity)
  rotate_left
  · apply (Finset.mem_filter (p:=fun x : Site n => pdist x≤⌊Y⌋₊)).2 ⟨Finset.mem_univ _,Finset.sup_le (fun i _ => Nat.le_floor ?_)⟩
    have ht0 := Finset.mem_filter.mp hx|>.2; rw [e,inv_mul_eq_div,div_le_iff₀ hy,one_mul] at ht0
    have hh := coordinate_le (incVec 1 (lift x)) i; simpa only [Full.incVec_apply,one_mul, ← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] using hh.trans ht0
  rw [show (mesh n / t)=Y⁻¹ by dsimp only [Y]; rw [inv_div]]; simp_rw [e,mul_pow,mul_inv, inv_pow,inv_inv, ← Finset.mul_sum]
  grw [hx,inner_weight,show ((⌊Y⌋₊):ℝ)≤Y from Nat.floor_le hy.le]; nlinarith only [show 0≤((⌊Y⌋₊):ℝ) by positivity]

lemma residue (d : ℕ) {s c T : ℝ} (hs : 0 < s) (h : c*(2*Real.pi)=T*s) (ht : 0 < T) : c^4*s^((d:ℤ)-2) * ((2/Real.pi)⁻¹^2*(432*T⁻¹^4)) = purse*s^(d+2) := by
  rw [inv_pow,show ((d:ℤ)-2)= (d:ℤ)+2+(-(4:ℤ)) from by ring,zpow_add₀ hs.ne']; push_cast
  have he : s^((d:ℤ)+2)=s^(d+2) := by rw [zpow_add₀ hs.ne',pow_add,zpow_natCast]; norm_cast
  rw [he]; have eq := (eq_div_iff (by positivity : 2*Real.pi≠0)).2 h; rw [eq]; unfold purse; field_simp
lemma lower (h s : ℝ) (hs : 0<s) (hh : 0<h) (h1 : h*s ≤ 2) (z : Site n) (D : List Axis) : ‖piece h s D z‖ ≤ purse*s^(D.length+2) := by
  let t:=h*s; let c:ℝ:=((n.val:ℝ)*h)⁻¹; let T:=mesh n/t
  have ev : c*(2*Real.pi)=T*s := by unfold c T t mesh; field_simp
  have e : ‖(((n.val:ℂ)*h)⁻¹^4*(s:ℂ)^(((D.length:ℕ):ℤ)-2))‖ = c^4*s^(((D.length:ℕ):ℤ)-2) := by dsimp [c]; norm_cast; apply Real.norm_of_nonneg; positivity
  rw [piece_unwrap hh hs,Complex.norm_mul]; rw [e,← residue D.length hs ev (div_pos mesh_pos (mul_pos hh hs))]
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [c]; positivity)
  refine le_trans (le_trans (norm_sum_le ..) (Finset.sum_le_sum (g:=fun p : Site n=>(2/Real.pi)⁻¹ ^2 * if p∈window t n then (‖stretch t p‖^2)⁻¹ else 0) (fun p hp=> by 
    rw [mul_assoc,Complex.norm_mul,norm_char,one_mul,mul_comm]; exact point_tax t ⟨(show 0≤t from (mul_pos hh hs).le),h1⟩ D p))) ?_
  rw [← Finset.mul_sum, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter];

  exact mul_le_mul_of_nonneg_left (total_pole t (mul_pos hh hs)) (by positivity)
end YM.Pert.Band
