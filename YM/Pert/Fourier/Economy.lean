import YM.Pert.Fourier.Beats
/-! Discrete oscillation identities and frequency counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Finset Lattice Full Topology Set
open scoped BigOperators ContDiff
variable {n : Side}
lemma sum_shift (w : Site n) (g : Site n → ℂ) : ∑ p : Site n, g (p+w) = ∑ p, g p := Equiv.sum_comp (Equiv.addRight w) g
lemma char_mul_sum (z x y : Site n) : char (x+y) z = char y z * char x z := by rw [add_comm,Full.swap (_+_) z,char_add,Full.swap z x,Full.swap z y]
set_option maxHeartbeats 500000 in
lemma sum_punch (z : Site n) (f : Site n → ℂ) (i : Axis) (j : ℕ) : ∑ p : Site n, char p z * gridDiff (-(step i)) j f p = ((char (step i) z)-1)^j * ∑ p, char p z * f p := by
  induction j with
  | zero => simp [gridDiff]
  | succ j h =>
    simp_rw [gridDiff,mul_sub,sum_sub_distrib]
    set Q : Site n→ℂ := gridDiff (-(step i)) j f with hQ
    have H := sum_shift (step i) (fun p : Site n => char p z * Q (p+(-(step i))))
    simp_rw [show ∀ p : Site n, p+step i + (-(step i))=p from fun _=>by abel,char_mul_sum,mul_assoc, ← Finset.mul_sum] at H
    rw [← H,h,pow_succ]; ring

-- avoid indexing recursion issues: proof replace
lemma counts (q : ℤ) {n : Side} {_s : Finset (Site n)} (h : ∀ x∈_s, ∀ i, |Lattice.lift x i| ≤ q) : _s.card ≤ (Int.toNat (q+1+q))^4 := by
  classical
  let A := Finset.Icc (-q) q
  have hI : Function.Injective (@lift n) := fun s v h => by rw [← wrap_lift s,← wrap_lift v,h]
  refine le_trans (b:=(Fintype.piFinset (fun i : Axis => A)).card) (Finset.card_le_card_of_injOn (@lift n) (fun i hi => by rw [Finset.mem_coe,Fintype.mem_piFinset]; exact fun a=> Finset.mem_Icc.mpr (abs_le.mp (h i hi a))) (Function.Injective.injOn hI)) ?_
  exact (by simp [A,Int.card_Icc,Fintype.card_piFinset])
lemma near_count {t : ℝ} (ht : 0<t) (hN : 1 ≤ t/mesh n) : let B := Finset.univ.filter (fun p : Site n => ‖stretch t p‖≤3); let T:ℝ:= t/mesh n; (B.card : ℝ) ≤ 8^4*T^4 := by
  intro B T
  have hh : (⌊3*T⌋ : ℤ) ≥ 0 := Int.floor_nonneg.mpr (mul_nonneg zero_le_three (show 0≤T from zero_le_one.trans hN))
  have he : ((⌊3*T⌋ +1+⌊3*T⌋).toNat : ℝ) ≤ 8*T := by
    calc _ = ((⌊3*T⌋ +1+⌊3*T⌋ : ℤ):ℝ) := by
           have h' : (((⌊3*T⌋+1+⌊3*T⌋).toNat : ℤ):ℝ)=((⌊3*T⌋+1+⌊3*T⌋:ℤ):ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
           exact_mod_cast h'
         _ ≤ _ := by push_cast; linarith [show T≥1 from hN, Int.floor_le (3*T)]
  have hpi (x : Site n) (hx : x∈B) (i : Axis) : |Lattice.lift x i| ≤ ⌊3*T⌋ := by
    have hv : |stretch t x i|≤3 := (coordinate_le _ _).trans (Finset.mem_filter.mp hx).2
    have hx : (↑|Lattice.lift x i| : ℝ) ≤ 3*T := by
      have e : |stretch t x i| = (↑|Lattice.lift x i|:ℝ) / T := by simp [stretch,T,PiLp.smul_apply,abs_mul,abs_of_pos ht,abs_of_pos mesh_pos]; field_simp
      rw [e] at hv; exact (div_le_iff₀ (show 0<T from by unfold T; positivity)).mp hv
    rw [← Int.le_floor] at hx; exact hx
  calc _ ≤ ((((⌊3*T⌋+1+⌊3*T⌋).toNat)^4:ℕ):ℝ) := by exact_mod_cast counts (n:=n) (⌊3*T⌋) hpi
       _ ≤ (8*T)^4 := by push_cast; gcongr
       _ = _ := by ring
lemma ctrl (D : List Axis) (v : ℕ) : ∃ C > 0, ∀ {n : Side} {t : ℝ}, 0<t → t ≤ 1 → mesh n * v ≤ 1/2 → mesh n * (v+1) ≤ t → ∀ (f : Axis) (z : Site n), let T:ℝ := mesh n/t;
 ‖char (step f) z - 1‖^v * ‖∑ p,char p z * ringM D t p‖ ≤ C / (T^4)*T^v ∧ (1/2 ≤ t → ‖char (step f) z - 1‖^v * ‖∑ p, char p z * roof D t p‖ ≤ C / (T^4)*T^v) := by
  obtain ⟨c,hp,H⟩ := punches D v
  refine ⟨max (8^4*c) ((4*Real.pi)^4*c),lt_of_lt_of_le (by positivity) (le_max_left ..),?_⟩; intro n t ht ht' hr hv i z T
  let E := t/mesh n
  have hv' : mesh n * (v:ℝ) ≤ t := by linarith [mesh_pos (n:=n)]
  have hh : 1 ≤ E := by unfold E; rw [le_div_iff₀ mesh_pos]; have hv'' := mesh_pos (n:=n); nlinarith [show (0:ℝ)≤v by positivity]
  have ht0 : 0 < T := div_pos mesh_pos ht
  rw [← Complex.norm_pow]
  constructor
  · rw [← Complex.norm_mul,← sum_punch z]
    apply (norm_sum_le ..).trans
    grw [show (∑ p, ‖char p z * gridDiff (-step i) v (ringM D t) p‖) ≤ ∑ p ∈ Finset.univ.filter (fun p : Site n=>‖stretch t p‖≤3),T^v*c by
      rw [Finset.sum_filter]; apply Finset.sum_le_sum; intro p _; rw [Complex.norm_mul,norm_char,one_mul]; exact (H ht ht' hr hv' i p).1]; rw [Finset.sum_const,nsmul_eq_mul]
    have hb := near_count ht hh
    dsimp only at hb
    apply (mul_le_mul_of_nonneg_right hb (show 0≤T^v*c from by positivity)).trans
    calc _ = 8^4*c/T^4*T^v := by unfold T; field_simp
         _ ≤ _ := by gcongr; exact le_max_left ..
  intro h1
  rw [← Complex.norm_mul,← sum_punch z]
  apply (norm_sum_le ..).trans
  apply (Finset.sum_le_sum (g:=fun (p : Site n) => T^v*c) _).trans ?_
  · intro p _; rw [Complex.norm_mul,norm_char,one_mul]; exact (H ht ht' hr hv' i p).2 h1
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,site_card,Nat.cast_pow]
  have ht4 : (1/2:ℝ)^4 ≤ t^4 := by gcongr
  have eN : (n.val:ℝ) ≤ 4*Real.pi/T := by
    unfold T mesh; field_simp; have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 4*Real.pi by positivity); nlinarith
  calc _ ≤ (4*Real.pi/T)^4*(T^v*c) := by gcongr
       _ = ((4*Real.pi)^4*c/T^4)*T^v := by ring
       _ ≤ _ := by gcongr; apply le_max_right
end YM.Pert.Band
