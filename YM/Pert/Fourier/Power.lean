import YM.Pert.Fourier.Survey
/-! Upper momentum tail of a separated finite difference, no incorrect absolute infinite-volume sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Metric Lattice Full Topology
open scoped BigOperators
variable {n : Side}
lemma convert_layer (c E R T s : ℝ) (hs : 0<s) (hmesh : T * s = 2*Real.pi*c) (hc : 0 < c) (hr : 0<R) (d : ℕ) :
    c^4*s^((d:ℤ)-2)*(E / T^4)*(T^(d+3))/((R*c)^(d+3)) = (E/(2*Real.pi)^4)*(2*Real.pi/R)^(d+3)/s := by
  have hm : T = 2*Real.pi*c/s := (eq_div_iff hs.ne').2 hmesh
  rw [hm,zpow_sub₀ hs.ne']; norm_cast; push_cast
  rw [pow_add (2 * _ / R),pow_add _ d, mul_pow R, div_pow (2*Real.pi*c) s, mul_pow (2*Real.pi) c]; simp only [div_pow, mul_pow, pow_add]; field_simp
lemma convert_one {n} {s h A C T : ℝ} {I : ℂ} (hc : 0<h) (hs : 0<s) (hA : 0 < A) (hC : 0 < C)
  (R : ℂ) (c : ℝ) (hc' : c = (↑n.val*h)⁻¹) (d : ℕ) (he : T*s = 2*Real.pi*c) (fn : Axis) (z : Site n) (hi : A*c ≤ ‖char (step fn) z - 1‖)
  (hv : ‖char (step fn) z-1‖^(d+3) * ‖R‖ ≤ C/T^4 * T^(d+3))
  (hI : I = (((n.val:ℂ)*h)⁻¹^4*(s:ℂ)^((d:ℤ)-2)) * R) :
   ‖I‖ ≤ (C/(2*Real.pi)^4)*(2*Real.pi/A)^(d+3)/s := by
  have hcp : 0<c := hc'.symm ▸ inv_pos.mpr (mul_pos (val_pos n) hc)
  have e : ‖(((n.val:ℂ)*h:ℂ)⁻¹^4*(s:ℂ)^((d:ℤ)-2))‖ = c^4*s^((d:ℤ)-2) := by
    rw [hc']; norm_cast; apply Real.norm_of_nonneg; positivity
  rw [hI,Complex.norm_mul,e,← convert_layer c C A T s hs he hcp hA]; apply (le_div_iff₀ (pow_pos (mul_pos hA hcp) _)).2
  have hb := mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hi (d+3)) (norm_nonneg R)) hv) (show 0≤c^4 * s^((d:ℤ)-2) by positivity)
  linarith only [hb]
lemma layer (D : List Axis) (R : ℝ) (hr : 0 < R) : ∃ C > 0, ∀ {n : Side} {s h : ℝ}, 0<s → 0<h → h*s ≤ 1 → mesh n * ((D.length+4:ℕ):ℝ) ≤ 1/2 → mesh n * ((D.length+4:ℕ):ℝ) ≤ h*s → ∀ z : Site n, R ≤ ‖incVec h (Lattice.lift z)‖ →
    ‖corona h s D z‖ ≤ C/s ∧ (1/2 ≤ h*s → ‖outsideP h s D z‖ ≤ C/s) := by
  obtain ⟨E,hE,G⟩ := ctrl D (D.length+3)
  refine ⟨(E/(2*Real.pi)^4)*(2*Real.pi/R)^(D.length+3),by positivity,?_⟩
  intro n s h hs hh h1 hv0 hv1 z hZ
  obtain ⟨fn,hf⟩ := signal z h hh
  let c : ℝ := ((n.val:ℝ)*h)⁻¹
  let t := h*s
  have hc : 0<c := inv_pos.mpr (mul_pos (val_pos n) hh)
  have gz : R*c ≤ _ := le_trans (mul_le_mul_of_nonneg_right hZ hc.le) hf
  have hb := G (n:=n) (t:=t) (mul_pos hh hs) h1 (le_trans (by push_cast; linarith [mesh_pos (n:=n)]) hv0) (le_trans (by push_cast; ring_nf; exact le_rfl) hv1) fn z
  have cost {x Q : ℂ} (L : ‖char (step fn) z - 1‖^(D.length+3)*‖Q‖ ≤ E/(mesh n/t)^4 * (mesh n/t)^(D.length+3))
      (hI : x = (((n.val:ℂ)*h)⁻¹^4*(s:ℂ)^((D.length:ℤ)-2)) * Q) : ‖x‖ ≤ _ := convert_one hh hs hr hE Q c rfl D.length (by unfold t mesh c; field_simp) fn z gz L hI
  exact ⟨cost hb.1 (corona_expand _ _ hh hs _ _),fun hq => cost (hb.2 hq) (outside_expand _ _ hh hs _ _)⟩
def dial (S C : ℝ) (n : ℕ) := C/(2^n*S)
lemma double_diff (D : List Axis) {n : Side} (z : Site n) {h s C : ℝ} {q : ℕ} (hx : ∀ i<q, ‖corona h (2^i*s) D z‖ ≤ dial s C i) :
    ‖piece h (2^q*s) D z-piece h s D z‖ ≤ (2*(1-(1/2:ℝ)^q))*(C/s) := by
  induction q with
  | zero => simp
  | succ m ih =>
    have e := hx m (by omega)
    let α:=2*(2^m*s)
    have eq1 : piece h (2^(m+1)*s) D z-piece h s D z = (corona h (2^m*s) D z) + (piece h (2^m*s) D z-piece h s D z) := by unfold corona; rw [sub_add_sub_cancel, pow_succ, mul_right_comm, mul_comm 2]
    rw [eq1]; apply le_trans ((norm_add_le ..).trans (add_le_add e (ih (fun i hi => hx i (by omega))))) (le_of_eq ?_)
    unfold dial
    have h2 : ((2:ℝ)^m) ≠ 0 := by positivity
    rw [pow_succ, one_div, inv_pow]
    field_simp; ring

lemma threshold {h s : ℝ} (hs : 0<s) (hh : 0<h) (hx : h*s≤1/2) : ∃ q : ℕ, h*(2:ℝ)^q*s ∈ Set.Icc (1/2) 1 := by
  have he := tendsto_pow_atTop_atTop_of_one_lt (r:=(2:ℝ)) (by norm_num)
  have hv := he.eventually (eventually_gt_atTop ((1/2) / (h*s)))
  have ho : ∃ i : ℕ, (1/2) < h*(2:ℝ)^i*s := by obtain ⟨i,hi⟩ := hv.exists; apply Exists.intro i; have hp := (div_lt_iff₀ (mul_pos hh hs)).mp hi; linarith only [hp]
  let k := Nat.find ho; have hk := Nat.find_spec ho
  refine ⟨k,le_of_lt hk,?_⟩
  obtain ⟨j,hj⟩ : ∃ j, k = j+1 := Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => by rw [show Nat.find ho = 0 from h0,pow_zero] at hk; linarith)
  have hv := le_of_not_gt (Nat.find_min (p:=fun i : ℕ => 1/2<h*(2:ℝ)^i*s) ho (by omega : j<k))
  rw [hj,pow_succ]; linarith only [hv]
lemma upper_tail (D : List Axis) (R : ℝ) (hr : 0<R) : ∃ C>0, ∀ {n : Side} {h s : ℝ}, 0<h → 0<s → h*s ≤ 1/2 → mesh n * ((D.length+4:ℕ):ℝ) ≤ h*s → ∀ z : Site n, R ≤ ‖incVec h (Lattice.lift z)‖ → ‖joint h D z-piece h s D z‖ ≤ C/s := by
  obtain ⟨C,hp,H⟩ := layer D R hr; refine ⟨3*C,by positivity,?_⟩; intro n h s hh hs hv1 ht z hZ
  obtain ⟨q,hq₁,hq₂⟩ := threshold hs hh hv1
  have he (i : ℕ) (hi : i≤q) := H (n:=n) (s:=2^i*s) (by positivity) hh (by rw [←mul_assoc]; grw [show (2:ℝ)^i ≤ 2^q from pow_le_pow_right₀ (by norm_num) hi]; exact hq₂) (ht.trans hv1) (ht.trans (by grw [← one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ))]; simp)) z hZ
  have hi := ((he q le_rfl).2 (by rwa [← mul_assoc])).trans (div_le_div_of_nonneg_left hp.le hs (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : 1≤(2:ℝ))) hs.le))
  have hg : (joint h D z-piece h s D z) = outsideP h ((2:ℝ)^q*s) D z+(piece h ((2:ℝ)^q*s) D z-piece h s D z) := by rw [← add_sub_assoc,clear_joint h ((2:ℝ)^q*s) D]; congr 1; apply add_comm
  rw [hg]; apply le_trans ((norm_add_le ..).trans (add_le_add hi (double_diff D z (fun i hj => (he _ hj.le).1)))) ?_
  rw [show 3*C/s=3*(C/s) by ring]; nlinarith only [show 0≤ (C/s)*(1/2:ℝ)^q from by positivity]
end YM.Pert.Band
