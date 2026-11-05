import YM.Laurent.Eval

/-!
# Mesh Fourier orthogonality in Cover conventions

Column side aliases later. No ignoring harmonic point. No σ powers here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Bloch
open Lattice Laurent Matrix Function Filter Set Complex
open scoped Topology BigOperators ComplexConjugate ContDiff

abbrev Momentum := Laurent.Phase Axis
variable {n : Side}

def mon (p : Site n) : Momentum := ((n.val : ℂ)⁻¹) • reciprocal (lift p)

def cell (p r : Site n) : ℂ := mode (mon p) (lift r)
lemma side_pos (n : Side) : (0:ℝ)<(n.val:ℝ) := by exact_mod_cast n.property
lemma side_ne (n : Side) : (n.val:ℂ)≠0 := by exact_mod_cast n.property.ne'

@[simp] lemma mon_phase (p : Site n) : n.val • mon p = reciprocal (lift p) := by
  unfold mon; rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,mul_inv_cancel₀ (side_ne _),one_smul]

@[simp] lemma mon_zero : mon (0 : Site n)=0 := by funext; simp [mon,Lattice.lift,reciprocal]

@[simp] lemma real_frequency (p : Site n) : star (mon p)=mon p := by
  funext i; simp only [mon,reciprocal,Pi.smul_apply,smul_eq_mul, Pi.star_apply, Complex.star_def,map_mul,map_ofNat]; simp

lemma cover_of_eq (p q : Cover) (h : wrap n p=wrap n q) : ∃ z : Cover, q=p+n.val • z := by
  have H (i : Axis) : ∃ j : ℤ, q i=p i+(n.val:ℤ)*j := by
    have he : (n.val : ℤ) ∣ q i-p i := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congr_fun h i)
    obtain ⟨j,hj⟩ := he
    exact ⟨j,by omega⟩
  choose z hz using H
  exact ⟨z, funext fun i => hz i |>.trans (by simp)⟩

lemma respects (p : Site n) (x y : Cover) (h : wrap n x=wrap n y) : mode (mon p) x=mode (mon p) y := by
  obtain ⟨z,rfl⟩ := cover_of_eq x y h
  rw [mode_shift, ← mode_scale, mon_phase, mode_periodic,mul_one]

@[simp] lemma cell_wrap (p : Site n) (x : Cover) : cell p (wrap n x)= mode (mon p) x := respects _ _ _ (wrap_lift _)

@[simp] lemma cell_add (p r t : Site n) : cell p (r+t)=cell p r*cell p t := by
  obtain ⟨x,rfl⟩ := (show Surjective (wrap n) from fun i => ⟨_,wrap_lift i⟩) r
  obtain ⟨x',rfl⟩ := (show Surjective (wrap n) from fun i => ⟨_,wrap_lift i⟩) t
  rw [← map_add]; simp only [cell_wrap,mode_shift]

lemma cell_duality (p r : Site n) : cell p r=cell r p := by
  unfold cell mode
  simp only [mon,reciprocal,Pi.smul_apply,smul_eq_mul]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

lemma cell_inverse (p r : Site n) : cell p (-r)=(cell p r)⁻¹ := by
  rw [← wrap_lift r,← map_neg,cell_wrap,mode_opposite, cell_wrap]

@[simp] lemma cell_origin (p : Site n) : cell p 0=1 := by rw [cell_duality]; simp [cell]

@[simp] lemma cell_ne (p r : Site n) : cell p r≠0 := Complex.exp_ne_zero _

lemma cell_sub (p q i : Site n) : cell (p-q) i = cell p i * (cell q i)⁻¹ := by
  rw [cell_duality (p-q) i,sub_eq_add_neg,cell_add,cell_inverse,cell_duality i p,cell_duality i q]

lemma cell_step (p : Site n) (i : Axis) : cell p (step i)=Complex.exp (Complex.I*mon p i) := by
  rw [show (step i : Site n)=wrap n (step i) from (wrap_step ..).symm,cell_wrap]
  simp [mode,mul_ite]

lemma step_picks (p : Site n) (hp : p≠0) : ∃ i, cell p (step i) ≠ 1 := by
  by_contra! h
  apply hp
  have he (i : Axis) : (n.val:ℤ) ∣ lift p i := by
    have hh := h i
    rw [cell_step] at hh
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp hh
    have hs := side_ne n
    change I * ((n.val:ℂ)⁻¹*(2 * (Real.pi:ℂ)*(lift p i:ℤ))) = _ at hk
    have ht (X Y : ℂ) : 2*(Real.pi:ℂ)*X*Complex.I=2*(Real.pi:ℂ)*Y*Complex.I → X=Y := by
      intro eq
      exact mul_left_cancel₀ (show 2*(Real.pi:ℂ) ≠ 0 from mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) (mul_right_cancel₀ Complex.I_ne_zero eq)
    have hl : (lift p i:ℂ) = (n.val:ℂ)*k := ht _ _ (by
      have e := congr_arg ((n.val:ℂ)*·) hk; field_simp at e ⊢ 
      linear_combination e)
    exact ⟨k,by exact_mod_cast hl⟩
  rw [← wrap_lift p]
  funext i
  obtain ⟨k,hk⟩ := he i
  change ((lift p i : ℤ) : ZMod n.val)=0
  simp [hk]

@[simp] lemma cell_bar (p r : Site n) : conj (cell p r)=(cell p r)⁻¹ := by
  have he := mode_adjoint (mon p) (lift r)
  rw [real_frequency,mode_opposite] at he
  exact he

lemma sum_cell {p : Site n} (hp : p≠0) : ∑ i, cell p i=0 := by
  obtain ⟨j,hj⟩ := step_picks p hp
  have ht : ∑ i, cell p i=(∑ i, cell p i)*cell p (step j) := calc
    _ = ∑ i, cell p (i+step j) := (Equiv.sum_comp (Equiv.addRight (step j)) _).symm
    _ = _ := by simp [Finset.sum_mul]
  by_contra! h
  exact hj <| mul_left_cancel₀ h (ht.symm.trans (mul_one _).symm)

lemma orthogonal (p r : Site n) : (∑ i, cell p i * (cell r i)⁻¹)=if p=r then (n.val : ℂ)^4 else 0 := by
  rw [show (∑ i, _) = ∑ i, cell (p-r) i by simp_rw [cell_sub]]
  split
  next he => rw [he]; simp [cell]
  next he => exact sum_cell (sub_ne_zero_of_ne he)

/-- DFT as a counting matrix. -/
def F (n : Side) : Matrix (Site n) (Site n) ℂ := of cell

@[simp] lemma F_apply (p r : Site n) : F n p r=cell p r := rfl

theorem gram (n : Side) : F n * star (F n) = (n.val : ℂ)^4 • 1 := by
  ext i j
  simpa [Matrix.star_eq_conjTranspose,mul_apply,one_apply,ite_id, smul_ite] using orthogonal i j

theorem coGram (n : Side) : star (F n) * F n = (n.val : ℂ)^4 • 1 := by
  ext i j
  simp only [mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,F_apply,Matrix.one_apply, Matrix.smul_apply]
  simp only [Complex.star_def,cell_bar, smul_eq_mul, mul_ite,mul_one,mul_zero]
  calc
    _ = ∑ p, cell j p * (cell i p)⁻¹ := Finset.sum_congr rfl fun p _ => by rw [cell_duality p,cell_duality p,mul_comm]
    _ = _ := (orthogonal j i).trans (by simp [eq_comm])
end YM.Bloch
