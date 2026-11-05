import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Resolve
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Further.FREE_COVARIANCE_KP.KP.Episode
import YM.Push.GRID_APPROXIMATION.AttachDefs


/-!
# Scalar-curvature part of the atlas

Normalization E KPcol, on the actual train. Positive blades, base at a corner,
`K=x row, y column`, so the `+i p` mode of `x-y`. All tori including coincident
sites and self-conjugate grid frequencies. We promote the KP sums to actual
matrices and identify them with the cochain inverse on curls (Resolve).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free
open Further.FreeCovariance.KP
open Further.CorrectedLift
open scoped Topology BigOperators ComplexConjugate

variable {n : Side} {j : ℕ} {k : ℝ}

/-- Real scalar matrix in unscaled lattice units, directions `TypeFace 2`.
`Episode.found` uses the *same* kernel at contact (the full Brillouin sum),
and at **frequency** zero the arc is zero. -/
def scalarCov (k : ℝ) (v : Train j) (n : Side) : Matrix (Body 2 n) (Body 2 n) ℝ :=
  of fun x y => (Episode.found k v n x.2 y.2 (lift x.1-lift y.1)).re

lemma scalar_entry (hk : 0<k) (v : Train j) (x y : Body 2 n) :
    ((scalarCov k v n x y : ℝ) : ℂ) = Episode.found k v n x.2 y.2 (lift x.1-lift y.1) :=
  Complex.conj_eq_iff_re.mp (Episode.found_real hk v n _ _ _)

private theorem turn_entry (n : Side) (p x y : Site n) :
    mode (mon p) (lift x - lift y) = cell p x * star (cell p y) := by
  rw [sub_eq_add_neg,mode_shift,mode_opposite,Complex.star_def,cell_bar]
  rfl

lemma scalar_formula (hk : 0<k) (v : Train j) (n : Side) :
    let R := rotations n (TypeFace 2)
    approached (scalarCov k v n) = meter n • (R*solo n (Episode.arc k v)*Rᴴ) := by
  intro R; ext ⟨x,a⟩ ⟨y,b⟩
  rw [approached, Matrix.map_apply, scalar_entry hk]
  unfold R solo Episode.found; rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [rot_fiber]
  apply congr_arg (meter n * ·); apply Finset.sum_congr rfl
  intro p _; rw [turn_entry]
  simp [rotations, apply_ite star, mul_ite, mul_right_comm]

lemma scalar_circuit (hk : 0<k) (v : Train j) (n : Side) :
    Runs (rotations n (TypeFace 2)) (rotations n (TypeFace 2))
      (scalarCov k v n) (solo n (Episode.arc k v)) := by
  let R := rotations n (TypeFace 2)
  let X := solo n (Episode.arc k v)
  have hh : Rᴴ*R=stageVolume n • 1 := (rotations_crew n _).2.2
  change approached (scalarCov k v n) * R=R*X
  rw [show approached (scalarCov k v n)= (stageVolume n)⁻¹ • (R*X*Rᴴ) from scalar_formula hk v n,
    Matrix.smul_mul,Matrix.mul_assoc (R*X),hh,Matrix.mul_smul,Matrix.mul_one,smul_smul,inv_mul_cancel₀ (stage_ne n),one_smul]

private theorem herm_arc (hk : 0<k) (v : Train j) (q : Site n) :
    (Episode.arc k v (mon q))ᴴ = Episode.arc k v (mon q) := by
  let p := mon q
  have hc : star (scaleD 1 k v p) = scaleD 1 k v p := funext fun i=> (fieldD_silver _ _ hk _ (real_frequency q) i).fixed
  have h : (fieldD 1 k v p)ᴴ=fieldD 1 k v p := by rw [fieldD,mask_adj,hc]
  change (_*fieldD 1 k v p*_ )ᴴ = _
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,h,conjTranspose_conjTranspose,← Matrix.mul_assoc]
  rfl

lemma scalar_symm (hk : 0<k) (v : Train j) (n : Side) :
    (scalarCov k v n)ᵀ=scalarCov k v n := by
  have hh := scalar_circuit hk v n
  have ht := hh.back (rotations_crew n _) (rotations_crew n _)
  unfold solo at *
  rw [div_self (stage_ne n),one_smul,fiber_H] at ht
  simp_rw [herm_arc hk] at ht
  exact ht.lands hh (rotations_crew n _)

lemma scalar_closed (hk : 0<k) (v : Train j) (n : Side) :
    Exterior.d 2 n*scalarCov k v n = 0 := by
  have hf := (cobound_true 2).coarse n
  have ht := hf.product (scalar_circuit hk v n)
  have hh : solo n (signal 1 2)*solo n (Episode.arc k v)=0 := by
    unfold solo; rw [fiber_mult]
    have he (p : Momentum) : signal 1 2 p*Episode.arc k v p=0 := by
      rw [signal_unit, Episode.arc,← Matrix.mul_assoc, ← Matrix.mul_assoc]
      rw [show symbol 2 p*symbol 1 p=0 from Exterior.d_d .., Matrix.zero_mul, Matrix.zero_mul]
    simp_rw [he]; ext i j; simp [fiber]
  rw [hh] at ht
  refine ht.lands ?_ (rotations_crew n _)
  unfold Runs; rw [Matrix.mul_zero,show approached (0: Matrix _ _ ℝ) = 0 by ext; simp [approached], Matrix.zero_mul]

/-- Uniform point prices before looking at lengths, origins, or depth; unlike
Kper, includes x=y. Uses the punctured multiplier input to that theorem
and the *actual* zero mode. -/
lemma arc_price (hk : 0<k) (hj : 4≤j) : ∃ C : ℝ, 0≤C ∧
    ∀ (v : Train j) (n : Side) (x : Site n) a b, ‖Episode.arc k v (mon x) a b‖ ≤ C := by
  obtain ⟨α,D,η,ha,hη,h⟩ := Episode.paid k hk hj
  choose c hc hh using fun a b => ((gem_quote ha (Ω:=D) hη).1 a b).quotes 0
  let C := ∑ i, ∑ j, c i j
  have hm (i j) : c i j ≤ C :=
    (Finset.single_le_sum (fun j _=> hc i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _=> Finset.sum_nonneg fun b _=> hc a b) (Finset.mem_univ i))
  have hC : 0≤C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _=> hc i j
  refine ⟨C,hC,fun v n x a b=> ?_⟩
  obtain ⟨f,hf⟩:=h v
  by_cases hu : mon x=0
  · rw [hu,Episode.zero_harmonic,Matrix.zero_apply,norm_zero]; exact hC
  rw [← Episode.covered_layer v hk hj f hf ha hη x]
  let q := lit n (lift x)
  have he : q ∈ search := by
    refine ⟨fun i => ((local_price x i).trans_lt ?_),fun h => hu ?_⟩
    · unfold earth; linarith [Real.pi_pos]
    change q = 0 at h; rw [← lit_mon x]; change mcast q=_; rw [h]; ext; simp [mcast]
  apply le_trans ?_ (hm a b)
  simpa only [norm_iteratedFDeriv_zero,Nat.cast_zero,sub_zero,zpow_zero,mul_one] using hh a b f q he

lemma scalar_price (hk : 0<k) (hj : 4≤j) : ∃ C : ℝ, 0≤C ∧
    ∀ (v : Train j) (n : Side) (x y : Body 2 n), ‖scalarCov k v n x y‖ ≤ C := by
  obtain ⟨C,hC,H⟩ := arc_price hk hj
  refine ⟨C,hC,fun v n x y=>?_⟩
  rw [← Complex.norm_real,scalar_entry hk,Episode.found,norm_mul]
  have he : ‖meter n‖ * (∑ _ : Site n, C) = C := by
    have hn := side_pos n
    simp only [Further.FreeCovariance.KP.meter,norm_inv,norm_pow,Complex.norm_natCast,Finset.sum_const,
      Finset.card_univ,site_card,nsmul_eq_mul,Nat.cast_pow]; field_simp
  nth_rw 1 [← he]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro p _; rw [norm_mul, mode_real _ _ (real_frequency p), one_mul]; exact H v n p _ _

-- Upon the actually retained floor, compatibility with the inverse on the
-- real cochain quotient is exact. These hypotheses are not implicit coercivity
-- claims about arbitrary (e.g. cut) path generators.
section interface
variable {A : Bed} {V : RG.Clip} {η D l : ℝ} (h : Floor A V n η D) (he : 0<η)
variable {v : Train j} (hv : Defined k l v A) (hj : 4≤ j) (hr : 0<k)

include hv hj hr h he
lemma scalar_eq_screen : scalarCov k v n = Resolve.screenP h he := by
  have ht := Resolve.circuit h he hj hr v l hv
  simp_rw [signal_unit] at ht
  exact (scalar_circuit hr v n).lands ht (rotations_crew n _)

end interface
end YM.PhysicalNext.RankCovariance
