import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Support
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Weighted

/-!
# A localized quadratic/linear insertion into the Gaussian density

Perturb a centered reference covariance C by exponential of a local
quadratic potential in a list of actual slots. Divide by its SAME-cloud
normalization. Price with explicit determinant and local volume results
(and a numerical upper price via the weighted Laplace test). Allows
large linear sources with their costs visible. `B` doesn't include any
constant charge outside the formula. In particular if using a piece of the
exponent of some RG integrand, that constant and all other pieces are
unchanged and *not* estimated here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open Multi.Vacuum (Gauss.pay)
open scoped Topology BigOperators Classical ENNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Finset ι} {C A J : Gaussian.Table ι} {t a : Vec ι} {B : Vec ι → ℝ} {p q L ε θ K : ℝ}

/-- For use with FURTHER Lq tests. -/
structure Inserted (S : Finset ι) (C A : Gaussian.Table ι) (a : Vec ι) (p K : ℝ) (B : Vec ι → ℝ) : Prop where
  reference_pos : C.PosDef
  installed_pos : A.PosDef
  varies (z : Vec ι) : variation A C (0-a) z = B z
  confined : Confined S A C (0-a)
  coercive : (mixed (marginalCov S A) (marginalCov S C) p).PosDef
  price : moment (marginalCov S A) (marginalCov S C) p (observe S (0-a)) ≤ K

section

variable (hI : Inserted S C A a p K B)
include hI















end

/-- Quadratic and linear inserted pieces. -/
def into (S : Finset ι) (J : Gaussian.Table ι) (t z : Vec ι) : ℝ :=
  t ⬝ᵥ maskVec S z + quad J (maskVec S z) / 2

def intoCost (p K ε θ L : ℝ) (n : ℕ) :=
  Real.exp (2*p*(n*(L^2/(4*θ)) + 2*K*(n*(θ + ε/2))))

lemma mask_le (v : Vec ι) : maskVec S v ⬝ᵥ maskVec S v ≤ v ⬝ᵥ v := by
  unfold dotProduct
  apply Finset.sum_le_sum
  intro i _
  simp_rw [maskVec_apply]; split
  · exact le_rfl
  · rw [zero_mul]; exact mul_self_nonneg _

lemma inserted_quad (hA : A.PosDef) (hi : A⁻¹ = C⁻¹-maskForm S J) (z : Vec ι) :
    variation A C (0-A *ᵥ maskVec S t) z = into S J t z := by
  rw [variation_expand hA, zero_sub, mulVec_neg, mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hA.det_pos.ne'), one_mulVec, dotProduct_neg, hi,
    sub_sub_cancel, maskForm_quad, dot_maskVec, dotProduct_comm (maskVec S z), sub_neg_eq_add, add_comm]
  rfl

private lemma into_bound (hθ : 0 < θ) (he : ∀ z : Vec ι, |quad J z| ≤ ε*(z ⬝ᵥ z))
    (hl : ∀ i ∈ S, |t i| ≤ L) (z : Vec ι) :
    |into S J t z| ≤ S.card * (L^2/(4*θ)) + Gauss.pay (fun i => if i∈S then θ+ε/2 else 0) z := by
  let b := maskVec S z
  let u := ∑ i ∈ S,z i^2
  have hs : b ⬝ᵥ b = u := by
    unfold b u dotProduct
    simp_rw [maskVec_apply]
    simp [apply_ite₂ (· * ·), sq]
  have ht : |t ⬝ᵥ b| ≤ S.card*(L^2/(4*θ)) + θ*u := by
    unfold dotProduct
    calc
      |∑ i,t i * b i| ≤ ∑ i, |t i| * |b i| := by
        simp_rw [← abs_mul]; exact Finset.abs_sum_le_sum_abs ..
      _ = ∑ i ∈ S, |t i| * |z i| := by
        simp only [b, maskVec_apply, apply_ite abs, abs_zero, mul_ite, mul_zero,
          Finset.sum_ite_mem, Finset.univ_inter]
      _ ≤ ∑ i ∈ S, (L^2/(4*θ) + θ*z i^2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hh := mul_le_mul_of_nonneg_right (hl i hi) (abs_nonneg (z i))
        refine hh.trans ?_
        apply (sub_le_iff_le_add).1
        rw [le_div_iff₀ (by linarith : 0 < 4*θ)]
        have hx : |z i|^2 = z i^2 := sq_abs _
        nlinarith only [sq_nonneg (2*θ*|z i|-L), show θ^2*|z i|^2 = θ^2*z i^2 by rw [hx]]
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, u]
  have hg := he b
  rw [hs] at hg
  unfold into
  refine (abs_add_le ..).trans ?_
  change |t ⬝ᵥ b| + |quad J b / 2| ≤ _
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), show Gauss.pay (fun i => if i∈S then θ+ε/2 else 0) z =
    (θ+ε/2)*u by unfold Gauss.pay u; simp only [ite_mul, zero_mul, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.mul_sum]]
  linarith

/-- Generic sufficient smallness test on a signed local quadratic-affine letter. Used below for
an insertion of true log-exponent terms. -/
theorem insert_letter (hC : C.PosDef) (hh : Ceiling C K) (hK : 0 < K) (hJ : J.IsSymm)
    (hε : 0 ≤ ε) (he : ∀ z : Vec ι, |quad J z| ≤ ε*(z ⬝ᵥ z))
    (ht : ∀ i ∈ S, |t i| ≤ L) (hp : 1 ≤ p) (hθ : 0 < θ) (hw : K*(p*(θ + ε/2)) ≤ 1/4) :
    let A := (C⁻¹ - maskForm S J)⁻¹
    Inserted S C A (A *ᵥ maskVec S t) p (intoCost p K ε θ L S.card) (into S J t) := by
  intro A
  let P := C⁻¹-maskForm S J
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hb : ε < K⁻¹ := by
    apply lt_of_mul_lt_mul_left (a:=K) _ hK.le
    rw [mul_inv_cancel₀ hK.ne']
    have hx : θ+ε/2 ≤ p*(θ+ε/2) := le_mul_of_one_le_left (by linarith) hp
    have hy := (mul_le_mul_of_nonneg_left hx hK.le).trans hw
    linarith only [hy, mul_pos hK hθ]
  have hg : FreeResolvent.Gap P (K⁻¹ - ε) := by
    constructor
    intro v
    unfold P; rw [sub_mulVec, dotProduct_sub]
    have h : quad (maskForm S J) v ≤ ε*(v ⬝ᵥ v) := calc
      quad (maskForm S J) v = quad J (maskVec S v) := maskForm_quad ..
      _ ≤ _ := (le_of_abs_le (he _)).trans (mul_le_mul_of_nonneg_left (mask_le v) hε)
    have hz := (inv_gap hC hh hK).lower v
    unfold quad at h
    linarith only [hz, h]
  have hP := posDef_of_gap hg ((isHermitian_iff_isSymm.mp hC.inv.isHermitian).sub
    (maskForm_symm hJ)) (sub_pos.mpr hb)
  have hA : A.PosDef := hP.inv
  have hi : A⁻¹ = P := nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ hP.det_pos.ne')
  let b := A *ᵥ maskVec S t
  have hs : Confined S A C (0-b) := by
    constructor
    · rw [hi]; intro i j ha; unfold P; rw [sub_sub_cancel]; exact maskForm_apply_of_not_mem J ha
    intro i ha; rw [zero_sub, mulVec_neg, show A⁻¹ *ᵥ b = _ from by unfold b; rw [mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hA.det_pos.ne'), one_mulVec], Pi.neg_apply,
      maskVec_apply, if_neg ha, neg_zero]
  have hd : ∀ z, variation A C (0-b) z = into S J t z := inserted_quad hA hi
  let W (i : ι) := if i∈S then θ+ε/2 else 0
  have h1 i : 0 ≤ W i := by unfold W; split <;> positivity
  have h2 i : K*(p*W i) ≤ 1/4 := by
    unfold W
    split
    · exact hw
    · norm_num
  have h3 : Weighted A C (0-b) W ((S.card:ℝ) * (L^2/(4*θ))) := by
    intro z
    rw [hd]
    exact into_bound hθ he ht z
  obtain ⟨hm,hy⟩ := weighted hA hC hh hK.le hp h1 h2 h3
  have hj := (mixed_local hA hC hs).1 hm
  refine ⟨hC,hA,hd,hs,hj,?_⟩
  change moment _ _ _ (observe S (0-b)) ≤ _
  rw [← moment_local hA hC hs hj]
  simpa [W, intoCost, mul_add] using hy

end YM.SectorTools.PhysicalGaussianInsertion
