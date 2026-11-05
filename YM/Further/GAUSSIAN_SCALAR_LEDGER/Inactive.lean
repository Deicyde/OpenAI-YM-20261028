import YM.Further.GAUSSIAN_SCALAR_LEDGER.Balance
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Threshold
import YM.Next.SCHEDULE.Postal


set_option warningAsError false

/-! Identity on omitted frozen block even for windows of varying shape
(with full precision, no boundary row deletion). Tree identity block by
same argument, in this service use only Free from the start.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice Tree RG
open Round (rowRate)
open YM.Progress.StationaryScenes.Green
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {c f : Side} {g : Ratio c f} {F : Forest g} {G : Gauge} (H : Finset F.Free)
  (A : Wall (Bits G H))
local notation "e" => mergeBits H G

lemma coast (x : Hold G H) (j : Key F G) : filled H A (e (Sum.inr x)) j = (1 : Wall (Key F G)) (e (Sum.inr x)) j ∧
    filled H A j (e (Sum.inr x)) = (1 : Wall (Key F G)) j (e (Sum.inr x)) := by
  obtain ⟨i,rfl⟩ := (e).surjective j
  have he := sortBits H A (1 : Wall (Hold G H)); unfold filled
  rw [show meet H A 1 _ _ =_ from congr_fun (congr_fun he (Sum.inr x)) i,
      show meet H A 1 _ _=_ from congr_fun (congr_fun he i) (Sum.inr x)]
  cases i <;> simp [Matrix.one_apply]

namespace Lens

private lemma eye_cancel {ι : Type*} [Fintype ι] [DecidableEq ι] {A T : Wall ι} (i : ι)
    (he : ∀ j, A i j=(1 : Wall ι) i j) (h : A*T=1) (j : ι) :
    T i j=(1 : Wall ι) i j := by
  have hh : (A*T) i j=((1 : Wall ι)*T) i j := by rw [Matrix.mul_apply,Matrix.mul_apply]; simp_rw [he]
  rw [h,one_mul] at hh
  exact hh.symm

-- general inert coordinate of full matrix (use also tree links if completing to all links).
theorem shields {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Lens ι)
    {A : Wall ι} (h : A.PosDef) (i : ι)
    (he : ∀ j, A i j=(1 : Wall ι) i j) (j : ι) :
    Z.visit A 0 i j=(1 : Wall ι) i j ∧ Z.visit A 0 j i=(1 : Wall ι) j i := by
  have hr (x : ι) (u : i∈Z.eye x) (v : j∈Z.eye x) :
      ((plus (Z.glass A x) 0)⁻¹) ⟨i,u⟩ ⟨j,v⟩=(1 : Wall ι) i j ∧
      ((plus (Z.glass A x) 0)⁻¹) ⟨j,v⟩ ⟨i,u⟩=(1 : Wall ι) j i := by
    let I := Z.glass A x
    have hI : I.PosDef := h.submatrix Subtype.val_injective
    let k : (Z.eye x) := ⟨i,u⟩
    let l : (Z.eye x) := ⟨j,v⟩
    have HH (d : (Z.eye x)) : (1 : Wall (↥(Z.eye x))) k d=(1 : Wall ι) i d.val := by
      simp [Matrix.one_apply,Subtype.ext_iff,k]
    have ha (d : (Z.eye x)) : I k d=(1 : Wall (↥(Z.eye x))) k d := by rw [HH]; exact he _
    have hp := (eye_cancel k ha (mul_nonsing_inv I (isUnit_iff_ne_zero.mpr hI.det_pos.ne')) l).trans (HH l)
    rw [show plus (Z.glass A x) 0=I by simp only [plus,zero_smul,add_zero,I]]
    refine ⟨hp,?_⟩
    change I⁻¹ l k = _
    rw [show I⁻¹ l k=I⁻¹ k l from congr_fun (congr_fun (show I⁻¹ᵀ=I⁻¹ by simpa [Matrix.IsHermitian] using hI.inv.1) k) l]
    refine hp.trans ?_
    change (1 : Wall ι) i j = _; by_cases hx : i=j <;> simp_all only [Matrix.one_apply,eq_comm]
  unfold visit; simp only [of_apply]; constructor
  · split
    · next hx => exact (hr j hx (Z.sees j)).1
    next hx => exact (Matrix.one_apply_ne (show i ≠ j from fun H => hx (H.symm ▸ Z.sees _))).symm
  split
  · next hx => exact (hr i (Z.sees i) hx).2
  next hx => exact (Matrix.one_apply_ne (show j ≠ i from fun H => hx (H.symm ▸ Z.sees _))).symm

-- Consequently symmetric covariance and especially projector for `fieldLaw` on active coordinates.
lemma muted (Z : Lens (Key F G)) (h : (filled H A).PosDef) :
    let W := RawPrice.field Z (filled H A)
    filled H (blankOut H W)=W := by
  intro W
  have hs : W.IsHermitian := RawPrice.field_transpose Z _
  have ht := hermitian_filled _ _ (show (blankOut H W).IsHermitian from hs.submatrix _)
  have hb (i : Hold G H) (j : Key F G) : W (e (Sum.inr i)) j = (1 : Wall (Key F G)) (e (Sum.inr i)) j := by
    let t := e (Sum.inr i)
    have hh (b : Lens (Key F G)) := b.shields h t (fun x => (coast _ _ i x).1) j
    unfold W RawPrice.field; rw [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,(hh Z).1,(hh Z).2]
    rw [show (1 : Wall (Key F G)) j t=(1 : Wall (Key F G)) t j from
      congr_fun (congr_fun (Matrix.transpose_one (n:=Key F G) (α:=ℝ)) t) j]; rw [smul_eq_mul]; ring
  ext i j
  obtain ⟨u,rfl⟩ := (e).surjective i; obtain ⟨v,rfl⟩ := (e).surjective j
  cases u with
  | inr l => rw [(coast ..).1,hb]
  | inl x =>
    cases v with
    | inl y => exact congr_fun (congr_fun (blank_meets H (blankOut H W) 1) x) y
    | inr y =>
      have H : Wᵀ=W := by simpa [Matrix.IsHermitian] using hs
      rw [(coast ..).2,← show W _ _=W _ _ from congr_fun (congr_fun H (e (Sum.inl x))) (e (Sum.inr y)),hb]
      simp
end Lens

-- same for reference mean. Can take even if not using the symbol the
-- source recommends, but here's that formula.

def spreadBits (b : VV (Bits G H)) (x : Key F G) : ℝ := Sum.elim b (fun _ : Hold G H => 0) ((e).symm x)
def viewBits (b : VV (Key F G)) (x : Bits G H) : ℝ := b (e (Sum.inl x))

lemma sees_mean (Z : Lens (Key F G)) (b : VV (Bits G H)) (h : (filled H A).PosDef) :
    let M := RawPrice.meanAt Z (filled H A) (spreadBits H b)
    spreadBits H (viewBits H M)=M := by
  intro M; funext i; obtain ⟨x,rfl⟩ := (e).surjective i; unfold spreadBits; rw [Equiv.symm_apply_apply]
  cases x with
  | inl x => rfl
  | inr j =>
    change 0=M (e (Sum.inr j))
    unfold M RawPrice.meanAt
    have he (k) := Z.shields h (e (Sum.inr j)) (fun i => (coast _ _ _ _).1) k
    rw [neg_mulVec]
    simp only [Pi.neg_apply, Matrix.mulVec,dotProduct,Matrix.transpose_apply, (he _).2, Matrix.one_apply,ite_mul, one_mul, zero_mul]
    simp [spreadBits]

end YM.Further.GaussianScalar
