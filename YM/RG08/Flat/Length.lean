import YM.RG08.Flat.Mesh

/-!
# Fix the length gate before the length. Sufficient numerical costs for kfalt 0
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior
open scoped Topology ENNReal

set_option autoImplicit false
variable {G : Gauge} {a : Levels G}

def curve (P : MapPrices) (j : ℕ) := min 1 (min (P.α j) (P.α (j+1)))

def Lambda (a : Levels G)(i : ℕ) := 2+Real.log (a.clock.hatBeta i)
def Lambda' (a : Levels G)(i : ℕ) := 1+Lambda a i

def Delay (a : Levels G)(P : MapPrices)(e : ℕ) := ∀ i,e ≤ i → P.Ω (a.clock.J i) ≤ Real.log (a.clock.hatBeta i)

def before (P : MapPrices)(j i : ℕ) :=
   let h:=allotment P j i
   (Fintype.card Faces:ℝ)*h*(Fintype.card Faces*(2/curve P j)*h)

def entrance (P : MapPrices) (j:ℕ) : ℝ := 2/curve P j + (before P j j)^2+(before P j (j-1))^2

def Enough (a : Levels G)(E : ℕ→ℕ) (e : ℕ) := ∀ i,e ≤ i → E (a.clock.J (i+1)) ≤ (a.S.block i).val

def tickets (P : MapPrices)(j:ℕ) := Nat.ceil (entrance P j)

theorem curve_pos (P : MapPrices)(j:ℕ) : 0 < curve P j := lt_min zero_lt_one (lt_min (P.alpha_pos _) (P.alpha_pos _))

private theorem near (S : Calendar G) (h:S.Fits)(i:ℕ) : S.J i=S.J (i+1) ∨ S.J (i+1) = S.J i + 1 := by
  have ht := h.stepSlow i
  have he := h.mono (show i ≤ i+1 by omega)
  omega

theorem universeClock (a : Levels G)(h : G.Simple)(k i : ℕ) : Real.log (a.clock.hatBeta i) ≤
    (1+G.slopeConstant)*clock a.S (Lambda' a) k i := by
  let s := G.slopeConstant
  have hs : 0 < s := Gauge.slopeConstant_pos h
  let v := a.clock.hatBeta i / a.clock.hatBeta k
  let r := |a.S.scale i-a.S.scale k|
  have hk := a.fits.delayed k
  have hi := a.fits.delayed i
  have hr : a.clock.hatBeta i ≤ a.clock.hatBeta k+s*r := by
    unfold Calendar.hatBeta; have hv := le_abs_self (a.S.scale i-a.S.scale k); change _ ≤ _+_+s*r; unfold s r at *; unfold Levels.S at *; nlinarith only [mul_le_mul_of_nonneg_left hv hs.le]
  have ht : v ≤ 1+s*r := by
    apply (div_le_iff₀ (zero_lt_one.trans hk)).mpr
    have hh : 0 ≤ s*r := mul_nonneg hs.le (abs_nonneg _)
    nlinarith
  have hv : Real.log (a.clock.hatBeta i) ≤ Real.log (a.clock.hatBeta k)+s*r := by
    have h₁ : 0 < v := div_pos (zero_lt_one.trans hi) (zero_lt_one.trans hk)
    have hb : Real.log v ≤ v-1 := Real.log_le_sub_one_of_pos h₁
    unfold v at hb
    rw [Real.log_div (zero_lt_one.trans hi).ne' (zero_lt_one.trans hk).ne'] at hb; linarith
  apply hv.trans
  unfold clock Lambda' Lambda
  have he := abs_nonneg (a.S.scale i - a.S.scale k)
  have hy := Real.log_pos hk
  unfold r s
  nlinarith

theorem spacing_choice (h:G.Simple) (P : MapPrices) {e} (hw:Enough a (tickets P) e)(ht:Delay a P e) :
    Spacing a P (Lambda' a) (curve P) (1/2) e := by
  refine ⟨fun k=>?_,curve_pos P,fun j=>(min_le_right ..).trans (min_le_left ..),fun _=>min_le_left ..,fun i _=> ?_,by norm_num,fun i hi=>?_,fun i hi=>?_,?age⟩
  case age => refine ⟨_,1,(zero_lt_one.trans_le (le_add_of_nonneg_right (Gauge.slopeConstant_pos h).le)).le,fun k i hi=>?_⟩; rw [pow_one]; exact (ht i hi).trans (universeClock a h k i)
  · unfold Lambda' Lambda; linarith [Real.log_pos (a.fits.delayed k)]
  · refine le_min (min_le_left ..) (le_min ?_ ((min_le_right ..).trans (min_le_left ..)))
    obtain he|he := near a.clock a.fits i
    · rw [he]; exact (min_le_right ..).trans (min_le_left ..)
    rw [he]; exact (min_le_right ..).trans (min_le_right ..)
  · let j := a.clock.J (i+1); let u := a.clock.J i; let L :ℝ:=(a.S.block i).val
    have hp : entrance P j ≤ L := (Nat.le_ceil _).trans (by unfold j L; exact_mod_cast hw i hi)
    have he := curve_pos P j
    have hL : 0 < L := by unfold L; positivity
    have hK : (before P j u)^2 ≤ L := by
      apply le_trans _ hp; unfold entrance; rcases near a.clock a.fits i with hv|hv
      · rw [show u=j from hv]; nlinarith [sq_nonneg (before P j (j-1)),div_nonneg (by norm_num : (0:ℝ)≤2) he.le]
      rw [show u=j-1 by change a.clock.J _=_; unfold j; omega]; nlinarith [sq_nonneg (before P j j),div_nonneg (by norm_num : (0:ℝ)≤2) he.le]
    change before P j u / L ≤ L ^ (-(1/2:ℝ))
    rw [Real.rpow_neg hL.le,← Real.sqrt_eq_rpow]
    have ht := Real.sq_sqrt hL.le
    field_simp [hL.ne', (Real.sqrt_pos.mpr hL).ne']
    have hb : before P j u ≤ Real.sqrt L := by nlinarith [Real.sqrt_pos.mpr hL]
    simpa only [← sq, ht] using (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg L)) -- simp?
  · let j := a.clock.J (i+1); let L :ℝ:=(a.S.block i).val
    have hp : entrance P j ≤ L := (Nat.le_ceil _).trans (by unfold j L; exact_mod_cast hw i hi)
    have he := curve_pos P j; have hK : 2 / curve P j ≤ L := by unfold entrance at hp; nlinarith only [hp,sq_nonneg (before P j j),sq_nonneg (before P j (j-1))]
    have hh : curve P (a.clock.J i) ≤ 1 := min_le_left ..
    replace hK := (div_le_iff₀ he).mp hK
    change _ ≤ L*curve P j; linarith
end YM.RG08.Flat
