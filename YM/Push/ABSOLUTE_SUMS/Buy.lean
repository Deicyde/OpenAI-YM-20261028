import YM.Push.ABSOLUTE_SUMS.Grants
import YM.Push.ABSOLUTE_SUMS.Mixed


/-!
# Actual gain and a compatible quote

A downstream use at the conditional interface needed for packet prices.

Quantifiers before doing any
particular volume, arity, choice of local tags.

No abstract Banach fixed
point or assumptions on sums of mixed clusters.

Includes demonstration
on real oriented factors, one U,V,k retained throughout a sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Buy
open Filter Lattice RG Mixed Pressure Wilson Grant Delay Reserves Tree
open scoped Topology BigOperators ENNReal Classical
variable (G : Gauge) (L : Side)

def tolerance (δ : ℝ) (B : ℕ) : ℝ := δ/(16*(Animals.ballCost B:ℝ))

/-- For this combinatorial interface: charge a short list of prices,
using HALF the guaranteed income as extractable mandatory marks.
Combinatorial degree q=1/2 convenient. -/
def quote (μ u a ε δ β x C extra spend γ : ℝ) : Costs where
  reserveTree := δ
  exponent := a
  reservePoly := ε
  cap := C
  spendSeed := spend
  extraSeed := extra
  markSeed := hatWin G L (μ/2) u x
  gain := credit β μ x G L
  optionalHit := γ
  packetRatio := retained G L (μ/2) u x
  rootHit := Real.exp (-hatWin G L (μ/2) u x/4) + γ
  q := 1/2

lemma needed {μ u δ : ℝ} (hm : 0 < μ) (hu : 0 < u) (hd : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-hatWin G L μ u x/4) ≤ tolerance δ (radiusB x) := by
  have hp : 0 < δ/16 := by positivity
  filter_upwards [Delay.sawn G L hm hu hp (show 0 ≤ (3:ℝ)^4 by norm_num) 4 (show (0:ℝ)<2 by norm_num)]
    with x hx
  let B := radiusB x; let c : ℝ := Animals.ballCost B; let y := Delay.bill G L x
  have he : 0 < c := by have he := Animals.neighbors_ge B; unfold c; positivity
  have hw := Delay.bill_ge G L x
  have hz : c ≤ (3:ℝ)^4 * y^4 := by
    unfold c Animals.ballCost; push_cast
    rw [← mul_pow]; gcongr
    have he : (B:ℝ) ≤ y := by unfold B y Delay.bill; linarith [sq_nonneg (Real.log (betaF G x L))]
    change 1 ≤ y at hw; linarith
  let v := Real.exp (-hatWin G L μ u x/4)
  have hk : (3:ℝ)^4*y^4*v ≤ δ/16 := by simpa only [Real.rpow_zero, mul_one] using hx
  have ht := (mul_le_mul_of_nonneg_right hz (show 0 ≤ v from (Real.exp_pos _).le)).trans hk
  change v ≤ δ/(16*c)
  rw [le_div_iff₀ (by positivity : (0:ℝ)<16*c)]; linarith

/-- Numeric sufficiency at issued μ and fixed L and test orders.
Arbitrary extra factors in the packet up to the **log** fee,
including C. Still need the optional prices small too. -/
lemma quoted {μ u a ε δ D z : ℝ} (hm : 0 < μ) (hu : 0 < u) (hd : 0 < δ) (ha : 0 ≤ a)
    (he : 0 < ε) (hD : 0 ≤ D) (hz : z < 2) (d l : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 < betaF G x L ∧ ∀ β C extra spend γ : ℝ,
      let B := radiusB x; let fee := D*Delay.bill G L x^d*fineMonitor G L x^z
      (u*betaF G x L ≤ β) → 0 ≤ extra → 0 ≤ C → C ≤ Real.exp fee → spend+2*ε*extra ≤ fee →
      0 ≤ γ → γ ≤ tolerance δ B →
      (quote G L μ u a ε δ β x C extra spend γ).Buy L l B := by
  have hp : 0 < μ/2 := half_pos hm
  filter_upwards [Delay.fits G L l hp hu (show 0 ≤ a+2*ε+δ by linarith) hD d hz,
    needed G L hp hu hd, shift_pos G L] with x hx hN ht
  refine ⟨ht, ?_⟩
  intro β C extra spend γ B fee hβ he' hC hb hc hi ho
  let M := hatWin G L (μ/2) u x
  let b := quote G L μ u a ε δ β x C extra spend γ
  have wy : 0 < M := Delay.win_pos G L x hp hu
  have hg : M ≤ b.gain - M := by
    have hv := Delay.comparison G L ht hm β hβ
    change hatWin G L μ u x ≤ b.gain at hv
    have he : hatWin G L μ u x = M+M := by unfold M hatWin; ring
    linarith only [hv,he]
  obtain ⟨hy,hq⟩ := hx (spend+2*ε*extra) (b.gain-M) C hc hg hC hb
  change b.Buy L l B
  have w : 0 < b.rootHit := add_pos_of_pos_of_nonneg (Real.exp_pos _) hi
  refine ⟨he,hd,w,hC,he',wy.le,ha,⟨hy.1,?_,hy.2.2⟩,?_,?_,by norm_num [b,quote]⟩
  · apply le_trans _ hy.2.1
    apply le_of_eq
    unfold Packets.ratioCost Packets.oneCost; dsimp only [Costs.head,Costs.spend,b,quote,B,M]; ring_nf
  · apply add_le_add_left
    change Packets.totalCharge L C l (radiusB x) b.packetRatio 0 ≤ Real.exp (-M/4)
    simpa only [M,b,quote,max_eq_left zero_le_one,Nat.cast_one,mul_one] using hq 0
  let y : ℝ := Animals.ballCost B
  have hz : 0 < y := by have he := Animals.neighbors_ge B; unfold y; positivity
  have hS : b.rootHit ≤ δ/(16*y)+δ/(16*y) := add_le_add hN ho
  change 4*(y*b.rootHit/δ) ≤ 1/2
  apply le_trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hz.le) hd.le) (by norm_num))
  apply le_of_eq; field_simp; ring

section Apply
variable {G}


end Apply
end YM.Push.AbsoluteSums.Buy
