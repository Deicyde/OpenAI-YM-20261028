import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Escrow

/-! # The scale of derivative payment at *every* admitted input beta in band, including chart cost

Desk widths & grades chosen before the threshold. Fields still priced in
context, with their own population and per-ancestor bills making up
`people`; we do not assume things like unit/stationary normalization or
Λ of other activities disappears in this result. The schedule actually
operates after shipping those separate costs too. But rank consumption is
polynomial in this data, even when the number of walks hitting the origin
or their unbounded length increase with the period (the price for
reanchoring vs long paths separately lives in EACH address hit receipt).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure Presented
open AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Reading Tariff SectorNext.Remainder
open MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {G : Gauge} {S : StepData c f} {Q : Kiosk} {k : ℕ} {θ : ℝ} {d : Desk G S}
    {H R ι α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    {X : Support c} {M : Income α β γ (H⊕R)} {j : ℕ} {N x y : ℝ} {P : Patch}

-- Explicit amounts at post-L. Use everywhere, no claim of acquiring the same
-- Growth polynomial order (plan) across other components that need more.
def deposit (G : Gauge) (P : Patch) (Q : Kiosk) (k j : ℕ) :=
  40 + k + ((j*(4*k):ℕ):ℝ) + ((P.L.val^4*Fintype.card Axis:ℕ):ℝ) +(Fintype.card G.ColorIndex:ℝ) +
    |Q.v.price|+8*|Q.cap|+ backFactor G + G.colorScale + ∑ i : G.ColorIndex, ‖Notice.term G i‖*|Q.L|

structure Safe (G : Gauge) (P : Patch) (Q : Kiosk) (k j : ℕ) (N : ℝ) : Prop where
  thirty : 30 ≤ N
  rank : (1+k:ℝ) ≤ N
  booth : ((j*(4*k):ℕ):ℝ) ≤ N
  projected : ((P.L.val^4*Fintype.card Axis:ℕ):ℝ) ≤ N
  colors : (Fintype.card G.ColorIndex:ℝ)≤ N
  growth : |Q.v.price|≤N
  pays : 8*Q.cap ≤ N
  base : 1 + backFactor G ≤ N
  dims : G.colorScale ≤ N
  toll b : 1 + ‖Notice.term G b‖ * |Q.L| ≤ N

lemma issuance (G P Q k j) : Safe G P Q k j (deposit G P Q k j) := by
  have hB : 0 ≤ backFactor G := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let t (b : G.ColorIndex) := ‖Notice.term G b‖*|Q.L|
  have ht i : 0≤t i := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hs := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>ht i)
  have hx := G.colorScale_pos
  have hh b := Finset.single_le_sum (fun i _=>ht i) (Finset.mem_univ b)
  have h1 := Nat.cast_nonneg (α:=ℝ) k; have h2 := Nat.cast_nonneg (α:=ℝ) (j*(4*k))
  have h3 := Nat.cast_nonneg (α:=ℝ) (P.L.val^4*Fintype.card Axis)
  have h4 := Nat.cast_nonneg (α:=ℝ) (Fintype.card G.ColorIndex)
  have h5 := abs_nonneg Q.v.price; have h6 := abs_nonneg Q.cap; have h7 := le_abs_self Q.cap
  unfold deposit
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,fun b=>?_⟩ <;> first | linarith only [h1,h2,h3,h4,hB,h5,h6,h7,hs,hx] | linarith only [hh b,h1,h2,h3,h4,hB,h5,h6,h7,hx]

def people (x : ℝ) (X : Support c) (M : Income α β γ ι) :=
    1 + (coverNumber (radiusB x) X:ℝ) + Fintype.card α + Fintype.card β + Fintype.card γ + |M.royalty| + ∑ i,M.wages i
lemma people_one (x : ℝ) (X : Support c) (M : Income α β γ ι) : 1≤people x X M := by
  unfold people; linarith [Nat.cast_nonneg (α:=ℝ) (coverNumber (radiusB x) X), Nat.cast_nonneg (α:=ℝ) (Fintype.card α), Nat.cast_nonneg (α:=ℝ) (Fintype.card β),Nat.cast_nonneg (α:=ℝ) (Fintype.card γ), abs_nonneg M.royalty, Finset.sum_nonneg (s:=Finset.univ) (fun i _=>M.wages_nn i)]

def sales (G : Gauge) (P : Patch) (x : ℝ) := Scales.b x * (1+Scales.p G P.L x)
lemma sells_poly (G P x) : Scales.b x ≤ sales G P x ∧ Scales.p G P.L x ≤ sales G P x := by
  have h := Scales.size x; have hv := Scales.pos G P.L x; unfold sales; constructor <;> nlinarith
lemma sells_one (G P x) : 1 ≤ sales G P x := (Scales.size x).trans (sells_poly G P x).1

def endow (d : Desk G S) (Q : Kiosk) (k j : ℕ) (X : Support c) (M : Income α β γ ι) := deposit G S.patch Q k j * sales G S.patch d.betaHat * people d.betaHat X M

lemma payout {x : ℝ} (h : 0<Scales.y G P.L x) {r : ℝ} (hr : 0<r) (ht : r ≤ 2*Scales.y G P.L x) :
    ‖(coupling r)⁻¹‖*fiery G x P.L ≤ 2*Scales.p G P.L x := by
  rw [coupling,inv_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _),Scales.fi]
  have he : √r * Scales.g G P.L x ≤ 2 := by
    have hR := Scales.yg2 G P.L h; have hz := Scales.gauge G P.L h
    have ht' := mul_le_mul_of_nonneg_right ht (sq_nonneg (Scales.g G P.L x)); rw [mul_assoc, hR] at ht'
    rw [← Real.sq_sqrt hr.le] at ht'; nlinarith only [ht']
  rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right he (Scales.pos ..).le

lemma endows (h₀ : 0<Q.cap) (hj : max 1 M.plan ≤ j) (ht : d.out.threshold=temp d.betaHat)
    (hr : 0<d.input.beta) (hv : d.input.beta ≤ 2*Scales.y G S.patch.L d.betaHat)
    (hx : 0<Scales.y G S.patch.L d.betaHat) (hB : temp d.betaHat ≤ 2*fiery G d.betaHat S.patch.L) : Escrow X M d Q k j (endow d Q k j X M) := by
  let u:=deposit G S.patch Q k j; let w:=sales G S.patch d.betaHat; let z:=people d.betaHat X M; let t:=Scales.p G S.patch.L d.betaHat
  have he := issuance G S.patch Q k j; have h := he.thirty; have hu : 30 ≤ u := h
  have hw := (show 1≤w from sells_one ..); have hz := (show 1≤z from people_one ..)
  have hy : u*w ≤ endow d Q k j X M := le_mul_of_one_le_right (by positivity) hz
  have hU : u ≤ endow d Q k j X M := (le_mul_of_one_le_right (by positivity) hw).trans hy
  have hW : w ≤ endow d Q k j X M := (le_mul_of_one_le_left (by positivity) (show 1 ≤ u by linarith)).trans hy
  have hZ : z ≤ endow d Q k j X M := le_mul_of_one_le_left (by linarith) (by nlinarith : 1≤u*w)
  have ht' : ‖d.g⁻¹‖*fiery G d.betaHat S.patch.L ≤ 2*t := payout hx hr hv
  have hN : 4*t ≤ endow d Q k j X M := (mul_le_mul (b:=u) (by linarith) (sells_poly G S.patch d.betaHat).2 (Scales.pos ..).le (by positivity)).trans hy
  have hK : max 1 ‖d.g⁻¹‖ * d.out.threshold ≤ endow d Q k j X M := by
    rcases max_choice (1:ℝ) ‖d.g⁻¹‖ with h|h
    · rw [h,one_mul]; exact d.out.threshold_le.trans ((by linarith : 1≤u).trans hU)
    rw [h,ht]; exact (mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans (by linarith only [ht',hN])
  refine ⟨⟨hu.trans hU,he.rank.trans hU,he.booth.trans hU,(sells_poly G S.patch _).1.trans hW,
      he.projected.trans hU,he.colors.trans hU,he.growth.trans hU,⟨h₀,he.pays.trans hU⟩,he.base.trans hU,he.dims.trans hU,fun i=>(he.toll i).trans hU,
      hK,by have := Scales.pos G S.patch.L d.betaHat; unfold t at *; linarith only [ht',hN,this]⟩,hj,⟨?_,?_,?_⟩,?_,?_,?_⟩ <;> refine le_trans ?_ hZ <;> unfold z people <;>
      linarith [Nat.cast_nonneg (α:=ℝ) (coverNumber (radiusB d.betaHat) X), Nat.cast_nonneg (α:=ℝ) (Fintype.card α), Nat.cast_nonneg (α:=ℝ) (Fintype.card β),Nat.cast_nonneg (α:=ℝ) (Fintype.card γ),abs_nonneg M.royalty,Finset.sum_nonneg (s:=Finset.univ) (fun i _=>M.wages_nn i)]

lemma outings (G : Gauge) (P : Patch) : ∀ᶠ x : ℝ in atTop, 0<Scales.y G P.L x ∧ temp x ≤ 2*fiery G x P.L := by
  filter_upwards [(Scales.year G P.L).eventually_gt_atTop 0,eventually_gt_atTop 0,
    (Work.E09.temp_ratio (G.slopeConstant * Real.log P.L.val)).eventually (le_mem_nhds (by norm_num : (1/2:ℝ)<1))] with x hx hp h
  refine ⟨hx,?_⟩; have ht := (le_div_iff₀ (Work.E09.temp_pos hp)).mp h; unfold fiery betaF; linarith
end YM.PhysicalNext.JointLoad.Folio
