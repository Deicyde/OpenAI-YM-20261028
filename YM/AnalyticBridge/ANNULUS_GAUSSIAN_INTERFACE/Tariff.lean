import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Factor
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical


set_option warningAsError false

/-!
# Post-block price sheet. Charge honest Gaussian normalization factors

Canonical sector on Active A x F; pay the paired local log at the SAME
matrix windows as in `Factor`.

Keep all link-components.

Ratio and
kinetic charges not implied by this ticket.

Coupling powers from the
measure cost logs are post-L.

`exposed` or the separated E and marked
multipliers need additional payments.

No free re-entry under other
potentials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus.Tariff
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory
open YM.SectorNext.Remainder (coin)
open YM.SectorNext.Remainder.Affine
open YM.SectorNext.Remainder.Scales
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma tag (x : ℝ) (O : Stores S) (k : S.Choices) (D : ℕ) (U : Config G f) (hx : 1≤radiusB x) :
    tagRate (Visits.near O D x) k U ≤ Real.exp (
      streets (D+100) x O * Real.log (Fintype.card S.patch.FrameTag:ℝ) +
      Fintype.card Axis * streets (D+101) x O *Real.log (Fintype.card S.patch.Points:ℝ)) := by
  let N := Visits.near O D x
  let F : ℝ := Fintype.card S.patch.FrameTag; let B : ℝ := Fintype.card S.patch.Points
  have hh : 1≤F := Nat.one_le_cast.mpr Fintype.card_pos
  have hl : 1≤B := Nat.one_le_cast.mpr Fintype.card_pos
  let H := F^N.sites.card * B^N.bonds.card
  have hc (s : ℕ) {w : ℝ} (h : 1 ≤ w) : w ^ s = Real.exp (s*Real.log w) := by
    have ht := pow_pos (zero_lt_one.trans_le h) s
    rw [← Real.log_pow, Real.exp_log ht]
  apply (rate_cost N k U).2.trans
  change H ≤ _
  rw [show H= _ from congr_arg₂ (fun i j : ℝ => i*j) (hc N.sites.card hh) (hc N.bonds.card hl), ← Real.exp_add]
  apply Real.exp_monotone (add_le_add (mul_le_mul_of_nonneg_right (frame_street ..) (Real.log_nonneg hh))
    (mul_le_mul_of_nonneg_right (bond_street O D x hx) (Real.log_nonneg hl)))

def icePrice (J : ChartRatio G) := |Real.log J.scale|+Fintype.card G.ColorIndex *
    (|Real.log (Real.sqrt (2*Real.pi))|+(1/2:ℝ)*|Real.log 2|+1)
lemma water (J : ChartRatio G) : 0 ≤ icePrice J := by unfold icePrice; positivity

lemma spareCost (J : ChartRatio G) (hJ : LocalRatio J) {β r : ℝ} (hr : 1≤r) (hb : β∈Icc (r/2) (2*r)) :
    -Real.log (spare J β) ≤ icePrice J * (1+Real.log r) := by
  have hy := zero_lt_one.trans_le hr
  have hp := lt_of_lt_of_le (half_pos hy) hb.1
  let N : ℝ := Fintype.card G.ColorIndex
  let u := Real.sqrt (2*Real.pi)
  let g := coupling β
  have hx : 0<u := by unfold u; have := Real.pi_pos; positivity
  have hs : 0<g := coupling_pos hp
  have he : spare J β = (u*g)^Fintype.card G.ColorIndex * J.scale := by
    unfold u spare g
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hs.le]
  have hv : Real.log g = -(1/2:ℝ)*Real.log β := by
    unfold g coupling; rw [Real.log_inv,Real.log_sqrt hp.le]; ring
  rw [he,Real.log_mul (pow_pos (mul_pos hx hs) _).ne' hJ.scale.ne',Real.log_pow, Real.log_mul hx.ne' hs.ne',hv]
  have hi : Real.log β ≤ Real.log 2+Real.log r := by rw [← Real.log_mul (by norm_num) hy.ne']; exact Real.log_le_log hp hb.2
  have h : 0≤N := Nat.cast_nonneg _
  let D := |Real.log u| + (1/2:ℝ)*|Real.log 2|+1
  have hb : -(Real.log u+-(1/2:ℝ)*Real.log β) ≤ D*(1+Real.log r) := by
    have h : (1/2:ℝ) ≤ D := by unfold D; have := abs_nonneg (Real.log 2); have := abs_nonneg (Real.log u); linarith
    have hl := mul_le_mul_of_nonneg_right h (Real.log_nonneg hr)
    unfold D at *; linarith [neg_abs_le (Real.log u),le_abs_self (Real.log 2)]
  change -(N*_+_) ≤ (|Real.log J.scale|+N*D)*(1+Real.log r)
  have hu := le_mu J
  linarith only [mul_le_mul_of_nonneg_left hb h, mul_nonneg (abs_nonneg (Real.log J.scale)) (Real.log_nonneg hr),hu]
where
  le_mu J : -(Real.log (J:ChartRatio G).scale) ≤ |Real.log J.scale| := by linarith [neg_abs_le (Real.log J.scale)]

def basis (d : ℕ) : ℝ := 4*((2*d+1:ℕ):ℝ)^4
lemma basis_pos (d : ℕ) : 0 ≤ basis d := by unfold basis; positivity

def lots (L : Side) := (L.val:ℝ)^4*(Fintype.card Axis:ℝ)
lemma lots_pos (L : Side) : 0 ≤ lots L := by unfold lots; positivity

def payroll (P : Patch) (J : ChartRatio G) (D : ℕ) (E : ℝ) :=
    basis (D+100) * Real.log (Fintype.card P.FrameTag:ℝ) + Fintype.card Axis * basis (D+101) * Real.log (Fintype.card P.Points:ℝ) +
      lots P.L * (basis (D+1) * E + basis 11 * icePrice J)
lemma payroll_nn (P : Patch) (J : ChartRatio G) (D : ℕ) {E : ℝ} (h : 0 ≤ E) : 0 ≤ payroll P J D E := by
  have hg (ι : Type) [Fintype ι] [Nonempty ι] : 0 ≤ Real.log (Fintype.card ι:ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr Fintype.card_pos)
  unfold payroll; have ha := basis_pos (D+100); have hb := basis_pos (D+101); have hv := basis_pos 11
  have he := basis_pos (D+1); have := water J; have := hg P.FrameTag; have := hg P.Points; have := lots_pos P.L; positivity

lemma funds (T : Tube G S) (x : ℝ) (V : Config G c) (A O : Stores S) (F : Forest S.ratio) (D : ℕ)
    (J : ChartRatio G) (hJ : LocalRatio J) (k : S.Choices) {β E : ℝ}
    (hx : 1 ≤ radiusB x) (hy : 1 ≤ y G S.patch.L x)
    (hb : β∈Icc (y G S.patch.L x/2) (2*y G S.patch.L x))
    (hE : 0≤E) (he : ∀ i∈pairsAt O F D x, LocalLog.paired T x V A k F i ≤ E) :
    let P := S.patch
    streets (D+100) x O * Real.log (Fintype.card P.FrameTag:ℝ) +
      Fintype.card Axis * streets (D+101) x O *Real.log (Fintype.card P.Points:ℝ) + LocalLog.write T x V A O k F D +
      quotaCharge x A F J β (freezeAt O A x F) ≤ valuation O (payroll P J D E) 4 x G := by
  intro P
  let K := b x ^4 * O.shares
  have h i : streets i x O = basis i*K := by unfold K streets basis; ring
  have hK : 0≤K := by unfold K; positivity
  let w := 1+Real.log (y G S.patch.L x)
  have hw : 1≤w := le_add_of_nonneg_right (Real.log_nonneg hy)
  let n := lots P.L
  have ha : LocalLog.write T x V A O k F D ≤ n * basis (D+1) * E * K := calc
    _ ≤ ∑ _i∈pairsAt O F D x,E := Finset.sum_le_sum he
    _ = (pairsAt O F D x).card*E := by simp
    _ ≤ n * streets (D+1) x O * E := mul_le_mul_of_nonneg_right (bond_pairs O F D x hx) hE
    _ = _ := by rw [h]; ring
  have hb : quotaCharge x A F J β (freezeAt O A x F) ≤ n*basis 11*icePrice J*K*w := by
    let m : ℝ := (freezeAt O A x F).card
    have hk : m ≤ n * streets 11 x O := frozen_street O A F x hx
    have hu : 0≤ icePrice J * w := mul_nonneg (water J) (zero_le_one.trans hw)
    calc
      _ = m * -Real.log (spare J β) := by unfold quotaCharge m; ring
      _ ≤ m * (icePrice J * w) := mul_le_mul_of_nonneg_left (spareCost J hJ hy hb) (Nat.cast_nonneg _)
      _ ≤ (n*streets 11 x O)*(icePrice J * w) := mul_le_mul_of_nonneg_right hk hu
      _ = _ := by rw [h]; ring
  let a := basis (D+100) * Real.log (Fintype.card P.FrameTag:ℝ) + Fintype.card Axis * basis (D+101) * Real.log (Fintype.card P.Points:ℝ)+
      n*basis (D+1)*E
  have hA : 0 ≤ a := by
    have hh := Real.log_nonneg (Nat.one_le_cast.mpr Fintype.card_pos : 1 ≤ (Fintype.card P.FrameTag:ℝ))
    have hh := Real.log_nonneg (Nat.one_le_cast.mpr Fintype.card_pos : 1 ≤ (Fintype.card P.Points:ℝ))
    unfold a; have h0 := basis_pos (D+100); have h1 := basis_pos (D+101); have h2 := basis_pos (D+1); have h3 := lots_pos P.L
    positivity
  rw [h,h]
  have hg := le_mul_of_one_le_right (mul_nonneg hA hK) hw
  have hc : valuation O (payroll P J D E) 4 x G = (a+n*basis 11*icePrice J)*K*w := by
    unfold payroll a valuation coin K w n; ring
  rw [hc]; unfold a at *; linarith only [hg,hb,ha]

lemma accumulated (O : Stores S) (H h : ℝ) (n x) (hH : 0≤H) (hh : 0≤h)
    (hy : 1≤y G S.patch.L x) :
    valuation O H n x G + valuation O h 4 x G ≤ valuation O (H+h) (max 4 n) x G := by
  have hl : 0≤1+Real.log (y G S.patch.L x) := by have := Real.log_nonneg hy; linarith
  have hp := size x
  unfold valuation coin; rw [add_mul (a:=H),add_mul,add_mul]; gcongr <;> omega
end YM.AnalyticBridge.Annulus.Tariff
