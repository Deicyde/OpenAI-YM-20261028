import YM.Next.SCHEDULE.Post
import YM.Progress.DIRECTED_RECIPE.Tender

/-!
# Financing an Ingredients purchase

Given actual `Quotes` etc, this gives one way estimators may meet the
Ingredients geometry. Do NOT assume that the hard/soft populations
will have estimates of this shape! Here if enough entering size at THAT
stage pair, for all periods, we can do the (+1) joint attachment purchase
from separate post-L exponential / power hit bounds. Powers remain explicit.
Topology (`Passage` and `Menu.curve`) separate. Use beta boosts BEFORE Bar
on the same auctions as in `before_kin`. Applies even at level zero.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe.Payments

open Function Set RG Lattice Wilson RG.Shoot Ovens Ovens.Pipes
open Next.Scheduling Next.Scheduling.Clock RG.Supply MeasureTheory Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

/-- These estimates themselves are obligations. C,L constants post-L. Both
populations on the stronger support metric. Use y (fine hat) not β at bulk.
`rate` in F must have been chosen specifically to leave this reservoir. These
are *possible* budget comparisons, without conclusions about physics. -/
structure Pairing (F : Postage) where
  C : ℝ
  C_nonneg : 0 ≤ C
  r : ℝ
  after_L : F.rate < r
  d : ℕ
  e : ℝ
  p : ℝ
  weak : 0 < p

variable {F : Postage}

namespace Pairing
variable (P : Pairing F)

def mild (y : ℝ) := P.C * (1+(cover y:ℝ))^P.d * Instrument.plain.P y ^ P.e * gap y ^ P.p

def strong (y β : ℝ) := P.C * Real.exp (-P.r * (Instrument.plain.t y/gap β)^(2:ℕ))

def kGoal (F : Postage) (y β : ℝ) := F.rate*(Instrument.plain.t y/gap β)^(2:ℕ)

private lemma charged (d : ℕ) (e p : ℝ) (hp : 0 < p) :
    Tendsto (fun x : ℝ => (1+(cover x:ℝ))^d* Instrument.plain.P x ^ e * gap x ^ p) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Instrument.plain.P x^(1+e)*gap x^p) atTop (𝓝 0) := light 2 _ _ hp
  have hh : Tendsto (fun x : ℝ => (1+(cover x:ℝ))^d/Instrument.plain.P x^(1:ℝ)) atTop (𝓝 0) :=
    ceiling_cheaper 2 _ _ one_lt_two zero_lt_one
  have H := hh.mul ht
  rw [zero_mul] at H
  refine H.congr fun x => ?_
  have he : 0<Instrument.plain.P x := wp _ _
  rw [Real.rpow_add he,Real.rpow_one]; field_simp

private lemma priced (d : ℕ) (a : ℝ) (ha : 0 < a) : Tendsto
    (fun y : ℝ => (1+(cover y:ℝ))^d * Real.exp (-a * Instrument.plain.P y ^ (2:ℕ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ => (1+(cover y:ℝ))^d * gap y) atTop (𝓝 0) := by
    simpa using charged d 0 1 zero_lt_one
  have h := ht.mul (burnt (-1) a 2 2 ha one_lt_two zero_lt_two)
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have he := gp hy
  simp only [Real.rpow_neg_one,Real.rpow_two]
  unfold Instrument.P; field_simp; rfl

/-- Pair step. Uniform β. `a` coarse (or same hat for startup) with
cover not exceeding fine `y`. All interpolation here is about prices.
`strong` through ALL β allowed; startup callers can choose this e.g. at β=y
and pay a common sup hit. -/
lemma currency : ∀ᶠ y : ℝ in atTop, 1 < y ∧
    ∀ β, inBand y β → ∀ B ≤ cover y, Rates B (Real.exp (-kGoal F y β))
      (P.strong y β) (P.mild y) (kGoal F y β) := by
  let M := Instrument.plain.P
  have hP := P.after_L
  let η : ℝ := (P.r-F.rate)/4
  have heta : 0<η := by unfold η; linarith
  have hpay d : Tendsto (fun y : ℝ => (1+(cover y:ℝ))^d * P.mild y) atTop (𝓝 0) := by
    have he := (charged (d+P.d) P.e _ P.weak).const_mul P.C
    rw [mul_zero] at he
    refine he.congr fun x => ?_
    simp only [Pairing.mild, pow_add]; ring
  let h y := P.C * Real.exp (-η*M y^ (2:ℕ))
  let v y := h y + 2*P.mild y
  have hz d : Tendsto (fun y : ℝ => (1+(cover y:ℝ))^d * v y) atTop (𝓝 0) := by
    have ht := ((priced d η heta).const_mul P.C).add ((hpay d).const_mul 2)
    simp only [mul_zero, add_zero] at ht
    apply ht.congr
    intro y; unfold v h M; ring
  have Hv : Tendsto v atTop (𝓝 0) := by simpa using! hz 0
  have he : Tendsto (fun y => 2^(4:ℕ)*((1+(cover y:ℝ))^ (4:ℕ) * v y)) atTop (𝓝 0) := by
    simpa using (hz 4).const_mul ((2:ℝ)^ (4:ℕ))
  have hf : Tendsto (fun y => Real.exp (v y)-1) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_exp.continuousAt.tendsto.comp Hv).sub_const 1
  have hm : Tendsto P.mild atTop (𝓝 0) := by simpa using! hpay 0
  filter_upwards [eventually_gt_atTop (1:ℝ),he.eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)),
    hf.eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)),hm.eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with y hy ht hu hq
  refine ⟨hy, fun β hb B hi => ?_⟩
  let z := gap β
  have h0 : 0<y := lt_trans zero_lt_one hy
  obtain ⟨ha,hc⟩ := band_gap y β h0 hb
  have hY : 0 < gap y := gp h0
  have hy' : 0<M y := wp _ _
  have hx : 0<gap β := by linarith
  have hg : M y/2 ≤ Instrument.plain.t y/z := by
    apply (le_div_iff₀ hx).2
    unfold Instrument.t
    change M y/2 * gap β ≤ gap y * M y; nlinarith only [hc,hy']
  have hs : Real.exp (kGoal F y β) * P.strong y β ≤ h y := by
    unfold strong h
    rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ P.C_nonneg
    apply Real.exp_monotone
    have he:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_pos hy' (by norm_num)).le hg 2)
      (show 0≤P.r-F.rate from sub_nonneg.mpr hP.le)
    change F.rate * (Instrument.plain.t y/z)^ (2:ℕ) + -P.r *_ ≤ -((P.r-F.rate)/4)*M y^ (2:ℕ)
    linarith
  have hC : 0 ≤ P.C := P.C_nonneg
  have hS : 0 ≤ P.strong y β := mul_nonneg hC (Real.exp_pos _).le
  have ht' : 0 ≤ P.mild y := by
    have hw : 0<Instrument.plain.P y := hy'
    unfold mild; positivity
  let γ := inflation (P.strong y β) (P.mild y) (kGoal F y β)
  have hγ : γ ≤ v y := add_le_add_left hs (2*P.mild y)
  have hh : 0 ≤ γ := add_nonneg (mul_nonneg (Real.exp_nonneg _) hS) (mul_nonneg zero_le_two ht')
  have hnorm : 0 ≤ kGoal F y β := mul_nonneg F.pos.le (sq_nonneg _)
  refine ⟨hnorm,hS,ht',hq,?_,?_⟩
  · apply le_trans ?_ ht
    change ((B+B+1:ℕ):ℝ)^ (4:ℕ) * γ ≤ (2:ℝ)^ (4:ℕ)*(_^ (4:ℕ) * v y)
    rw [← mul_assoc, ← mul_pow]
    have hi0 : (B:ℝ) ≤ cover y := by exact_mod_cast hi
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _) hγ hh (by positivity)
  unfold Bid.quote
  refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
  exact (sub_le_sub_right (Real.exp_monotone hγ) 1).trans hu


end Pairing

section charging
variable {G : Gauge} {s : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
variable {V : Protection D} {W : Delays V} {Y : Bar W} {I : Wait Y}

/-- One set of extra purchases. Pick the actual F and Pairing forecasts with
compatible prices (and reserve s.A across their analyses, not implied here).
Run BEFORE pricing W at the `before_kin` interface. -/
structure Treats {F : ℕ → ℕ → Postage} (P : ∀ i j, Pairing (F i j)) (W : Delays V) : Prop where
  all i j : Adj i j → ∀ x ≥ W.betaEntry i,
    let y := x+G.slopeConstant*Real.log (D.L i).val
    ∀ β, inBand y β → Rates (cover x) (Real.exp (-Pairing.kGoal (F i j) y β))
      ((P i j).strong y β) ((P i j).mild y) (Pairing.kGoal (F i j) y β)
  start i : ∀ x ≥ W.betaEntry i, Rates (cover x) (Instrument.plain.w x)
      ((P i i).strong x x) ((P i i).mild x) (Pairing.kGoal (F i i) x x)





open Pairing

variable {F : ℕ → ℕ → Postage} {P : ∀ i j, Pairing (F i j)} {a : Levels G}






end charging
end YM.Progress.DirectedRecipe.Payments
