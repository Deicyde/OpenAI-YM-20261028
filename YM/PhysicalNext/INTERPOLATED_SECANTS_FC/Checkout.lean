import YM.Extra.WILSON_STARTUP.Channels
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Labor
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Reset
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Tariff

/-!
# Absolute and relative earnings before and through the actual freset

Quantitative numbers, not certificates of physical availability.

The primary purchases for
the remaining analytic inputs are accounted **assuming** the sharp/late coefficients in
`front` actually apply (unverified).

See the physical application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Lattice RG Wilson Pressure Filter Function Set Push.AbsoluteSums AnalyticBridge.VerifiedReset Collection Trees
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {n : Side}

namespace Rate
structure Solvent (G : Gauge) (S : Stage) (p : BudgetPoint) (L : Side) (pre post U κ x : ℝ) : Prop where
  later : 1 < x
  fine : x ≤ betaF G x L
  paid : 0 ≤ stamp G L κ x
  tree : let y := betaF G x L
    degreePrice p.B (shrink y hitPower) 1 ≤ shrink y treePower ∧ shrink y treePower ≤ 1/2
  mass : frozenMass L p pre post (betaF G x L) ≤ screens G S (betaF G x L)
  transport : let y := betaF G x L
    shrink y lengthPower ≤ upper-lower ∧ frozenFee L p pre post y ≤ fees G S y/2
  moving : let y := betaF G x L
    movingFee L p pre post y ≤ fees G S y/2
  unions : let y := betaF G x L; let γ:=shrink y hitPower; let q:=shrink y treePower; let u:=shrink y lengthPower
    Content.mild γ q u ≤ 1 ∧ (Animals.ballCost p.B:ℝ)*Content.mergeHit γ q u ≤ 1/2
  path α : |α| ≤ U → let y := betaF G x L; let gold := stamp G L κ x
    let share := Receipts.share G p S.clip S.width S.paths α (screens G S y) (fees G S y)
    let recon := Receipts.recon (intense gold) share (gold/4)
    share ≤ 1 ∧ (Animals.ballCost p.B:ℝ)*recon ≤ 1 ∧ Bid.quote (gold/4) recon ≤ Real.exp (-((Vac.Numbers.P x) ^ ((1:ℝ)/5))) ∧
      regularNeed G p S.clip S.width S.paths 0 (fees G S y) ≤ shrink x velocity ∧
      Geo.Width p S.clip S.width ∧ (S.clip.direct ≤ 1 → WilsonStartup.Decent S.clip p)



end Rate
namespace Content
open Rate

variable {ι η H : Type*} (f : Content G n ι η H) (A : Shelf G n ι η)
/-- Still unverified external V/mixed jets and low cancellation prerequisites through the
original order and exact transports. Coefficients in `front` are known to the numerical tables
in advance. Does NOT follow from `AtEach` or `Curve`, nor generically from `Held`. The
separation from the Cab construction for part of these debts is in subsequent files. -/
structure EntryBill (p : BudgetPoint) (pre post : ℝ) (L : Side) (y b : ℝ) (h : H) : Prop where
  frozen : FrozenOrders f A.toPlacement p h y (Quotes.preExponent p) (shrink y Rate.hitPower/8) (shrink y treePower)
  known : Deficit f A.toPlacement p h y (Quotes.preExponent p) (front pre post L y size)
  smooth i : p.Regular ((A.listing p).reg i).support ((f.issue A p y b h).logRead i)

variable {f A} {p : BudgetPoint} {pre post U κ x b b' D : ℝ} {path : ℝ → H} {S : Stage} {L : Side}
    (he : Solvent G S p L pre post U κ x)
    (hb : EntryBill f A p pre post L (betaF G x L) b (path 1)) (hb' : EntryBill f A p pre post L (betaF G x L) b' (path 0))
    (hR : let y := betaF G x L; Moving f A.toPlacement p path b y (Quotes.preExponent p) D (shrink y Rate.hitPower) (shrink y treePower) (front pre post L y size)
      (shrink y Rate.helperPower))
    (h₁ : let y := betaF G x L; b ∈ Set.Icc (y/2) (2*y)) (h₂ : let y := betaF G x L; b'∈Set.Icc (y/2) (2*y))
    (hδ : |b-b'|/betaF G x L ≤ D)

private lemma order_fee : 0 ≤ Quotes.preExponent p := by unfold Quotes.preExponent; linarith [p.exponent_pos]
include he hb h₁

omit he h₁ hb in
private lemma rooted_pull {Y : ι → RegularAddress n} {V : ℕ ≃ ι} {a d : ℝ} {f : ∀ i, Reading G p (Y i) → ℝ}
    (h : (roots Y p.B a).Box f d) : (roots (Y∘V) p.B a).Box (fun i => f (V i)) d := by
  obtain ⟨c,hc,H⟩ := h
  exact ⟨c∘V,seated_iff.mpr ⟨fun i=>hc.positive _,fun o=>Extra.Iteration.Cost.equiv V ((seated_iff.mp hc).2 o)⟩,fun i => H _⟩

include hb' hR h₂ hδ
omit hb in
lemma earnings : let y := betaF G x L
    (roots (A.listing p).reg p.B (Quotes.preExponent p)).Box (U:=fun i => Reading G p ((A.listing p).reg i))
      (fun i u => u.jet ((f.issue A p y b (path 1)).logRead i)-u.jet ((f.issue A p y b' (path 0)).logRead i)) (D*fees G S y) := by
  intro y
  have hy : 0 < y := (zero_lt_one.trans he.later).trans_le he.fine
  have hD := (div_nonneg (abs_nonneg _) hy.le).trans hδ
  have hhp := frozen_change (hb'.frozen.widen he.tree.1) hb'.known order_fee hy (shrink y lengthPower) b b'
    (shrink_pos hy _) he.transport.1 h₁ h₂
  have hh := hR.change order_fee hb'.known hD (shrink_pos hy helperPower)
  have hv := mul_le_mul_of_nonneg_left he.moving hD
  have hV := mul_le_mul he.transport.2 hδ (div_nonneg (abs_nonneg _) hy.le) (by linarith [fees_pos G S hy])
  have hd := (hh.add hhp).relax (M':=D*fees G S y) (show D*movingFee L p pre post y + _* frozenFee L p pre post y ≤ _ by linarith only [hv,hV])
  simp_rw [sub_add_sub_cancel] at hd
  exact rooted_pull hd

variable (hHard : let y := betaF G x L; PairValues f A.toPlacement p (path 1) (path 0) b b' D (stamp G L κ x)
    (shrink y Rate.hitPower) (shrink y treePower) (shrink y lengthPower))
include hHard



end Content
end YM.PhysicalNext.InterpolatedSecantsFc
