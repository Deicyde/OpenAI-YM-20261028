import YM.AnalyticBridge.RESET_INCOME_PORT.Dial
import YM.AnalyticBridge.RESET_INCOME_PORT.Journal

set_option warningAsError false

/-!
# Sector integral pricing inputs -> `Income`

Issue along surviving input intervals. Exposes precise purchases needed,
including the common probes/path/template and *which* κ can be used in
the raw invoice. Both services use the ACTUAL pushed normalized-kernel
response (unnormalized finite Wilson densities with same tag choices and
scalar). Neither service produces the Income prices physically. In
particular, don't infer the required Catalog from fixed-volume continuity
of the inputs, nor dial motion from a value estimate, nor the existence of
one schedule/configuration fitting all estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open Push.PriceCompiler
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P) {q : ResetPrices}
    {s : Set ℝ} {g a E : ℕ → ℕ → ℝ} {N m p i j : ℕ}



/-- All-good Prereset log receipts alternate service. Here genuinely
uses exact matched path calculation on all-good and true local derivative
prices of the early activity budget, including equality points; still
leaves the post-template obligations explicitly in the hypotheses. For
the E-like choice even the dial Meter is purchased under the same gate
(`clothed`). No demand that catalogs have already issued Before quotes;
not asserting they can hold. -/
theorem journals (hW : Ringing K g W) (hc : Cosmos Z K W g a E) (hm : m < N) (Q : In B.a m p)
    (hL : ∀ x∈s, Lives B.bake N (m+1) p (Q x)) (hb : ∀ x∈s,(Q x).beta∈band B.a (m+1))
    (H χ u k) (F : Terms B.a m p) (V : Config G (B.a.S.side m p)) (hv : RG.flags (B.a.budget m).threshold V = ∅)
    (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x) :
    let e := assigned B N m p g a H χ u k
    ∀ (J : ℝ → Journal e) (v : ℝ → ℝ) (t : ℝ → HeadGas.Token) (l : ℝ → ℕ → ℝ),
      (∀ x∈s,(J x).Read (Q x) (fun V => v x * sites (B.a.S.side m p) - demand B N (Q x) V) (t x)) →
      (∀ x∈s,(J x).Rates (l x) (funds B.a m q / 4)) → Meter B q s (N:=N) F V →
      Catalog (board B N F) s (window B.a m q) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m) →
        Prereset B q s N m p Q v (fun x => (J x).prints) ∧ Income B N m p q s Q V F := by
  intro e J v t l H' H'' hM hC
  have hh := prepares B hW hc hm Q hL hb H χ u k q J v t l H' H''
  exact ⟨hh,hC,fun x hx => (hh.value_income hv hx).1,
    fun x hx => pays_surplus hg hm hv (hh.value_income hv hx).2.2,dial B hg hm hv hM hC⟩


end YM.AnalyticBridge.ResetIncome
