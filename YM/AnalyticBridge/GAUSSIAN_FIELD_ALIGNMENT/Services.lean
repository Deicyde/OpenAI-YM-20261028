import Mathlib.Analysis.Complex.ExponentialBounds
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Charges
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.PRICE_COMPILER.Suppression
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff


set_option warningAsError false

/-!
# Common step on one priced schedule

Increase Delays BEFORE
any commitment (can preserve Ringing and order, and pass a DelayLe to other
gates).

No retroactive claim for every arbitrary Permit or Directed.

Read the unmasked path comparator from Installed/Motor ON THIS schedule; it
doesn't *define* another fluctuation law independently of the paths and
stages.

Use with `Ready.to_whole`, `unmasked` etc and all frozen variables
retained.

Also swap Gaussian and μ₀ prescriptions together *exactly* in a
whole RG sector integral (including false flag cells).

This reissues an
integrable expression and keeps the determinant/mean/affine/quadratic
corrections; does not ask to drop guards just because the covariance
comparison itself pays.

No assertion of budgets for locality of the entire
remaining density or of completed normalized interacting histories.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment
open Function Filter Set Lattice RG RG.Supply Precision Wilson Pressure Tree Matrix MeasureTheory Bid
open Testing Stores Push.PriceCompiler Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows 
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}



section clocks
variable {L : Sheet G} {D : Rolls L} {Θ : Protection D} {W : Delays Θ} {Z : ChartRatio G} {K : MapPrices}

structure Rates where
  s : ℝ
  η : ℝ
  C : ℝ
  D : ℝ
  width_pos : 0 < s
  η_pos : 0 < η
  cost_pos : 0 < C
  tail_nn : 0 ≤ D

abbrev Tickets := ℕ → ℕ → Rates

def Both (K : MapPrices) (D : Rolls L) (j i : ℕ) (r : Rates) (x : ℝ) :=
    ∀ (c f : Side) (S : StepData c f), S.patch.J=j → S.patch.L=D.L j → Larger (G:=G) S → 100*(1+radiusB x) ≤ c.val →
      ∀ T : Tube G S, (query L K j i).Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c),
      A.flags = RG.flags (temp x) V ∨ V=1 → GaussianFieldAlignment.Ready A F x T k V r.s r.η r.C r.D

def Earned (K : MapPrices) (W : Delays Θ) (r : Tickets) := ∀ j i, StepStages j i → L.first ≤ i → ∀ x,
    W.betaEntry j ≤ x → Both K D j i (r j i) x

lemma increase {w a E : ℕ → ℕ → ℝ} (h : Cosmos Z K W w a E) {W' : Delays Θ} (H : DelayLe W W') : Cosmos Z K W' w a E := by
  intro j i he hj
  obtain ⟨hu,hv,hx⟩ := h j i he hj
  exact ⟨hu,hv,fun x hi => hx x ((H.beta j).trans hi)⟩

/-- Use also with the earlier free and/or nonlinear cost gates by passing in
their W, not by selecting from two unrelated schedules. β,g,w etc from the
actual Sheet and Ringing; no reinterpretation of the chart Jacobian. -/
theorem issue_windows (W : Delays Θ) (hZ : LocalRatio Z) {w : ℕ → ℕ → ℝ} (h : Ringing K w W) :
    ∃ (W' : Delays Θ) (r : Tickets) (a E : ℕ → ℕ → ℝ), DelayLe W W' ∧ OrderedDelays W' ∧
      ∀ W'' : Delays Θ, DelayLe W' W'' → Ringing K w W'' ∧ Cosmos Z K W'' w a E ∧ Earned K W'' r := by
  obtain ⟨Y,hY,h',a,E,hE⟩ := issue_cosmos Z K hZ W w h
  have hy : DelayLe W Y := ⟨hY.1,hY.2,hY.shells,hY.power⟩
  have he (j i : ℕ) : ∃ r : Rates, ∀ᶠ x : ℝ in atTop, StepStages j i → L.first ≤ i → Both K D j i r x := by
    by_cases hi : StepStages j i ∧ L.first ≤ i
    · have h₄ := L.cut.trans (hi.2.trans hi.1.1)
      let P : Patch := ⟨D.L j,j,h₄,(D.large j).size,(D.large j).odd⟩
      obtain ⟨s,η,C,D',hs,ht,hC,hD,H⟩ := purchase (query L K j i) P (L.has P)
      refine ⟨⟨s,η,C,D',hs,ht,hC,hD⟩,H.mono fun x hx _ _ => ?_⟩
      intro c f S he hl hL hc T hT; exact hx _ _ S _ (by
        rcases h : S.patch with ⟨L,J,H,h₁,h₂⟩; rw [h] at he hl
        change J=j at he; change L=D.L j at hl; subst J L; rfl) hL hc hT
    exact ⟨⟨1,1,1,1,one_pos,one_pos,one_pos,zero_le_one⟩, Eventually.of_forall fun _ h h' => (hi ⟨h,h'⟩).elim⟩
  choose r hr using he
  let P := fun j x => ∀ i, StepStages j i → L.first ≤ i → Both K D j i (r j i) x
  have hp j : ∀ᶠ x in atTop, P j x := by
    filter_upwards [hr j j, hr j (j-1)] with x ht hl i hi
    have he : i ≤ j ∧ j ≤ i+1 := hi
    obtain rfl|hh := eq_or_ne i j
    · exact ht hi
    have e : i=j-1 := by omega
    rw [e]; exact hl (e ▸ hi)
  obtain ⟨Y',hB,ho,hU⟩ := delay_extra Y P (fun _ _ _ => True) hp (by simp)
  exact ⟨Y',r,a,E,hy.trans hB,ho,fun U hU' => ⟨Bid.recheck (hB.trans hU').beta h', increase hE (hB.trans hU'),
      fun j i hi he x hx => (hU U hU').1 j x hx i hi he⟩⟩

variable {Y : Bar W} {I : Wait Y} {a : Levels G} {r : Tickets} {w t E : ℕ → ℕ → ℝ}


end clocks

section use
variable {p : Before} {g : ℕ → ℕ} {D : Rolls (p.sheet G g)} {M : Preparations p D}
  {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G} {Z : Horizon a}
  {Q : ℕ → ℕ → PathData G} {r : Tickets}


end use

section directed
variable {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {q : PostCost D} {w t E : ℕ → ℕ → ℝ} {r : Tickets}
open RG.Shoot


end directed
end YM.AnalyticBridge.GaussianFieldAlignment
