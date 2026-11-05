import YM.AnalyticNext.GRID_STOP_ATTENUATION.Neighbors

set_option warningAsError false

/-!
# The once-only k-fork bill, allowed even exponential sqrt(betaHat)

Exponent estimates use the **specific clock and scale** of the
family. Compatible even if forced cost at k was paid only `Radial`,
as long as that radius and those parameters are themselves in budget.
No forced-factor loss asserted tolerable at successive internal steps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Planning
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Stock Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators Asymptotics
variable {G : Gauge} {C : Family G}

/-- Station bound, independent of N,p. Pointwise version used for
services with arbitrary refinement order. -/
def bear (C : Family G) (p : ℕ→ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,p k ≤ Real.exp (ε*C.S.scale k)

namespace bear
variable {f g : ℕ→ℝ}

lemma mk (hf : ∀ᶠ k : ℕ in atTop,0 < f k) (h : (fun k => Real.log (f k)) =o[atTop] C.S.scale) : bear C f := by
  intro ε he; filter_upwards [hf,h.def he] with k hk hp
  rw [← Real.log_le_log_iff hk (Real.exp_pos _),Real.log_exp]
  exact (Real.le_norm_self _).trans (hp.trans_eq (by rw [Real.norm_of_nonneg (show 0 ≤ C.S.scale k from Shoot.scale_nn C.path.levels k)]))


lemma below (h : bear C f) (hi : ∀ᶠ k in atTop,g k ≤ f k) : bear C g := fun ε he =>
    by filter_upwards [hi,h ε he] with j hj ht using hj.trans ht


lemma columns (hG : G.Simple) (ht : Tabs C.path.levels) (H : Margins C.path.levels) :
    bear C (fun k => (C.path.levels.params k).columns) := by
  obtain ⟨M,hm⟩ := market_bound C 0 hG (by norm_num) ht H
  apply below (f:= market C 0) (mk (Eventually.of_forall fun i => zero_lt_one.trans_le (market_one C 0 i le_rfl)) ?_)
    (Eventually.of_forall fun i => ?_)
  · have hf := (Work.I04.hat_receipt C.path.levels hG).const_mul_left (M:ℝ)
    refine isLittleO_iff.mpr fun x hx => ?_
    filter_upwards [hm, hf.def hx] with i hi hj; rw [Real.norm_of_nonneg (Real.log_nonneg (market_one C 0 i le_rfl))]; exact hi.trans ((Real.le_norm_self _).trans hj)
  exact le_mul_of_one_le_left (zero_le_one.trans (C.path.levels.params i).columns_ge) (Real.one_le_exp (by linarith [(C.path.levels.params i).price_pos]))
end bear






end YM.AnalyticNext.GridStop.Planning
