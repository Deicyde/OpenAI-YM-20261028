import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Cash
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Local

set_option warningAsError false
set_option autoImplicit false
set_option synthInstance.maxSize 1024

/-!
# Physical push and scalar extraction at adjacent stations

Throughput at the unnormalized densities. Before rewriting the output eval or
asserting any positivity we can already issue the exact push in this form.
At a surviving Selected/Directed pair obtain also positivity and the true v'
receipt. No positivity required/claimed on the individual listings in this
argument. Benchmark, path fit, tagged transform, log costs, and v all on THIS
history, all admitted N,m,p and all actual given trees under the real shared
prices (schedule precursor see `issue`). Value-only. Keep post-integration
budget promises for any downstream restructuring even at the always-eligible
identity V; these steps are NOT producing such bounds or a `Selected`.
-/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix RG Wilson Lattice Input RG.Supply RG.Shoot Push.PriceCompiler
  Pressure Pressure.Testing Push.SectorMeasure Precision Tree Next.SectorChange Further GaussianScalar AnalyticBridge AnalyticBridge.ResetIncome
  SectorNext.Vacuum GaussianFieldAlignment
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}

namespace Bought
variable {c f : Side} {S : StepData c f} {e : Plate G S} {v : GaussianFieldAlignment.Rates}
  (he : Bought e v) (R : Rep G f) (hp : 0 < R.beta) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w)
include he hR hp






end Bought

variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Input.Directed G I Z K P)
    {r : Tickets} {ε g a E : ℕ → ℕ → ℝ} (h : Cash W Z K r ε g a E)
    (T : ∀ (_ p : ℕ), Trail B.a p) (ht : B.bake.Stays T) (hs : (B.bake.make T).Selected)
    (N m p : ℕ) (hm : m<N)

lemma fits {R : Rep G (B.a.S.side (m+1) p)} (hR : Lives B.bake N (m+1) p R) :
    Presented.Fits (ships B N m p) R (B.a.clock.hatBeta m) :=
  ⟨by rw [hR.path,B.bases]; rfl, hR.clip, by rw [hR.point,costs_shift B]; rfl⟩

-- Useful attachment to the bought schedule in advance of Prereset proofs.


include ht hs

end YM.SectorTools.ActualScalar
