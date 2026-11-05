import YM.Next.EXTRACTION.Relay
import YM.Next.FOUNDATIONS.SU2
import YM.Work.F02

/-!
# Regenerated, volume-independent domain for canonical functions

Complex polynomials/series on forward and reverse letter variables. Full
comparison equalities at real gauge configurations (unmasked functions only).
Uses the funded width **without** replacing it in the history; ordinary
Frobenius/sup balls about any physical configuration. Native per-site costs.
Not a bound on the analytic radius of a stationary solution in its coarse
field variables! That involves inversion and block data. The aperture
hypotheses of the fresh calculation remain separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Disc
open Filter Function Lattice Wilson RG Exterior Precision Bloch Work.F02 Matrix Finset Metric
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius NNReal

variable {G : Gauge} {n : Side}









def turn (s : Signed) (M : Ambient G n) : Ambient G n := fun i =>
  let v := M (sendEdge s 0 i); if s.flip i.2 then v.swap else v




def priceExt (b : Face (Per n)) (M : Ambient G n) :=
  let w := square b.2.val.1 b.2.val.2
  1 - (trace (stringMat M w b.1) + trace (stringMat M (Lattice.reverse w) b.1))/2 / (G.repDim:ℂ)







variable {p : Clip} {W : PathData G} {σ C Λ : ℝ}

def ellExt (W : PathData G) (b : Face (Per n)) (M : Ambient G n) := ∑' i, rowExt W b i M


def atomsExt {k : ℕ} (A : ℕ → Atom G k) (x : Site n) (M : Ambient G n) := ∑' i,atomExt (A i) x M


def fullExt (p : Clip) (W : PathData G) (x : Site n) (M : Ambient G n) := ∑ i : PlaqAxes,
    ((p.direct:ℂ) * priceExt (x,i) M + (∑ j, (ellExt W (x,i) M j)^2)/2)







/-- Per-site complex estimate with true physical real reading. -/
structure Tracks (r A : ℝ) (F : Config G n → Site n → ℝ) (f : Site n → Ambient G n → ℂ) : Prop where
  physical_value (U : Config G n) (x) : f x (physical U) = ↑(F U x)
  analytic (U : Config G n) (x) : AnalyticOnNhd ℂ (f x) (ball (physical U) r)
  cost (U : Config G n) (x M) : M ∈ closedBall (physical U) r → ‖f x M‖ ≤ A




namespace Tracks
variable {r A B : ℝ} {F H : Config G n → Site n → ℝ} {f g : Site n → Ambient G n → ℂ} (h : Tracks r A F f) (h₂ : Tracks r B H g)
include h h₂
lemma add : Tracks r (A+B) (F+H) (f+g) := ⟨fun U x => by rw [Pi.add_apply,Pi.add_apply,h.physical_value,h₂.physical_value]; simp,
  fun U x M hm => (h.analytic U x M hm).add (h₂.analytic U x M hm),fun U x M hm => (norm_add_le ..).trans
    (add_le_add (h.cost U x M hm) (h₂.cost U x M hm))⟩
omit h₂

/-- Sum over all sites under explicit signed-channel averaging. -/
def rolled (f : Site n → Ambient G n → ℂ) (M : Ambient G n) := (Fintype.card Signed:ℂ)⁻¹ * ∑ s : Signed, ∑ x,f x (turn s M)



end Tracks

variable (p W)

def view := Tracks.rolled (fullExt (n:=n) p W + atomsExt W.cubic + atomsExt W.quartic)
def baseView := Tracks.rolled (fullExt (n:=n) p W)
def loopView := Tracks.rolled (atomsExt (n:=n) W.loop)

/-- Explicit prices and radius for all three functions, on any Side. -/
structure Window (G : Gauge) (W : PathData G) (p : Clip) (r cost second loopBound : ℝ) : Prop where
  pos : 0 < r
  values {n : Side} (U : Config G n) : view p W (physical U) = ↑(mainTerm p W U) ∧ baseView p W (physical U) = ↑(secondTerm p W U) ∧
      loopView W (physical U) = ↑(loop W U)
  analytic {n : Side} (U : Config G n) : AnalyticOnNhd ℂ (view p W) (ball (physical U) r) ∧
      AnalyticOnNhd ℂ (baseView p W) (ball (physical U) r) ∧ AnalyticOnNhd ℂ (loopView W) (ball (physical U) r)
  bounds {n : Side} (U : Config G n) (M : Ambient G n) : M ∈ closedBall (physical U) r →
      ‖view p W M‖ ≤ Fintype.card (Site n)*cost ∧ ‖baseView p W M‖ ≤ Fintype.card (Site n)*second ∧
        ‖loopView W M‖ ≤ Fintype.card (Site n)*loopBound




end YM.Extra.Iteration.Disc
