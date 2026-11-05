import Mathlib.Analysis.ODE.ExistUnique
import YM.Bid.Angular
import YM.Bid.Station


/-!
# More acceptance lugs

These are tiny clients doing additional type/scope checks on tricky applications;
not proving the large red Looms, Arrives etc. nor releasing new tickets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Org Table Climb Wilson Lattice RG Precision Tree Exterior Bloch Laurent Matrix Pressure
open Source MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal InnerProductSpace

variable {G : Gauge} {C : Family G}

-- use Gθ whole stop REAL


lemma masts (j : A12) (l : A10) (k : A09) (H : (Bel C.book).Hierarchy) (J : Lighthouse C.book) (h : J.Goes C.book H.spin)
    (X : Boundary.Spins (Bel C.book)) (hx : X.Descends J.K H.spin) (hp : Org.erases H.spin J.W) :
    ∃ t : MaxwellData C,t.T=J ∧ t.vacuum=X := by
  have he := h.turns
  have hh : Spin.Port J.K H.spin := ⟨he.spin,he.fixes,he.group,he.signed,he.real,he.infinitesimal⟩
  exact ⟨⟨J,H,h,X,hx,(k J.K.lie (l _ _ hh).1).1,j J.K _ hh,hp⟩,rfl,rfl⟩

variable {c f : Side} (S : StepData c f)

/-- Can perform station-matching (Φ + D) for one tree and transfer
classical part to any other, IF funding P setup. -/
lemma one_for_all (a : F05) (hx : Larger (G:=G) S)
    (H : Forest S.ratio) (p q : Clip) (W Y : PathData G) (σ C Λ α : ℝ) (hp : 0<α)
    (hz : W.Bounds p σ C Λ) (Tr : ChartRatio G) (hT : LocalRatio Tr)
    (ρ : (F : Forest S.ratio) → Dir G c→AxisChart G F) (h : ∀ F, Critical F p W (ρ F)) (hQ : ∀ F, PriceGap (S:=S) F p W α)
    (H' : ClassicalMatch H p q W Y (ρ H)) : ∀ F, ClassicalMatch F p q W Y (ρ F) := by
  intro F j hj i
  obtain ⟨he,hh,hK⟩ := H' j hj i
  have ht := (a _ _ _ S hx F H p W _ _ _ _ _ _ _ hz (h F) (h H) hp hp (hQ F) (hQ H) _ hT i).1
  exact ⟨he.congr_of_eventuallyEq ht,hh,((ht.iteratedFDeriv ℝ j).self_of_nhds).trans hK⟩
end YM.Bid
