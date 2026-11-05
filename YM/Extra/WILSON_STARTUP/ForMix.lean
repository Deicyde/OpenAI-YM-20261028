import YM.Extra.WILSON_STARTUP.Engine
import YM.Extra.WILSON_STARTUP.Fast
import YM.Extra.WILSON_STARTUP.MixRoom


/-! # Top-lane starts: use on the full collection of asks under common gates -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Mixture
open Function Filter RG Lattice Wilson Finset Overlay Source Mix Labels Cells Marker Start
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Supply.Sheet G} {D : Supply.Rolls C} {T : Supply.Protection D} {W : Supply.Delays T} {Y : Supply.Bar W}
    {I : Supply.Wait Y} {S : Labels.Frames G} {X : ∀ d, SectionData (S.level d)}

def funded (C : Supply.Sheet G) (f : ℕ → ℝ) := ∀ j ≥ C.first, ∀ x : ℝ, f j ≤ x → ∀ A : Levels G, ∀ N,
    A.params N = C.profile j → A.clock.hatBeta N = x → Extras A N

theorem first_edition (W : Supply.Delays T) : ∃ v : ℕ → ℝ,
    W.betaEntry ≤ v ∧ ∀ w : ℕ → ℝ,v ≤ w → funded C w := by
  choose f hf using fun j => eventually_atTop.mp (afford G (C.profile j))
  refine ⟨fun i => max (W.betaEntry i) (f i),fun _ => le_max_left ..,fun w hw i _ x hx A N => ?_⟩
  exact hf i x ((le_max_right ..).trans ((hw i).trans hx)) A N



open Input Shoot Precision
variable {O : ChartRatio G} {K : MapPrices} {Q : PostCost D}


end YM.WilsonStartup.Mixture
