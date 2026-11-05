import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Yield

/-!
# Supports and complete permissions of one label: (i)

Probe equality before all budgets. A and F are still parameters held jointly. Radius at **seed answers**, not
just addresses with positive incoming K functions. Assembly must use true negative answers as well. Color-coordinate
Gaussian footprint trim paid in `litH`; no arbitrary support from covariance spectral computation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Coverage
open Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels   Mixed Work.E03
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

-- full A, incl all off flags!
def shelves (S : StepData c f) (A A' : Stores S) (X : Support c) := ∀ i : Packets.Seed S,
    (∃ y ∈ X, y ∈ Packets.points S i) → (i ∈ Packets.seeds S A ↔ i∈Packets.seeds S A')

def lens (X : Support c) (i : Site c) (d : ℕ) := ∀ j : Site c,separation i j≤d → j∈X



def haloBook (X : Support c) (B : ℕ) := fun i => lens X i (20*B)

-- balloon W: V requests BOTH endpoints

namespace lens
variable {X Z : Support c} {i j : Site c} {d r : ℕ}

lemma extends_to (h : lens X i d) (he : X⊆Z) : lens Z i d := fun _ hp => he (h _ hp)



end lens

lemma labels (X : Support c) (i : Site c) (p v : ℕ) (h : i∈X) (he : v≤p) : lens (halo p X) i v :=
    fun _ hp => halo_spec.mpr ⟨_,h,hp.trans he⟩

namespace shelves
variable {A A' : Stores S} {X : Support c}









end shelves

-- budget on seed, prereq, V, tags, Y orientation. **same q**.
-- Z agreement tracked only where covariance proof will be allowed.
structure Shed {T : Tube G S} {x : ℝ} (F : Forest S.ratio) {A A' : Stores S} (Y : Mint T F A x) (Y' : Mint T F A' x) (X : Support c) : Prop where
  logs : shelves S A A' X
  field : Agrees X Y.V Y'.V
  crowns : ∀ i ∈ X,Y.k.1 i = Y'.k.1 i
  tails : ∀ (i : Bond c),i.1∈X→Y.k.2 i=Y'.k.2 i -- endpoint held by later station
  pins : ∀ (i : F.Free), home S i.val∈X → Y.Y i=Y'.Y i
  volume : Y.r=Y'.r ∧ Y.u=Y'.u ∧ Y.q=Y'.q

-- noholder and checks remain on eligibility grammar

def Spans (S : StepData c f) (Y : Support c) (B : ℕ) (z z' : ArrayR G f) := ∀ i : Vars G f, haloBook Y B (home S i.1) → z i=z' i

namespace Shed
variable {T : Tube G S} {F : Forest S.ratio} {x : ℝ} {A A' : Stores S} {Y : Mint T F A x} {Y' : Mint T F A' x} {X : Support c}
    (h : Shed F Y Y' X)
include h



lemma fulcrum (i : Site c) (d p : ℕ) (hh : p+1≤d) (he : lens X i d) : AgreeNear id i p Y.V Y'.V := by
  intro k hp; change separation i k.1 ≤ _ at hp
  exact h.field k (he _ (hp.trans (by omega))) (he _ ((separation_triangle _ k.1 _).trans
    ((Nat.add_le_add hp (Work.E03.sep_step _ _)).trans hh)))
end Shed


end YM.AnalyticNext.ConnectedActivity.Coverage
