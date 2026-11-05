import YM.Push.STRESS_FLUX.Film
import YM.Push.STRESS_FLUX.Layer
import YM.Work.A05.Window

/-! Mesh then period passage of the normalized *full finite quadrature with
all fine stress nodes*, on fixed windows. Each-period limits as well as the
fused consequence, not just a diagonal. Spectators held generic for point
passage (density/continuity in Annular/Solve for testing limiting field laws
through ties). No uniform-in-shrinking-window or diagonal estimate claimed. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Layer
open Matching Function Set Filter Lattice Wilson MeasureTheory Extraction Analysis
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {p N n : ℕ} {x : Points (n+1)} {χ : E4 → ℝ} {a b : Axis}
    {K : Set (Points (n+2))} {B : Set E4} {f : Extraction.Order} {Q : ℕ → Table C.book} {S : Table C.book} {V : E4 → E4}

def target (x : Points (n+1)) (q : Fin (n+2) → C.book.Token) (χ : E4 → ℝ) (V : E4 → E4) (a b : Axis) (P : Table C.book) (y : E4) :=
  Work.A05.weight χ a (fun z => V z b) y * P.read (Points.cons y x) q

structure Scene (C : Family G) (x : Points (n+1)) (χ : E4 → ℝ) (K : Set (Points (n+2))) (B : Set E4) : Prop where
  poses : IsCompact K ∧ IsCompact B ∧ K ⊆ conf _ ∧ tsupport (fderiv ℝ χ) ⊆ B
  stays : ∀ y∈B, Points.cons y x ∈ K
  approaches : ∀ᶠ N : ℕ in atTop, ∀ (V : E4 → E4) a b y, stone χ (C.S.a N) V a b (node (R:=C.S) N y) ≠ 0 → y∈B ∧
        tag (C.S.a N) (address (C.S.a N) (Points.cons y x)) ∈ K

def InsideScene (C : Family G) (K : Set (Points (n+2))) (B : Set E4) (χ : E4 → ℝ) (p : ℕ) := K ⊆ Inside C.S p _ ∧
    (∀ y∈B, pack y ∈ Fund C.S p 1) ∧ ∀ N (x : Site (C.side N p)) V a b, Discrete.boundaryWeight (C.S.a N) (χ ∘ C.S.place) (V ∘ C.S.place) x a b = stone χ (C.S.a N) V a b (C.S.place x)
lemma Scene.ready (h : Scene C x χ K B) (hc : HasCompactSupport χ) : ∀ᶠ p in atTop, InsideScene C K B χ p := by
  filter_upwards [room C.S h.poses.1,room C.S (h.poses.2.1.image pack.continuous),unwrap C.S hc] with p h1 h2 h3
  exact ⟨h1, fun y hy j a => (h2 (mem_image_of_mem _ hy) j a).imp_right (fun h => h.le),h3⟩






end YM.StressFlux.Layer
