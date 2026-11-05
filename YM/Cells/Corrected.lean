import YM.Cells.Transforms
import YM.Euclid.Comparator

/-!
One per weight d; one common aligned series for its full detecting set of
columns. Strict centered link tiling at side another
level; this picks the option E's geometry A claims to realize. `atK` uses
the exact local placements on the k-grid, and recompute free
coefficients there, scaled by **actual** r. No assumption on how near
cross-cell copies would be at scale r; construction must also arrange their
distances via allowed side and plateau.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Wilson Lattice Maxwell
open scoped ContDiff Topology BigOperators

variable {G : Gauge} (C : Family G) (f : Extraction.Order) (S : Table C.book)

abbrev standard (C : Family G) := freeTable C.labels

/-- Cluster template. Main input is unspecified first slot. -/
structure SampleRow (o : Type*) where
  extra : ℕ
  cap : extra ≤ 1
  uses : Fin extra → o
  expected : Points (extra+1)
  probes : expected∈ generic (extra+1)

namespace SampleRow
-- Input always first slot, arbitrary **quotient** labels on corresponding table.
def tests {B : Type*} (D : SampleRow B) {L : Register G} (S : Table L) {d : ℕ} (lam : B → S.Field d)
    (X : S.Field d) := S.useAt S D.expected (Fin.cons ⟨d,X⟩ (fun i => ⟨d,lam (D.uses i)⟩))
end SampleRow

structure Columns (S : Table C.book) (d : ℕ) where
  dim : ℕ
  H : (standard C).RealSpin
  basis : Module.Basis (Fin (dim+1)) ℂ ((standard C).Field d)
  realBasis i : (standard C).conj H d (basis i) = basis i
  initial : basis 0 = (standard C).unit d
  amount : ℕ
  row : Fin amount → SampleRow (Fin (dim+1))
  full : Injective (fun x => (fun i => (row i).tests (standard C) basis x))

namespace Columns
variable {C S} {d : ℕ}

/-- The series indexed by k uses probes centered at 0 in a side-b cell.
Length retuning per row not needed. -/
structure Trials (X : Columns C S d) where
  depth : Extraction.Sequence
  width : Extraction.Sequence -- really side level; strict to ensure shrink
  window k : width k ≤ depth k
  scale : ℕ → ℝ
  positive k : 0 < scale k
  zoom : Tendsto scale atTop (𝓝 0)
  mark (k : ℕ) (i : Fin X.amount) : Fin ((X.row i).extra+1) → Cover
  -- k,N,p, coordinate: actual cutoff v.
  lift (k N p : ℕ) : Fin (X.dim+1) → C.book.Ref d
  later (k : ℕ) : Fin (X.dim+1) → C.book.Ref d
  gap : ℕ → ℝ
  allowed k : 0 ≤ gap k
  small : Tendsto gap atTop (𝓝 0)

namespace Trials
variable {X : Columns C S d} (Z : X.Trials)

def realPlace (k i) := Extraction.Order.grid C (Z.depth k) (Z.mark k i)

def tested (k : ℕ) (i) : Points ((X.row i).extra+1) := (Z.scale k)⁻¹ • Z.realPlace k i

def names (i : Fin X.amount) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : Fin (X.dim+1) :=
  Fin.cons (α := fun _ => Fin (X.dim+1)) c (X.row i).uses s

/-- Include the entire corrected cylinder. With o=0 there are only singleton terms;
with extra=1 there are the two singletons and only pair. Pair output
`FG−aG−bF+a*b−(S₁₂−a*b)` as required by commuting square-zero markers. -/
def singleton (k : ℕ) (i c s) := (standard C).useAt (standard C)
  (points (fun _ : Fin 1 => Z.tested k i s)) (fun _ => ⟨d,X.basis (names (X := X) i c s)⟩)

def cumulant (k : ℕ) (i c s t) := (standard C).useAt (standard C)
  (points ![Z.tested k i s, Z.tested k i t])
    ![⟨d,X.basis (names (X := X) i c s)⟩,⟨d,X.basis (names (X := X) i c t)⟩] - Z.singleton k i c s * Z.singleton k i c t

def weigh (k N p : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) (j : Fin ((X.row i).extra+1)) : Config G (C.side N p) → ℂ := C.O N p (d := d)
  (Z.lift k N p (names (X := X) i c j)) (location C.S (Z.depth k) N p (Z.mark k i j))
def subtract1 (k N p i c j) := fun U => Z.weigh k N p i c j U - Z.singleton k i c j

def subtract2 (k N p i c j t) := fun U => Z.subtract1 k N p i c j U * Z.subtract1 k N p i c t U - Z.cumulant k i c j t

/-- Eventual for each fixed k in iterated limsup. Fit all s and data,
including literal unchanged coefficients and orientation-conjugated copies from
`rootTest`. For pair bounds only order s<t. Sides always a^(some level), link
seams through that calendar. -/
structure Valid : Prop where
  /-- Concretize "allowed rescaling lengths"  with  A placements; use plateau through tested h. (May not need A large buﬀer factors for reconstruction here, those become separate producer conditions.) -/
  ratios : ∃ b : ℝ, 0 < b ∧ ∀ k, Z.scale k = C.S.a (Z.depth k) * ((C.path.levels.clock.monitor (Z.depth k))^b)
  same_stage k m (hq : Z.width k ≤ m) (hN : m ≤ Z.depth k) :
    C.path.levels.clock.J m=C.path.levels.clock.J (Z.depth k)
  scale_down : StrictAnti Z.scale
  conjugate (k N p i) : star (Z.lift k N p i) = Z.lift k N p i
  unit (k N p) : Z.lift k N p 0 = C.refUnit d
  responds (k i) : f.limits (fun _ => True) (fun N p => Z.lift k N p i) (Z.later k i)
  bounded (k : ℕ) : ∃ A : ℝ, ∀ p, ∀ᶠ j : ℕ in atTop, ∀ i, ‖Z.lift k (f.mesh j) p i‖ ≤ A
  span : ∀ᶠ k in atTop, Submodule.span ℂ (Set.range fun i => S.project d (Z.later k i)) = ⊤
  tuned i : Tendsto (fun k => Z.tested k i) atTop (𝓝 (X.row i).expected)
  seams : ∃ η : ℝ, 0 < η ∧ ∀ k i j a,
    |Z.realPlace k i j a| ≤ C.S.a (Z.width k)*((2:ℝ)⁻¹-η)
  generic (k i) : Z.realPlace k i ∈ YM.generic _
  cheap (k : ℕ) (ε : ℝ) (he : 0 < ε) : f.late fun N p => ∃ h : Z.depth k ≤ N,
    let T := center C.S p ((Z.window k).trans h) 0
    ∀ i c s,
      Interior (T.chamber 0) (Z.weigh k N p i c s) ∧
      T.rootTest (C.beta N p) (Z.subtract1 k N p i c s) ≤ Z.gap k + ε ∧
      ∀ t, s<t → T.rootTest (C.beta N p) (Z.subtract2 k N p i c s t) ≤ Z.gap k + ε

lemma refresh (H : Z.Valid f) (g) : Z.Valid (f.refine g) where
  ratios := H.ratios
  same_stage := H.same_stage
  scale_down := H.scale_down
  conjugate := H.conjugate
  unit := H.unit
  responds k i := Extraction.Order.retained (H.responds k i)
  bounded k := by
    obtain ⟨A,h⟩ := H.bounded k
    exact ⟨A,fun p => g.mesh.cofinal.eventually (h p)⟩
  span := H.span
  tuned := H.tuned
  seams := H.seams
  generic := H.generic
  cheap k ε h := Extraction.Order.late_refine f g (H.cheap k ε h)
end Trials
end Columns

def RankWidths : Prop := ∀ d : ℕ, ∃ X : Columns C S d, ∃ Y : X.Trials, Y.Valid f
end YM.Cells
