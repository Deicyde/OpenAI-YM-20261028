import YM.Next.UV_STRESS.Annulus
import YM.Next.UV_STRESS.Zebra


/-!
# Offset calibration to a Q test at weight four (RPrep assistance)

Actual corners on h grid small sites translated, incl o offset, NOT just
weak station at origin. Detector list finite centered generic (can build
at Bel) with tolerance fixed before any choice of station or hierarchy
refinement. To produce input estimates on this one list via E one should
choose h-grid normalized spacing and round the points towards the detector,
small enough for `AtOffset`, AND fit h-cell root estimate for every
corresponding scaled column. Thus both costs would use one Q setup
(think A & smaller meshes); not authorizing placement or radius gates by
some fixed-sector comparison. Can also feed these with separate geometries
as long as that agrees. Merely having Seed.corrected or other rank stamps
would not give the uniformly-in-offset estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb Lattice Wilson Cells
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {T : Table C.book} {F : Extraction.Order} {h c N p : ℕ}

abbrev Entry (C : Family G) := (Bel C.book).Field 4

structure Palette where
  n : ℕ
  v : Fin n → (Bel C.book).Tag
  x : Points (n+1)
  spread : x∈generic _
  home : x 0=0

namespace Palette
variable (P : Palette C)
def eval : Entry C →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Work.A01.frontRead P.v P.x 4)

end Palette



/-- Offset-calibrated columns on same cutoff history. Value in actual *reference*
coordinates (can call `terminal` if formulated at bare). Not projections at S. -/
abbrev QMap (C : Family G) := (N p : ℕ) → Site (C.side N p) → Entry C →ₗ[ℂ] C.book.Ref 4

structure Marking (P : Palette C) where
  y : Fin P.n → Cover
  /-- stencil choices at same relative offset. May be built from weak maps
      at C reference weights; height of each spectator retained. -/
  other : (N p : ℕ) → Site (C.side N p) → (i : Fin P.n) → C.book.Ref (P.v i).1
  valid : Function.Injective (Fin.cons (α:=fun _ => Cover) 0 y)

namespace Marking
variable {R : Palette C} (D : Marking C R)

def committee (o : Site (C.side N p)) (i : Fin R.n) : C.book.Token := ⟨(R.v i).1,D.other N p o i⟩
def site (h : ℕ) (o : Site (C.side N p)) (i : Fin R.n) := o+location C.S h N p (D.y i)
def live (h : ℕ) (o : Site (C.side N p)) (v : C.book.Ref 4) :=
  C.numeric N p (Fin.cons (α:=fun _ : Fin (R.n+1) => C.book.Token) ⟨4,v⟩ (D.committee C o))
    (Fin.cons o (D.site C h o))



-- same root weights measured at all copies of Q. No pair cost grant
-- involving the not-yet-priced physical v.

def Seen (F : Extraction.Order) (h : ℕ) (hc : h+1≤c) := ∃ A : ℝ, 0≤A ∧ F.late fun N p => ∃ hn : c ≤ N,
    ∀ o : Site (C.side N p), ∀ i:Fin R.n,
    let T := zebra C h hc hn o; let x := D.site C h o i
    ∃ Q : Config G (C.side N p) → ℂ,
      C.seen (D.committee C o i) x = T.copy (wrap (C.side h p) (D.y i)) Q ∧
        Interior (T.chamber 0) Q ∧ T.rootTest (C.beta N p) Q ≤ A


end Marking
end YM.Next.UVStress
