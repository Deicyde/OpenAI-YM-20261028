import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Net
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.One



set_option warningAsError false

/-!
# Terminal-budget producer route for one-slot reflection approximation

At a fixed stop l, get full additive/forced `Bands` density
representation with per-site/mark estimates (including absolute and support
costs), at ever-growing radius w as the approximation improves.

Representation
identity for the actual mixed signal -- old products full push N:k, new
insertion *there*, then press further using the SAME unnormalized vacuum and
choices down to l.

Requires no presentation at level N of the marker
for the new coarse insertion.

See `ledger`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Stop
open Set Filter Function MeasureTheory RG Wilson Lattice Cells Block Extraction Org
open Marker Overlay Tower Net
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (C : Family G) {k l m p N : ℕ}

abbrev Port (p m : ℕ) := Stock.census (Flags C.path p m)

/-- w paid per mark. Use together with Offers/ledger to feed
genuine-cutoff estimates into reflection/compression. -/
structure Books (N p : ℕ) (v : C.book.Token) (hl : m ≤ l) (hk : l ≤ k) (hn : k ≤ N)
    (A : Qry C.path p k) (u r d b w : ℝ) : Prop where
  current : ∃ B : Bands (Port C p m) (C.path.rep N p l), B.Active ∧
    (∀ i, B.origins i = (C.S.toDepth hl p).embed i) ∧
    B.Radial (fun _ => w) u r d b ∧
    ∀ s : (Port C p m).Mode, ∀ U,
      (B.density U).part s = encoded C.path v.1 (hl.trans hk) hn hk (source C v N p) A s.val U


















end YM.ProjectorNext.RMirror.Stop
