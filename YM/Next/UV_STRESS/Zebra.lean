import YM.Next.UV_STRESS.Birth


/-!
# The seams for offset detectors in RPrep

Detector displacements will be chosen multiples of side h itself, smaller than
physical radius of a station's weak detector but possibly much larger than its
k0 grid. Still need to handle centers varying by offsets! Place the comparison
site-seams aligned to that k0=c grid, NOT link seams from o. Use both sides
of ancestry. Nothing buys the Q estimates there yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Around Cells
open scoped Topology ContDiff BigOperators
variable {G : Gauge} (C : Family G) {F : Extraction.Order}
variable {h c N p : ℕ}

/-- Re-center the smaller exterior test tiling at this canonical offset's
coarse *projection* on grid c (not at o in general). -/
def zebra (h : ℕ) (hc : h+1≤c) (hn : c ≤ N) (o : Site (C.side N p)) : Tiling (C.side N p) :=
    let W := C.S.toDepth hn p
    let Z := terrace C.S h (hc.trans hn) p
    Z.newly (Z.base + W.embed (W.parent o))






end YM.Next.UVStress
