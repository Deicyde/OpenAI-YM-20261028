import YM.MergeProof.Waver
import YM.TraceExtension.Prom.Hill.Gust
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion Spindle Atlas Cells
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]
-- generate chess-copies all polynomials. factor across every occurrence no collapse.

variable (C:Family G)(h:C.Makes)(N k p d m:ℕ) (v:Fin m→ C.label d) (b:ℝ)(Y:Points m)(hk:k≤N)

local notation "Q"=> C.path.rep N p N
set_option quotPrecheck false
def plumSky (j:ListensSky C b (v:=m) hk p):= dye (handSky C b hk p j) (fpSky C b hk p j)
def hopsSky (i:ℕ)(j:ListensSky C b hk p (v:=m)): Site (C.side i p):= Mix.camp C p k i (seatsSky C b Y hk p j)
local notation "L"=> Listens C b (v:=m) hk p
local notation "v'"=> hops C N k p m b Y hk
local notation "g'"=> plum C N k p m b hk
local notation "P"=> Issued C b Y hk p v
include h

end YM.MergeProof.Accent
