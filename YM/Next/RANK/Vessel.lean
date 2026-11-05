import YM.Next.RANK.StagePass

/-!
# Assemble the W/R comparison dynasty into the middle stop clearance
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {c : Course C N p k} {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}
variable (F : MarketGrant c P X R ξ)

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable {x : Points m} (H : Corridor C.path.levels ξ.band ξ k) (he : Fit C.path.levels ξ.band k x)
variable (v : Fin m→ C.label d) (Z : ∀ i, coin (O.W (v i))≤ ξ.principal (clim C.path.levels k))







include he in
lemma snug (i : pennant m) (p : ℕ) (d) : cozy C.path.levels x ξ.band p d
    (walls (clim C.path.levels (middle C.path.levels ξ.band k))) (before C.path.levels ξ.band k) i:= by
  cases i with
  | inl x=> trivial
  | inr x=>
    unfold cozy core; try dsimp only [Sum.elim_inr]
    rw [Station.at_stop he p,Station.at_stop he p,separation_self]; exact Nat.zero_le _

include H he Z


end YM.Next.Rank.Tapes
