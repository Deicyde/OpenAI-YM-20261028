import YM.Next.RANK.LedgerGate
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.LedgerGate for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V ι κ α : Type} [Fintype ι] [Fintype κ]
variable {C : Family G} {i k l j m p q d D a N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i<k} {h : middleSky C.path.levels b k ≤ i}
variable {c : Course C N p k}

section
variable [DecidableEq V] [Fintype V] {τ : ℝ} {Ψ : V → Site n}

-- denom references in Portal. cost relative, stamp responsibility later

end

-- R.Value bound for any requested realized activity. Need actual producers at eligible caps. Work on ONE compatible representation and flag incidence
section
variable (S : Era)

-- called j = width .. middle-1. fresh hit there at post-L rate (the statement with previous-level hat). Different LD record. multiplier can still be jointly chosen pre-L. ε ratio input (positive). Same coefficient world; no comparison expectation needed.
structure NonLeadingSky (x : Points m) (r : ℝ) (c : Course C N p k) (j : ℕ) (P : Rep G (C.side (j+1) p)) (P' : Rep G (C.side j p)) (b : ℝ) : Prop where
  rent (h : j+1≤ N) (α β : Type) (F : Fintype α) (v : Fintype β) :
    let ζ:= readersSky (C:=C) (b:=b) (p:=p) x c.allow h
    let ψ:= readersSky (C:=C) (b:=b) (p:=p) x c.allow ((Nat.le_succ _).trans h)
    ∀ (H : α→ SourceAt G ζ) (K : β→ Lifted G ζ P.p.threshold) (z : ℝ), 0 ≤ z → z ≤ Perch.bill (-1/2) (clim C.path.levels k) →
      Light P H K (fun _=>r) S.coast.e z (z*Perch.w (clim C.path.levels (j+1))) → Background P K →
        Value.Notice P' ψ ((C.path.levels.clock.op j p).push (c.changeβ (j+1)) (Value.dust P H K)) (fun _=>r)
          S.coast.e (S.α*z+Perch.bill (1/2) (clim C.path.levels k)*z^2) (Perch.gas S.coast (clim C.path.levels (j+1)))
end
end YM.Next.Rank.Tapes
