import YM.MergeProof.West.Dart
import YM.TraceExtension.Prom.Front.West.Mallow
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Gust
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V κ ι : Type} [DecidableEq V] [Fintype V]
variable {C : Family G}
variable {k N p c m : ℕ}

variable (X : Points (m+1)) (hN : k≤N) (s : ℝ) {d:Fin (m+1) → ℕ} (t : (i:Fin (m+1)) → C.label (d i))

-- spelling input for RMixed: W copies and K already fixed. Proof of equality of credentials at *any* subword.
section
variable (Z : Neat (C.side k p) → Burst G (C.side k p) (C.path.rep N p k).p.threshold)

def pressXSky (i : ListensSky C s (v:=m+1) hN p) := parcel C (d i.2) k N p (t i.2)
lemma satisfiesXSky (i : ListensSky C s (v:=m+1) hN p) (h : C.Makes) (hp : ∀ i,C.ref (d i) ≤ k) : (pressXSky hN s t i).Format 0 C.params (C.path.rep N p k):=
    (h.calibrated (d i.2) N p ((hp i.2).trans hN)).format k (hp i.2) hN _
variable [Fintype κ] [Fintype ι] (A : ι → SourceAt G (seatsSky C s X hN p))
variable (B : κ→Lifted G (seatsSky C s X hN p) (C.path.rep N p k).p.threshold)

def fabricatedXSky (h : C.Makes) (hp : ∀ i,C.ref (d i) ≤ k) := credsX (seatsSky C s X hN p) (fun i=>C.localSection (d i.2)) (pressXSky hN s t) (fun i=> satisfiesXSky hN s t i h hp) (handSky C s hN p) (fpSky C s hN p) Z (fun i=>pinHat C (d i.2) k) B A

def ensembleOXSky (h : C.Makes) (hp : ∀ i,C.ref (d i) ≤ k) := elderX (seatsSky C s X hN p) (pressXSky hN s t) (fun i=> satisfiesXSky hN s t i h hp) (handSky C s hN p) (fpSky C s hN p) Z (fun i=>pinHat C (d i.2) k)

end
end YM.Next.Rank.Edition
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G}{N k p : ℕ}
-- StakeX's existential can include padding finite types using F.C paths.
section
variable (m : ℕ){d: Fin (m+1)→ℕ} (Y : Points (m+1)) (b : ℝ) (hN : k≤N) (v : (i:Fin (m+1))→ C.label (d i))
variable {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable (h : C.Makes) (hp : ∀ i, C.ref (d i)≤k) (F : Course C N p k) (y : ℝ)

-- M-mix input at this probe only. Y includes all orientation hands. may generalize producer.
def StakeXSky := let Q:= C.path.rep N p k; let f:= seatsSky C b Y hN p
    ∃ (B : Neat (C.side k p)→ Burst G (C.side k p) Q.p.threshold), IsoVac _ B (C.path.levels.clock.forcedAllowance k) ∧
      ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ),∃ (A : ι→SourceAt G f) (K : κ→Lifted G f Q.p.threshold),
        Unpacks A Q.p (fun _=> y) Q.p.supportExponent 1 ∧ Unfold (p:=Q.p) K (fun _=> y) Q.p.supportExponent 1 ∧
        (∀ i, 2≤(A i).fires.val.card) ∧ (∀ i,2≤ (K i).fires.val.card) ∧
        fabricatedXSky Y hN b v B A K h hp=BillsXSky C b Y hN p v F
end
end YM.Next.Rank.Edition
