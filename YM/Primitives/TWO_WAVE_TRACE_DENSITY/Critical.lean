import YM.AnalyticNext.CALENDAR_SCENE_ADAPTER.Envelope
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Boards
import YM.Progress.JOINT_CALENDAR.Kinetics
import YM.Progress.STATIONARY_SCENES.Entrance


/-!
# Actual real stationary calculation on reindexed cell charts

Reuse CALENDAR_SCENE_ADAPTER's jets/Parked and zero-field logdet identity.
This version works on the compressed cell numbering with α free for coarse
**types** (notation only; not drift coefficient), β free for vertical types.
An all-type Fan may thus have incoming vertical/coarse mixed. Flatten in the
physical application via linear equivalence. Keep Haar and loop terms as
translation-scalar `extra`; no assumptions about their first derivative or
whether it's volume-independent. (No need to drop the acceleration by group
simpleness.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Function Matrix
open AnalyticNext.CalendarScene AnalyticNext.CalendarScene.Jets
open scoped BigOperators Classical ContDiff Topology
variable {n : Side} {k : ℕ} {α β : Type} [Fintype α] [Fintype β] {R : Type} [CommRing R]

/-- Unmarked full (coarse+vertical) quadratic jet read as a matrix. -/
def base (A : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 1 R) : Matrix (Leaf n (α⊕β)) (Leaf n (α⊕β)) R :=
    injectMatrix A (fun _ : Fin 0=>0)

lemma base_at (A : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 1 R) (i j:Leaf n (α⊕β)) : base A i j=A i ![j] := by
  classical
  have hh (l : Fin 0→Leaf n (α⊕β)): Fin.cons j l = ![j]:= by ext1 a; fin_cases a; rfl
  unfold base injectMatrix; simp [hh]





/-- Pure formulas with no regularity premised. Input fields on all coarse
sites. a named variation need only agree on the trace rule physically. -/
structure Invoices (α β : Type) (n : Side) (R:Type) where
  seed : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 1 R
  third : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 2 R
  fourth : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 3 R
  inv : Matrix (Leaf n β) (Leaf n β) R
  nonLoop₁ : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 0 R
  nonLoop₂ : FrameCoeffs (Leaf n (α⊕β)) (Leaf n (α⊕β)) 1 R

namespace Invoices
variable (I : Invoices α β n R)







-- separate for integral later



end Invoices

local notation "E" => Board
variable {S U : E α n ℝ × E β n ℝ →ℝ} {ρ : E α n ℝ→ E β n ℝ}
    {I : Invoices α β n ℝ}

/-- Actual tensor link, use zero-field jets of S = joint tested in
flattened coordinates. `U` = extra signed scalar. -/
def reprint (S : E α n ℝ × E β n ℝ →ℝ) (k : ℕ) := extractF
    (iteratedFDeriv ℝ (k+1) (S ∘ desks α β n) 0)








structure ClipIn (I : Invoices α β n ℝ) (S U : E α n ℝ × E β n ℝ→ℝ)
    (ρ : E α n ℝ→E β n ℝ) : Prop where
  zero : ρ 0=0
  law : Parked S ρ 0
  song : ContDiffAt ℝ ω U 0
  seed : I.seed=reprint S 1
  third : I.third=reprint S 2
  fourth : I.fourth=reprint S 3
  bill₁ : I.nonLoop₁=reprint U 0
  bill₂ : I.nonLoop₂=reprint U 1
  paid : I.inv*(base I.seed).submatrix (peg α) (peg α)=1

namespace ClipIn
open Invoices
variable (H : ClipIn I S U ρ)
include H







end ClipIn
end YM.Primitives.TwoWave
