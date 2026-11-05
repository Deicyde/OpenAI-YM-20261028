import YM.SectorNext.RECONNECTED_LOCALITY.Amble
import YM.SectorNext.RECONNECTED_LOCALITY.Cure


set_option warningAsError false

/-! # Yaw (transformations through symmetrized window table)

Physical transformations on color tangents orthogonal and /or permute
blocks. Require invoice at the level of actual whole A (can be issued from
input Gram factors with common inactive completion). Prove covariance at C
itself, including on *off-block* connections and all color components, when
windows transform together (include complete color even when particular
same-block offdiagonals are zero). W here genuinely geometry-prescribed,
not recalculated per chart or based on numerical nonzero footprint. Transit
pass on every $P$ and all real fields with that same A and Gaussian; not
choosing an orientation average after the fact. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Finset Matrix Function Lattice RG Wilson Bind Window MeasureTheory
open scoped BigOperators

variable {I J ι η : Type*} {Y : η→Type*} {G : Gauge} {c : Side}
variable [Fintype I] [DecidableEq I]
variable {A B T : Matrix I I ℝ} {δ b : ℝ} {W W' : I→Finset I} {g g' : Radar I}

/-- Focus operation on *syntax-fixed* window list. -/
def keep (W : Finset I) : Matrix I I ℝ := diagonal (fun i => if i∈W then 1 else 0)



/-- Solve multiplying by A first, then read the answer through without
rechoosing A. Characterizes principal inverse columns even with couplings
outside. Enough for commutation with gauge. -/
structure Obeys (A : Matrix I I ℝ) (V : Finset I) (x y : I→ℝ) : Prop where
  within : keep V *ᵥ x=x
  claim : keep V *ᵥ (A *ᵥ x)=y







/-- Qualifies even when coincidences allow e.g. mixing different geometrical
slots with the same window. Test *each* pair carrying a coefficient in T. -/
structure Shorn (T : Matrix I I ℝ) (W W' : I→Finset I) : Prop where
  turn : T*T.transpose = 1
  reverse : T.transpose*T = 1
  homes i j : T j i≠0 → T*keep (W i)=keep (W' j)*T

namespace Shorn




omit [DecidableEq I] in
lemma points (T M : Matrix I I ℝ) : drawn (T*M*T.transpose)=pushed (drawn T) (drawn M) := by
  funext i j
  simp only [drawn,mul_apply,transpose_apply,sum_mul,pushed]
  rw [sum_comm]; exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring


end Shorn

section move
open scoped Classical
-- apply over meetings at x.field V = source, B and destination tag Y still at V.
variable {X : Form G c ι I Y} {A : Slip G c ι Y → Matrix I I ℝ} {P:BudgetPoint} {p : I→Site c} {q : η→Site c}
variable [Fintype η] [∀ i,MeasurableSpace (Y i)] {σ k ν V0 : ℝ} {r d t : ℕ}

-- Need same DecidableEq I in shelter & Aligned despite scoped classical; inspect
variable (x : Drift G c ι) (L : Aligned X A p q W r d t σ k δ b ν V0)
variable {m : ∀ i,Measure (Y i)}

include L

end move
end YM.SectorNext.Reconnect.Ice
