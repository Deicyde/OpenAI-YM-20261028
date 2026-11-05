import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Kernel

set_option warningAsError false

/-!
# Conditional lifting and pushing on a common history

`H.β N p l` is the **actual** action parameter from that trajectory. Intended
for h:k≤l≤N (lemmas about mass-1 kernels hold at other padded levels too).
Compose literal kernels, never reselect at translated probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror
open Set Filter Function MeasureTheory RG Wilson Lattice Block
open scoped Topology BigOperators Matrix.Norms.Frobenius

namespace Tower
variable {G : Gauge} (H : History G) (N p : ℕ) {k l m : ℕ}
abbrev Qry (k : ℕ) := Config G (H.S.side k p) → ℂ
abbrev axis (k : ℕ) := H.levels.clock.op k p
abbrev temperature (k : ℕ) := H.β N p (k+1)

def gather (h : k ≤ l) (F : Qry H p k) : Qry H p l :=
    Nat.leRec (motive := fun l _ => Qry H p l) F
      (fun {l} _ Q => accept (axis H p l) (temperature H N p l) Q) h
def pressed (h : k ≤ l) : Qry H p l → Qry H p k :=
    Nat.leRec (motive := fun l _ => Qry H p l → Qry H p k) id
      (fun {l} _ y Q => y ((axis H p l).push (temperature H N p l) Q)) h


lemma first (F : Qry H p k) : gather H N p (show k ≤ k from le_rfl) F=F := by rw [gather,Nat.leRec_self]


























end Tower
end YM.ProjectorNext.RMirror
