import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Symmetric
import YM.Bid.Station

set_option warningAsError false

/-!
# Passing through physical test tori

`h` witnesses integer ratio of *periods*, not a one-step blocking Ratio
(though we use a second Ratio to read the geometry). Multiplicity exact;
tested for sequences independent of particular period. `Shifted` uses the
same common translation on all positions.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin
open Lattice RG Laurent Exterior Wilson Precision Bid Tensor 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n m : Side}

/-- Generating auxiliary periods at least n -/
abbrev divides (n m : Side) := n.val ∣ m.val
section
variable (h : divides n m)

def casing : Side := ⟨m.val / n.val, Nat.div_pos (Nat.le_of_dvd m.property h) n.property⟩
lemma cases_mul : m.val=(casing h).val*n.val := by
  change m.val=m.val/n.val*n.val; rw [Nat.div_mul_cancel h]

def enclosing : Ratio (casing h) m := ⟨n,cases_mul h⟩
def shrinkTo : Site m→+Site n := (enclosing h).residue
lemma shrinkWrap (x : Cover) : shrinkTo h (wrap m x)=wrap n x := (enclosing h).residue_wrap x


def extendDir (G : Gauge) (r : ℕ) : fieldDir G n r →L[ℝ] fieldDir G m r :=
    ContinuousLinearMap.pi fun (i : Exterior.Body r m) => (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Exterior.Body r n => G.Color) (shrinkTo h i.1,i.2))


variable {J α : Type} [Fintype J] [DecidableEq J] [Fintype α]




end

def shiftedDir (a : Site n) (G : Gauge) (r : ℕ) : fieldDir G n r →L[ℝ] fieldDir G n r :=
    ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Exterior.Body r n=> G.Color) (i.1+a,i.2))

/-- Poly-order functional allowed to be filled only on sides ≥ t
(populate smaller side entries arbitrarily). Usually comes from manifestly
natural expression; does not assert germs are solved on unbooked periods. -/
structure ShiftedThrough (k : ℕ) (t : ℕ) (Q : ∀ n : Side,T (Dir G n) ℝ k) : Prop where
  multiples (n m : Side) (h : divides n m) (hu : t ≤ n.val) : ∀ v, Q m (fun i => extendDir h G 1 (v i)) = Fintype.card (Site (casing h)) * Q n v
  translates n : t ≤ n.val → ∀ p v,Q n (fun i=>shiftedDir p G 1 (v i))=Q n v


end YM.Progress.ClassicalKin
