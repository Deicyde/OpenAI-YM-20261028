import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Polydisc
import YM.Corona.Halo
import YM.SectorNext.RECONNECTED_LOCALITY.Hoe


set_option warningAsError false

/-!
No address collapse incl if reversed or traced. $q$ labels
will keep entire color summation inside -- avoid a scalar-per-color alphabet
whose Gauge condition would then have to be relaxed. Ambient rates in output
lattice sites. Strip supports retain positions even for a zero value, e.g.
when window drops a leg among otherwise allowed ones. (Can omit non-numerical
range at the enumeration stage because tests and geometry are syntax-fixed and
`Wired.wide` literal; we instead use a zero cost there; either keep zero or
subtype on *committed* ranges.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Ice
open Function Matrix Finset Lattice RG Wilson Bind Window
open scoped BigOperators
variable {G:Gauge} {I J K κ ι η : Type*} {Y : η→Type*} {c : Side}

/-- $j$ inner legs and one terminator, full position record. -/
abbrev Logs (I : Type*) (n : ℕ) := I × (Fin n→I) × I



/- every position keeps its B cover (query halo radius R, marketing halo Y etc.) -/
def margin (p : I→Site c) (R : ℕ) (x:I) := around R (p x)

def crests (p : I→Site c) (R : ℕ) : (n : ℕ)→Logs I n→Support c
  | 0,l => margin p R l.1 ∪ margin p R l.2.2
  | n+1,(x,h,t) => margin p R x ∪ crests p R n (h 0,Fin.tail h,t)

def thread (p : I→Site c) (R : ℕ) : (n : ℕ)→Logs I n→Prop
  | 0,l => separation (p l.1) (p l.2.2)≤R
  | n+1,(x,h,t) => separation (p x) (p (h 0))≤R ∧ thread p R n (h 0,Fin.tail h,t)

lemma root_held (p : I→Site c) (R n) (l : Logs I n) : margin p R l.1 ⊆ crests p R n l := by
  cases n <;> rcases l with ⟨x,h,t⟩ <;> exact subset_union_left





/-- Charge each halo at $R=rB$. `thread` includes all nonzero
$S,A$ legs by the Wired supplies. Such halos really do meet at the
driving cover radius. No telescoping. -/
lemma prices (p : I→Site c) (r B n : ℕ) (hB : 0<B) (l : Logs I n) (h : thread p (r*B) n l) :
    coverNumber B (crests p (r*B) n l) ≤ (n+2)*(r+r+1)^4 := by
  let R:=r*B
  have hh i j (hd : separation (p i) (p j)≤R) {U : Support c} (hu : margin p R j⊆U) :
      coverNumber B (margin p R i ∪ U)≤(r+r+1)^4+coverNumber B U :=
    (Corona.meets_sum (x:=p j) (visible.mpr hd) (hu house) B).trans (Nat.add_le_add_right (Corona.tile (p i) r B hB) _)
  induction n with
  | zero => have he:=hh _ _ (show _ from h) (Finset.Subset.refl (margin p R l.2.2))
            exact he.trans (by have:=Corona.tile (p l.2.2) r B hB; change coverNumber _ (margin p R _)≤_ at this; omega)
  | succ n ih => rcases l with ⟨x,e,t⟩; obtain ⟨hx,he⟩:=h
                 have hm:=hh x (e 0) hx (root_held p R n (e 0,Fin.tail e,t))
                 have := ih _ he
                 unfold crests; apply hm.trans; nlinarith

section algebra
variable [Fintype I] [Fintype κ]
local notation "D" => Matrix (I×κ) (I×κ) ℝ
local notation "S" => Matrix κ κ ℝ









-- Hardened Z score for each whole label. `charge` does not use
-- integrability of $Z^tC^-1Z$; only on selected legs.








end algebra
end Ice
end YM.SectorNext.Reconnect
