import YM.Overlay.Terminal

set_option warningAsError false

/-!
# Singleton amplitudes in canonical mixed pass

Structural finite lemma, no budget loss, ordinary square-zero commuting ring.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Emit
open Set Filter Function MeasureTheory RG Wilson Lattice Marker Marker.Poly
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev rate (V : Type*) [Fintype V] [DecidableEq V] := Stock.census V
variable (A : Poly (rate V)) (x : (rate V).Mode)

abbrev mode (s : Finset V) : (rate V).Mode := ⟨s, Finset.mem_univ _⟩




lemma add_step (x y : Finset V) (h : Disjoint x y) (c d : ℂ) :
    send (mode x) c * send (mode y) d=send (mode (x∪y)) (c*d) := by
  apply Poly.ext; intro i
  change (Poly.prod _ _).part i=(send _ _).part i
  have ht : merges (mode x) (mode y) i ↔ i=mode (x∪y) := by
    simp only [merges,h,mode,true_and,Subtype.ext_iff]; exact eq_comm
  simp only [cart,ht,part_send]

lemma march (s : Finset V) (f : V → ℂ) :
    ∏ i∈s, send ((rate V).fire i) (f i) = send (mode s) (∏ i∈s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty,Finset.prod_empty]; rfl
  | @insert i s hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,ih,
      show (rate V).fire i=mode {i} from rfl,add_step _ _ (by simp [hi]), Finset.singleton_union]





variable (v : V) (c : ℂ)
private abbrev τ := send ((rate V).fire v) c








end YM.ProjectorNext.RMirror.Emit
