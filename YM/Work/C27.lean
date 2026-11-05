import YM.Analysis.Polydisc
import YM.Bid.Grow

set_option autoImplicit false
noncomputable section
namespace YM.Work.C27
open Boundary Mink
open scoped Topology BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

private theorem coordinate_tsupport (f : Fin n → Test4) (i : Fin n) :
    tsupport (Joint.materialize n f) ⊆ (fun x : Points n => x i) ⁻¹' tsupport (f i) := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro x hx
  apply subset_tsupport
  intro h
  apply hx
  exact (Joint.material_at f x).trans (Finset.prod_eq_zero (Finset.mem_univ i) h)

private theorem materialize_switch (P : NearPair n) (f : Fin n → Test4) :
    Probe.along P.switch.toContinuousLinearEquiv (Joint.materialize n f) = Joint.materialize n (f ∘ P.s) := by
  ext1 x
  change Joint.materialize n f (P.switch x) = _
  simp only [Joint.material_at, NearPair.switch_at, Function.comp_apply]
  exact ((Equiv.prod_comp P.s (fun i => f i (x (P.s i)))) |>.symm.trans (by simp [NearPair.s]))

private theorem exchange (W : Surface S) (H : Actor W) (P : NearPair n)
    (v : Fin n → S.Union) (f : Fin n → Test4) (hf : Fields.causal (f P.i) (f P.j)) :
    W.W n v (Joint.materialize n f) = W.W n (v ∘ P.s) (Joint.materialize n (f ∘ P.s)) := by
  have hs : tsupport (Joint.materialize n f) ⊆ P.gap := by
    intro x hx
    have hh := lateral _ |>.mp (hf (x P.i) (coordinate_tsupport f P.i hx) (x P.j) (coordinate_tsupport f P.j hx))
    change x P.j - x P.i ∈ spacelike
    rw [lateral, ← neg_sub (x P.i)]
    simpa only [clock_neg, rest_neg, abs_neg, norm_neg] using hh
  have hm := H n v P (Joint.materialize n f) hs
  change W.W n v _ - W.W n _ (Probe.along _ _) = 0 at hm
  rwa [sub_eq_zero, materialize_switch] at hm

private theorem expect_get (W : Surface S) (b : Sentence S) (v : Fin n → Letter S)
    (h : b.length = n) (hv : ∀ i, b.get i = v (Fin.cast h i)) :
    W.expect b = W.W n (fun i => (v i).1) (Joint.materialize n (fun i => (v i).2)) := by
  subst n
  have he : b.get = v := funext hv
  rw [Surface.expect, he]

variable {α : Type*}

/-- Place two letters between the spectator lists. -/
private def slots (a b : List α) (x y : α) (i : Fin (a.length + (b.length+2))) : α :=
    if h : i.val < a.length then a[i.val]
    else if _ : i.val = a.length then x
    else if _ : i.val = a.length+1 then y
    else b[i.val-(a.length+2)]'(by omega)

private def pair (a b : List α) : NearPair (a.length + (b.length+2)) :=
  ⟨⟨a.length, by omega⟩, ⟨a.length+1, by omega⟩, rfl⟩

private theorem get_slots (a b : List α) (x y : α) (i : Fin (a ++ x::y::b).length) :
    (a ++ x::y::b).get i = slots a b x y (Fin.cast (by simp) i) := by
  simp only [List.get_eq_getElem, slots, Fin.val_cast]
  split_ifs with h1 h2 h3
  · exact List.getElem_append_left h1
  · rw [List.getElem_append_right (by omega)]
    generalize_proofs _
    simp [h2]
  · rw [List.getElem_append_right (by omega)]
    generalize_proofs _
    simp [h3]
  rw [List.getElem_append_right (by omega)]
  have h : i.val - a.length = i.val - (a.length+2) + 1 + 1 := by omega
  generalize_proofs _
  simp [h]

private theorem slots_switch (a b : List α) (x y : α) (i : Fin (a.length + (b.length+2))) :
    slots a b x y ((pair a b).s i) = slots a b y x i := by
  rcases eq_or_ne i (pair a b).i with rfl|hi
  · simp [NearPair.s, slots, pair]
  rcases eq_or_ne i (pair a b).j with rfl|hj
  · simp [NearPair.s, slots, pair]
  rw [NearPair.s, Equiv.swap_apply_of_ne_of_ne hi hj]
  have h : i.val ≠ a.length := fun h => hi (Fin.ext h)
  have k : i.val ≠ a.length+1 := fun h => hj (Fin.ext h)
  simp [slots, h, k]

theorem answer : YM.Bid.C27 := by
  intro G L S W H a b x y f g h
  rw [expect_get W _ _ _ (get_slots a b (x,f) (y,g)), expect_get W _ _ _ (get_slots a b (y,g) (x,f))]
  have he := exchange W H (pair a b) (fun i => (slots a b (x,f) (y,g) i).1)
    (fun i => (slots a b (x,f) (y,g) i).2) (by simpa [pair,slots] using h)
  simpa only [Function.comp_def,slots_switch] using he

end YM.Work.C27
