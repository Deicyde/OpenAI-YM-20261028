import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Joint

/-!
# Birth receipt on the actual h replicated array at station k

Some of the physics request's algebra and norm production. Don't ask new
RG at all labels on all levels before these lemmas. CAN take authentic old
array lane through k, inject a canonical *coarse* source at k on the same
remaining variable, exact masks + unit, and with explicit upstream reserve
and launch costs obtain combined birth `Bands`. All selected sites carry
one marker each; can/should use requiring ticket I03 for alignment upstream
of that old supply. Use negative old, positive new in the same square-zero
census. Aggregating alternative addresses by mode (as in Attach modules),
not promising to solve sign-preserving dynamics from this identity alone.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Birth
open RG Lattice Wilson MeasureTheory Function Filter Finset Ac Marker Overlay Attach Cells Joint
open scoped Topology BigOperators

section fire
variable {V : Type*} [Fintype V] [DecidableEq V]
private def bucket (i : Finset V) : (Stock.census V).Mode := ⟨i,Finset.mem_univ _⟩

private lemma pile {x y : Finset V} (he : Disjoint x y) (p q : ℂ) :
    Poly.send (bucket x) p * Poly.send (bucket y) q = Poly.send (bucket (x∪y)) (p*q) := by
  ext i
  rw [Poly.part_send]
  change (Poly.prod _ _).part _ = _
  have h : Poly.merges (bucket x) (bucket y) i ↔ i=bucket (x∪y) :=
    ⟨fun h => Subtype.ext h.2.symm,fun h => h.symm ▸ ⟨he,rfl⟩⟩
  simp only [Poly.cart,h]

private lemma submits (s : Finset V) (f : V → ℂ) :
    ∏ i∈s, Poly.send ((Stock.census _).fire i) (f i) = Poly.send (bucket s) (∏ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty]; rfl
  | insert i s hi ih =>
    rw [prod_insert hi,ih,prod_insert hi]
    change Poly.send (bucket {i}) _ * _ = _
    rw [pile (by simpa using hi),Finset.singleton_union]

private lemma union_read {x y z : Finset V} : Poly.merges (bucket x) (bucket y) (bucket z) ↔
    y⊆z ∧ x=z\y := by
  change Disjoint x y ∧ x∪y=z ↔ _
  constructor
  · rintro ⟨he,rfl⟩
    refine ⟨subset_union_right,?_⟩; ext i; simp only [Finset.mem_sdiff,mem_union]
    constructor
    · intro hi; exact ⟨Or.inl hi,fun h => Finset.disjoint_left.mp he hi h⟩
    rintro ⟨h1,h2⟩; tauto
  rintro ⟨hx,rfl⟩; exact ⟨Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hx⟩

private lemma fires (A : Poly (Stock.census V)) (y s : Finset V) (x : ℂ) :
    (A*Poly.send (bucket y) x).part (bucket s) = if y⊆s then A.part (bucket (s\y)) * x else 0 := by
  rw [Poly.part_mul]
  let f (i j : (Stock.census V).Mode) := if Poly.merges i j (bucket s) then A.part i*(Poly.send (bucket y) x).part j else 0
  have he (i : (Stock.census V).Mode) : ∑ j, f i j=f i (bucket y) := by
    rw [Finset.sum_eq_single (bucket y)]; intro j _ hj; unfold f; simp only [Poly.part_send,if_neg hj]; split <;> simp
    simp
  have hc (i : (Stock.census V).Mode) : f i (bucket y) = if y⊆s then (if i = bucket (s\y) then A.part i*x else 0) else 0 := by
    unfold f; have hh : Poly.merges i (bucket y) (bucket s) ↔ y⊆s ∧ i = bucket (s\y) := by
      change Poly.merges (bucket i.val) _ _ ↔ _; rw [union_read]; exact and_congr_right fun _ => Iff.intro (fun h => Subtype.ext h) (fun h => congr_arg Subtype.val h)
    simp [hh,ite_and]
  change (∑ i, ∑ j, f i j)=_
  simp_rw [he,hc]; split <;> simp

lemma array_read (A : Poly (Stock.census V)) (s : Finset V) (f : V → ℂ) :
    (A*∏ i, (1+Poly.send ((Stock.census V).fire i) (f i))).part (bucket s) =
      ∑ l∈s.powerset, A.part (bucket (s\l))*∏ i∈l,f i := by
  classical
  rw [prod_one_add,mul_sum,Poly.part_sum]; simp_rw [submits, fires]
  let w (l : Finset V) := A.part (bucket (s\l))*∏ i∈l,f i
  have hb : s.powerset ⊆ Finset.univ.powerset := fun x hx => Finset.mem_powerset.mpr (subset_univ x)
  have he : ∀ l ∈ s.powerset, (if l⊆s then w l else 0) = w l := fun l h => if_pos (Finset.mem_powerset.mp h)
  have hz : ∀ l∈ Finset.univ.powerset, l∉s.powerset → (if l ⊆ s then w l else 0)=0 :=
    fun l _ hh => if_neg (mt Finset.mem_powerset.mpr hh)
  exact (Finset.sum_subset hb hz).symm.trans (Finset.sum_congr rfl he)
end fire

section ups
variable {V : Type*} [DecidableEq V] {R : Census V}



variable {G : Gauge} {H : History G} {O : Type*} {p N m k : ℕ}

lemma push_first (H : History G) (N p : ℕ) (he : m+1≤k) (F : Config G (H.S.side k p) → ℂ) :
    pushTo H N p (show m≤k from le_trans (Nat.le_succ _) he) F =
      (H.levels.clock.op m p).push (H.β N p (m+1)) (pushTo H N p he F) := by
  induction k,he using Nat.le_induction with
  | base => rw [pushTo_next H N p (le_refl m),pushTo_self,pushTo_self]
  | succ i hi ih => rw [pushTo_next H N p (le_trans (Nat.le_succ _) hi),pushTo_next H N p hi,ih]

-- Function version of old signal equality to the old negative term of
-- Grid's join, at every V. Not just evaluated under Haar.

variable {h : ℕ}




end ups

section combined
variable {G : Gauge} (C : Family G) {h k d N p : ℕ}
    (H : C.Makes) (hk : h≤k) (he : k≤N) (hr : C.ref d ≤ k)
    (v x : C.label d) (L : Lane C.path (Markers C.path h p) N p)




end combined
end YM.Push.GridApprox.Birth
