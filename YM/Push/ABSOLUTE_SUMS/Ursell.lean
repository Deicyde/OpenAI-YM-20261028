import YM.Push.ABSOLUTE_SUMS.Graph


/-!
# Literal hard-core Ursell coefficients

`pot` the actual overlap-edge set. Includes same-address incompatibility
(occurrences are numbered); for addresses with nonempty footprint that
just says overlap. graph mass is the full alternating sum,
not a formal bound on a different orientation of the edges. This
file includes equivariant reindexing needed to use the tree bound with
ANY test root. Use `coefficient` only for nonempty tuples.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Ursell
open Trees Graph Lattice Finset Relation
open scoped Classical Topology BigOperators
variable {ι α τ : Type*} {n : Side}

def blocked (X : ι → Support n) (i j : ι) := i=j ∨ Ac.meets X j (X i)
lemma blocked_back (X : ι → Support n) {i j : ι} (h : blocked X i j) : blocked X j i := by
  rcases h with h|⟨x,hx,he⟩
  · exact Or.inl h.symm
  exact Or.inr ⟨x,he,hx⟩

section Graphs
variable (R : ι → ι → Prop)

-- arbitrary hard exclusions, use symmetric ones for Ursell/tests.
def pot [Fintype α] (z : α → ι) : Network α := univ.filter
    (fun e : Finset α => e.card=2 ∧ ∀ i∈e, ∀ j∈e,i≠j → R (z i) (z j))

def coefficient [DecidableEq α] [Fintype α] (z : α → ι) : ℝ := mass (pot R z)

lemma potential_mem [Fintype α] (z : α → ι) (e : Finset α) : e ∈ pot R z ↔
    e.card=2 ∧ ∀ i∈e, ∀ j∈e,i≠j → R (z i) (z j) := by simp [pot]

lemma allow [DecidableEq α] [Fintype α] (z : α → ι) {i j : α}
    (h : link (pot R z) i j) : R (z i) (z j) := (potential_mem R z _ |>.mp h.2).2 _ (by simp) _
      (by simp) h.1

section Relabel
variable [DecidableEq α] [DecidableEq τ]

private lemma map_link (e : α ≃ τ) {S : Network α} {i j : α} :
    link (e.finsetCongr.finsetCongr S) (e i) (e j) ↔ link S i j := by
  unfold link
  have he : ({e i,e j}:Finset τ)=e.finsetCongr ({i,j}:Finset α) := by
    simp [Equiv.finsetCongr]
  rw [he]
  simp [Equiv.finsetCongr]

private lemma connected_equiv (e : α ≃ τ) (S : Network α) (h : reaches S) :
    reaches (e.finsetCongr.finsetCongr S) := by
  intro i j; obtain ⟨i,rfl⟩ := e.surjective i; obtain ⟨j,rfl⟩ := e.surjective j
  induction h i j with
  | refl => exact .refl
  | tail _ ht IH => exact .tail IH ((map_link e).mpr ht)

lemma relabel_mass (e : α ≃ τ) (T : Network α) : mass (e.finsetCongr.finsetCongr T) = mass T := by
  let p := e.finsetCongr.finsetCongr
  symm
  apply Finset.sum_equiv p
  · intro i; rw [belongs,belongs]
    apply and_congr
    · simp [p,Equiv.finsetCongr,Finset.map_subset_map]
    constructor
    · exact connected_equiv e _
    intro he
    have h := connected_equiv e.symm _ he
    change reaches (p.symm (p i)) at h
    rwa [p.symm_apply_apply] at h
  intro i _; simp only [alternating,p,Equiv.finsetCongr,Equiv.coe_fn_mk, Finset.card_map]

omit [DecidableEq α] [DecidableEq τ] in
lemma relabel_pot [Fintype α] [Fintype τ] (e : α ≃ τ) (z : τ → ι) :
    pot R z = e.finsetCongr.finsetCongr (pot R (z ∘ e)) := by
  have he (s : Finset α) (i : α) : e i ∈ e.finsetCongr s ↔ i∈s := by simp [Equiv.finsetCongr]
  have hf (s : Finset α) : s∈pot R (z ∘ e) ↔ e.finsetCongr s ∈ pot R z := by
    rw [potential_mem,potential_mem, show (e.finsetCongr s).card=s.card from Finset.card_map _]
    apply and_congr_right; intro _; constructor
    · intro h i hi j hj hk
      obtain ⟨i,rfl⟩ := e.surjective i; obtain ⟨j,rfl⟩ := e.surjective j
      exact h _ ((he s i).mp hi) _ ((he s j).mp hj) (fun h => hk (congr_arg _ h))
    intro h i hi j hj hn
    exact h _ ((he s i).mpr hi) _ ((he s j).mpr hj) (e.injective.ne hn)
  ext s; obtain ⟨s,rfl⟩ := e.finsetCongr.surjective s
  rw [← hf]; change _ ↔ e.finsetCongr s ∈ (pot R (z ∘ e)).map e.finsetCongr.toEmbedding
  rw [Finset.mem_map_equiv,Equiv.symm_apply_apply]

lemma relabel [Fintype α] [Fintype τ] (e : α ≃ τ) (z : τ → ι) :
    coefficient R z = coefficient R (z ∘ e) := by
  rw [coefficient,relabel_pot R e z, relabel_mass]; rfl
end Relabel
end Graphs
end YM.Push.AbsoluteSums.Ursell
