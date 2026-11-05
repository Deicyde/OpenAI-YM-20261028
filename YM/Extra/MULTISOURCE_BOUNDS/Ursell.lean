import Mathlib.Combinatorics.SimpleGraph.Acyclic
import YM.Next.EXTRACTION.Tails



/-!
# Alternating connected-choice estimate for the coefficient of a marked log

Simple graphs on the *occurrences*, not on the set of distinct
spatial supports.

Sum over any subset of the available overlap edges: bound
by rooted trees using add/delete; an optional edge already connected through
the forced edges kills the sum exactly.

No probabilistic interpretation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.Mayer
open Function Filter Finset SimpleGraph
open scoped Topology BigOperators Classical

variable {V : Type*}

private lemma redundant {G : SimpleGraph V} {i j : V} (h : G.Reachable i j) :
    (G ⊔ edge i j).Connected ↔ G.Connected := by
  refine ⟨fun H => ?_,Connected.mono le_sup_left⟩
  haveI := H.nonempty
  refine ⟨fun x y => ?_⟩
  induction reachable_iff_reflTransGen _ _ |>.mp (H x y) with
  | refl => exact Reachable.refl _
  | tail _ he ih =>
    apply ih.trans
    obtain he|he := (sup_adj ..).mp he
    · exact he.reachable
    obtain ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩ := (edge_adj ..).mp he; exacts [h,h.symm]

def polymer (H : SimpleGraph V) (s : Finset (Sym2 V)) := if (H ⊔ fromEdgeSet s).Connected then (-1:ℝ)^s.card else 0

def tree (H : SimpleGraph V) (s : Finset (Sym2 V)) : ℝ := if (H ⊔ fromEdgeSet s).IsTree then 1 else 0

lemma connected_sum_le (H : SimpleGraph V) (hH : H.IsAcyclic) (s : Finset (Sym2 V)) :
    |∑ t∈s.powerset,polymer H t| ≤ ∑ t∈s.powerset,tree H t := by
  induction s using Finset.induction_on generalizing H with
  | empty =>
    simp only [powerset_empty,sum_singleton,polymer,tree,coe_empty,fromEdgeSet_empty,sup_bot_eq,
      isTree_iff,and_iff_left hH,card_empty,pow_zero]; split <;> norm_num
  | @insert e s he ih =>
    induction e using Sym2.inductionOn with | _ i j =>
    let H' := H ⊔ edge i j
    have hh t : H ⊔ fromEdgeSet ↑(insert s(i,j) t : Finset (Sym2 V)) = H' ⊔ fromEdgeSet ↑t := by
      simp only [H',edge,Finset.coe_insert, ← Set.singleton_union,fromEdgeSet_union,sup_assoc]
    have ha t (ht : t∈s.powerset) : polymer H (insert s(i,j) t) = -polymer H' t := by
      rw [polymer,card_insert_of_notMem (fun h => he (mem_powerset.mp ht h)),hh,polymer]
      split <;> simp [pow_succ]
    rw [sum_powerset_insert he, sum_congr rfl ha, Finset.sum_neg_distrib,sum_powerset_insert he]
    conv_rhs => rhs; arg 2; intro t; rw [tree,hh]
    change _ ≤ (∑ t∈s.powerset,tree H t) + (∑ t∈s.powerset, tree H' t)
    by_cases hp : H.Reachable i j
    · rw [show polymer H'=polymer H by
        funext t; unfold polymer H'
        rw [sup_right_comm,redundant (hp.mono le_sup_left)]]
      rw [add_neg_cancel,abs_zero]
      exact add_nonneg (sum_nonneg fun i _ => by unfold tree; split <;> norm_num) (sum_nonneg fun i _ => by unfold tree; split <;> norm_num)
    exact (abs_add_le ..).trans (add_le_add (ih H hH) (by simpa using ih H' (hH.sup_edge_of_not_reachable hp)))

/-- Rooted trees as decreasing parent functions (root maps to itself and
has no parent edge). Avoid choosing orderings of daughter subtrees in the
bound. -/
def Trunk (H : SimpleGraph V) (r : V) (f : V → V) := f r=r ∧ ∃ d : V→ℕ, ∀ i ≠ r, d (f i) < d i ∧ H.Adj i (f i)

theorem hasTrunk (H : SimpleGraph V) (h : H.Connected) (r : V) : ∃ f, Trunk H r f := by
  have he i (hi : i≠r) : ∃ j,H.Adj i j ∧ H.dist j r < H.dist i r := by
    obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist i r
    cases p with
    | nil => exact (hi rfl).elim
    | cons hj p => exact ⟨_,hj,(dist_le p).trans_lt (hp ▸ Nat.lt_succ_self _)⟩
  let f i := if hi : i=r then r else (he i hi).choose
  refine ⟨f,dif_pos rfl,(fun i => H.dist i r),fun i hi => ?_⟩
  rw [show f i=_ from dif_neg hi]; exact (he i hi).choose_spec.symm

private def graph (f : V → V) : SimpleGraph V where
  Adj x y := (f x=y ∨ f y=x) ∧ x≠y
  symm := ⟨fun x y h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ => by simp⟩

lemma trunk_read {H : SimpleGraph V} (h : H.IsTree) {r : V} {f : V → V} (he : Trunk H r f) : H = graph f := by
  obtain ⟨hr,d,hd⟩ := he
  have hle : graph f ≤ H := fun i j ⟨he,hh⟩ => (by
    rcases he with rfl|he
    · exact (hd _ (fun hx => hh (by rw [hx,hr]))).2
    exact he ▸ (hd _ (fun hx => hh (by rw [hx,hr] at he; exact he.symm.trans hx.symm))).2.symm)
  have Hx (n : ℕ) : ∀ i, d i = n → (graph f).Reachable i r := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      by_cases hx : i=r
      · rw [hx]
      have ht := (hd i hx).1
      exact (show (graph f).Adj i (f i) from ⟨Or.inl rfl,fun he => by rw [← he] at ht; omega⟩).reachable.trans
        (ih _ (ht.trans_eq hi) _ rfl)
  exact le_antisymm ((isTree_iff_minimal_connected.mp h).le_of_le ((connected_iff_exists_forall_reachable _).mpr
    ⟨r,fun i => (Hx _ i rfl).symm⟩) hle) hle

variable [Fintype V]

open scoped Classical in
def pairs (H : SimpleGraph V) := H.edgeFinset

def ursell (H : SimpleGraph V) : ℝ := ∑ s ∈ (pairs H).powerset,polymer ⊥ s

def spans (H : SimpleGraph V) (r : V) : Finset (V → V) := univ.filter (Trunk H r)

theorem tree_estimate (H : SimpleGraph V) (r : V) : |ursell H| ≤ (spans H r).card := by
  classical
  apply (connected_sum_le _ SimpleGraph.isAcyclic_bot (pairs H)).trans
  simp only [tree, bot_sup_eq, sum_boole]
  norm_cast
  let s := (pairs H).powerset.filter (fun s : Finset (Sym2 V) => (fromEdgeSet (↑s : Set (Sym2 V))).IsTree)
  let f (t : Finset (Sym2 V)) := if ht : t ∈ s then
      (hasTrunk (fromEdgeSet ↑t) (mem_filter.mp ht).2.connected r).choose else id
  have he {t} (ht : t∈s) : Trunk (fromEdgeSet ↑t) r (f t) := by
    unfold f; rw [dif_pos ht]; exact (hasTrunk _ (mem_filter.mp ht).2.connected _).choose_spec
  have hle {t} (ht : t∈s) : (↑t : Set (Sym2 V)) ⊆ H.edgeSet := coe_edgeFinset H ▸
    (show (↑t:Set (Sym2 V)) ⊆ (pairs H) from (mem_powerset.mp (mem_filter.mp ht).1))
  refine card_le_card_of_injOn f (fun i hi => mem_filter.mpr ⟨mem_univ _,?_⟩) (fun i hi j hj hij => ?_)
  · obtain ⟨a,d,hx⟩ := he hi
    have hb : fromEdgeSet (↑i : Set _) ≤ H := H.fromEdgeSet_edgeSet ▸ fromEdgeSet_mono (hle hi)
    exact ⟨a,d,fun i hi => ⟨(hx i hi).1,hb (hx i hi).2⟩⟩
  have hw {i j} (hi : i∈s) (hj : j∈s) (hij : f i = f j) : i ⊆ j := by
    have ht : fromEdgeSet (↑i : Set (Sym2 V)) = fromEdgeSet (↑j : Set (Sym2 V)) := by
      rw [trunk_read (mem_filter.mp hi).2 (he hi), hij,← trunk_read (mem_filter.mp hj).2 (he hj)]
    intro x hx; induction x using Sym2.inductionOn with | _ x y =>
    exact (show (fromEdgeSet ↑j).Adj x y from ht ▸ ⟨hx,(show H.Adj _ _ from hle hi hx).ne⟩).1
  exact subset_antisymm (hw hi hj hij) (hw hj hi hij.symm)

lemma ursell_ne (H : SimpleGraph V) (h : ursell H ≠ 0) : H.Connected := by
  classical
  by_contra he
  exact h (sum_eq_zero fun s hs => if_neg fun ht => he (ht.mono (sup_le bot_le ((fromEdgeSet_mono
    (show (↑s:Set _) ⊆ H.edgeSet from SimpleGraph.coe_edgeFinset H ▸
      (show (↑s:Set (Sym2 V)) ⊆ (pairs H : Set _) from mem_powerset.mp hs))).trans_eq H.fromEdgeSet_edgeSet))))

end YM.Extra.Multi.Mayer
