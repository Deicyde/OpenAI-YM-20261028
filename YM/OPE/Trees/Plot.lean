import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
/-!
# Finite cluster trees (all internal vertices have scales)

Use a labelled tree including both internal nodes & leaves. An internal node
may have arbitrary finite valence, including 0; the root is internal. Leaves
outside `zones` have no children and provide the overall input tuple. All
nodes are reachable from the root (acyclic). This flat presentation eases
successive expansion and contraction in an arbitrary order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Finset
open scoped Classical
variable {I:Type}

structure Arboreal (I:Type) where
    root : I
    zones : Finset I
    parent : I→ I
    depth : I→ℕ
    direct : parent root=root
    inward (i:I) : parent i∈ zones
    step (i:I): i≠root→ depth (parent i)<depth i

namespace Arboreal
variable (s:Arboreal I) (i j k:I) {a b : I}

lemma initial : s.root∈ s.zones:= s.direct ▸ s.inward s.root
lemma not_parent (h:i≠s.root) : i≠s.parent i:= fun hz=>ne_of_lt (s.step i h) (congr_arg _ hz.symm)
lemma descends : s.depth (s.parent i) ≤ s.depth i:=by
    by_cases h:i=s.root; · subst i; rw [s.direct]
    exact (s.step i h).le
@[elab_as_elim]
theorem hill (s:Arboreal I)(i : I){P:I→ Prop} (h:P s.root) (hp:∀ i:I,i≠s.root→ P (s.parent i) → P i) : P i :=by
    by_cases hh:i=s.root; subst i; · exact h
    exact hp i hh (hill s (s.parent i) h hp)
termination_by s.depth i
decreasing_by exact s.step i hh
-- Anc incl self, parent root self.
def Anc : Prop := ∃ n : ℕ,s.parent^[n] j=i
variable {i j k}
lemma Anc.same (s: Arboreal I)(i) : s.Anc i i:= ⟨0,rfl⟩
lemma Anc.step (s:Arboreal I)(i) : s.Anc (s.parent i) i:= ⟨1,rfl⟩
lemma Anc.joins {s:Arboreal I} (h:s.Anc i j)(hp:s.Anc j k): s.Anc i k:=by
    obtain ⟨t,rfl⟩:=hp; obtain ⟨u,rfl⟩:=h; exact ⟨u+t, iterate_add_apply ..⟩
lemma closure (i) : s.Anc s.root i:= by
    induction i using s.hill with
    | h=> exact Anc.same ..
    | hp i hi ih=> exact ih.joins (Anc.step ..)
lemma Anc.excess {s:Arboreal I}(h:s.Anc i s.root): i=s.root:=by
    obtain ⟨n,rfl⟩:=h; induction n with
    | zero=>rfl
    | succ n ih=> rw [iterate_succ_apply',ih,s.direct]
lemma Anc.back {s:Arboreal I}(h:s.Anc i j)(he:j≠i) : s.Anc i (s.parent j):=by
    obtain ⟨k,hk⟩:=h; cases k with
    | zero=>exact (he hk).elim
    | succ n=>exact ⟨n,hk⟩
lemma Anc.depth {s:Arboreal I} (h:s.Anc i j) : s.depth i ≤ s.depth j:=by
    obtain ⟨n,rfl⟩:=h; induction n with
    | zero=> exact le_rfl
    | succ n ih=> rw [iterate_succ_apply']; exact (s.descends _).trans ih
lemma Anc.into {s:Arboreal I} (h:s.Anc i j)(he:j≠i): s.depth i<s.depth j:=
    (h.back he).depth.trans_lt (s.step _ (fun hx=> he ((hxe hx h).symm ▸ hx))) -- he prova inspect
where hxe (h':j=s.root)(h:s.Anc i j) : i=s.root:= (show s.Anc i s.root from h' ▸ h).excess
lemma Anc.unique {s:Arboreal I} (h:s.Anc i j)(hp:s.Anc j i): i=j:=
    Decidable.byContradiction fun hh=> not_lt_of_ge h.depth (hp.into hh)
lemma Anc.inner {s:Arboreal I}(h:s.Anc i j)(hi:j ∈ s.zones): i ∈ s.zones:=by
    obtain ⟨n,rfl⟩:=h; cases n with
    | zero=> exact hi
    | succ n=> rw [iterate_succ_apply']; exact s.inward _
lemma Anc.proper {s:Arboreal I}(h:s.Anc i j)(hh:j≠ i): i∈ s.zones:=(h.back hh).inner (s.inward j)
lemma Anc.compare {s:Arboreal I} (h:s.Anc i k)(hp:s.Anc j k): s.Anc i j ∨ s.Anc j i:=by
    obtain ⟨n,rfl⟩:=h; obtain ⟨t,rfl⟩:=hp; rcases le_total n t with h|h
    · obtain ⟨w,rfl⟩:=Nat.exists_eq_add_of_le h; exact Or.inr ⟨w, by rw [add_comm n w, iterate_add_apply]⟩
    obtain ⟨w,rfl⟩:=Nat.exists_eq_add_of_le h; exact Or.inl ⟨w, by rw [add_comm t w, iterate_add_apply]⟩

lemma Anc.along {s:Arboreal I} {j : I} (h:s.Anc i j)(P:I→ Prop)(he:P i)(hp:∀ k:I,s.Anc i k → s.Anc k j → k≠i → P (s.parent k) → P k) : P j:=by
    by_cases hh:j=i; · subst j; exact he
    exact hp j h (Anc.same ..) hh ((h.back hh).along P he (fun k hk hi hu hc=>hp k hk (hi.joins (Anc.step ..)) hu hc))
termination_by s.depth j
decreasing_by
    exact s.step _ (by intro hi; exact hh (hi.trans (show i=s.root from Anc.excess (hi▸h)).symm))
-- possibly Anc.same requires Fintype, remove

variable [Fintype I]
def kids (i) := Finset.univ.filter fun j=> j≠s.root∧ s.parent j=i
lemma related (i j): j∈ s.kids i↔j≠s.root∧ s.parent j=i:=by simp [kids]
lemma Anc.child {s:Arboreal I} (h:i∈ s.kids j): s.Anc j i := (s.related j i|>.1 h).2 ▸ Anc.step s i
lemma higher {s:Arboreal I} (h:i∈ s.kids j): s.depth j < s.depth i:= (s.related ..|>.1 h).2 ▸ s.step i (s.related ..|>.1 h).1
lemma useful {s:Arboreal I}(h:i∈ s.kids j): i ≠ j:= by
    intro h'; exact ne_of_lt (higher h) (congr_arg _ h'.symm)

lemma Anc.first {s:Arboreal I} {j : I} (h:s.Anc i j)(hp:j≠i) : ∃ k∈ s.kids i, s.Anc k j:=by
    by_cases hi:s.parent j=i; exacts [⟨j,(s.related ..).2 ⟨(fun hx=> hp (hx.trans (show i=s.root from (Anc.excess (hx▸h))).symm)),hi⟩,Anc.same ..⟩,by
      obtain ⟨k,hk,he⟩:=(h.back hp).first hi; exact ⟨k,hk,he.joins (Anc.step ..)⟩]
termination_by s.depth j
decreasing_by exact s.step _ (by intro hi; exact hp (hi.trans (show i=s.root from Anc.excess (hi▸h)).symm))

def Fork (s:Arboreal I) (i j k : I): Prop:= ∃ a∈ s.kids i, ∃ b∈ s.kids i, a≠b∧ s.Anc a j ∧ s.Anc b k
lemma divergence (h:¬s.Anc j k)(hp:¬ s.Anc k j)(hi:s.Anc i j)(hk:s.Anc i k): ∃ u∈ s.zones,s.Anc i u∧ s.Fork u j k := by
    let A:= ((Finset.univ : Finset I).filter (fun i=> s.Anc i j ∧ s.Anc i k)); obtain ⟨u,hU,hV⟩:= A.exists_max_image s.depth ⟨i,mem_filter.mpr ⟨mem_univ _,hi,hk⟩⟩; obtain ⟨hj,hk'⟩:= (mem_filter.mp hU).2
    have hψ: j≠u:= fun he=> h (he.symm ▸ hk'); obtain ⟨a,ha,hb⟩:= hj.first hψ; obtain ⟨a',ha',hb'⟩:= hk'.first (fun he=>hp (he.symm ▸ hj))
    refine ⟨u,hj.proper hψ,?_,a,ha,a',ha',fun hx=> ?_,hb,hb'⟩
    · have he:=hi.compare hj; rcases he with he|he; · exact he
      by_contra hx; exact not_lt_of_ge (hV i (mem_filter.mpr ⟨mem_univ _,hi,hk⟩)) (he.into (show i≠u from fun H=>hx (H ▸ Anc.same s i)))
    subst a'; exact not_lt_of_ge (hV a (mem_filter.mpr ⟨mem_univ _, hb,hb'⟩)) (higher ha)
lemma Fork.left {s:Arboreal I}(h:s.Fork i j k) : s.Anc i j ∧ j≠ i:= by
    obtain ⟨u,he,t,-,-,hu,-⟩:=h; exact ⟨(Anc.child he).joins hu,fun ht=> useful he (ht ▸ hu|>.unique (Anc.child he))⟩ -- ht syntax
lemma Fork.swap {s:Arboreal I}(h:s.Fork i j k):s.Fork i k j:=by obtain ⟨a,ha,b,hb,h,hi,hj⟩:=h; exact ⟨b,hb,a,ha,h.symm,hj,hi⟩
lemma Fork.inner {s:Arboreal I}(h:s.Fork i j k): i ∈ s.zones := h.left.1.proper h.left.2
end Arboreal
end YM.OPE
