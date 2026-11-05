import YM.Next.RANK.Flux.Collection
import YM.Next.RANK.Flux.Pavilion

/-!
# Lift nonempty sector first. Then unforced log and flagged assembly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}
variable (S : ι→ Plug G ζ t)

abbrev Bright := { i // ¬(S i).landed }
abbrev Dimmed := { i // (S i).landed }
def drain : ι ≃ Bright S⊕Dimmed S:=(Equiv.sumCompl (fun i=> (S i).landed)).symm.trans (Equiv.sumComm ..)
def sunny (i : Bright S) := (Plug.innocent i.property).choose
def evening (i : Dimmed S) := (Plug.flushed i.property).choose
lemma bright_valid (i : Bright S): S i.val=.regular (sunny S i) := (Plug.innocent i.property).choose_spec
lemma dim_valid (i : Dimmed S): S i.val=.raid (evening S i):= (Plug.flushed i.property).choose_spec
lemma drunk : S=Sum.elim (fun i=> Plug.regular (sunny S i)) (fun i=> Plug.raid (evening S i)) ∘ drain S:= by
  ext i
  obtain ⟨w,rfl⟩:= (drain S).symm.surjective i
  rw [Function.comp_apply,Equiv.apply_symm_apply]; rcases w with a|a; exacts [bright_valid _ _,dim_valid _ _]

variable [Fintype ι] [Fintype κ]
private lemma emblem (X : ι≃κ) (S : κ→Plug G ζ t) (U) : deck_at (S ∘ X) U=deck_at S U:= by
  unfold deck_at; rw [Finset.sum_filter,Finset.sum_filter]; refine Fintype.sum_equiv X.finsetCongr _ _ ?_; intro p
  let v:=p.map X.toEmbedding
  have h: unmark (S ∘ X) p (flags t U)↔unmark S v (flags t U):= by
    have he : v.biUnion (fun i=> (S i).inventory)=p.biUnion fun i=>(S (X i)).inventory:= by ext; simp [v,mem_biUnion];rw [X.exists_congr_left];simp
    simp only [unmark,he,Function.comp_apply]; refine and_congr_left fun _=> ?_
    rw [packed,packed,show (↑v:Set _)=(X '' (p:Set ι)) from ?_,Set.PairwiseDisjoint,Set.PairwiseDisjoint,X.injective.injOn.pairwise_image]
    simp [v, Finset.map_eq_image]
  split_ifs with hh hp hp
  · change _= ∏ i ∈ p.map X.toEmbedding,(S i).tolls U; rw [prod_map];rfl
  · exact False.elim (hp (h.mp hh))
  · exact False.elim (hh (h.mpr hp))
  rfl

def RAIDage (S : ι → Lifted G ζ t) U := ∑ i : Finset ι,Lifted.pack S i U
lemma storm (S : ι → Lifted G ζ t) U : deck_at (Plug.raid ∘ S) U=RAIDage S U:= by
  unfold deck_at; rw [Finset.sum_filter];apply sum_congr rfl; intro i hi; unfold Lifted.pack; split_ifs with hh hp hp; exact rfl; exact False.elim (hp hh); exact False.elim (hh hp); rfl

section
variable [DecidableEq ι]
variable (X : ι → SourceAt G ζ) (B : κ → Lifted G ζ t)

-- holes at effective unforced log entries from incompatible supports

def negXs (i : MergeLog X) : Lining G ζ t:= .inl {
  toInner (Bond X i) with value:= -(Bond X i).value
                          meas := (Bond X i).meas.neg
                          loc:= fun U u h=> congr_arg Neg.neg ((Bond X i).loc U u h)
                          inv:= fun j U=> congr_arg Neg.neg ((Bond X i).inv j U) }

-- implicit τ parameter
lemma negs (i : MergeLog X) (U : Config G n) : (raised (negXs (t:=t) X i)).covets U= -((Bond X i).amount t U):= by
  let z:=Bond X i; change Poly.send z.fires (masked _ z.extent (-z.value) U)= _
  have he: masked t z.extent (-z.value) U = - (masked t z.extent z.value U):= by
    by_cases ht:Healthy t z.extent U
    · rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ ht];rfl
    rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ ht,neg_zero]
  change _= - z.amount t U; rw [he]; ext j; unfold SourceAt.amount; simp only [Poly.part_send,Poly.part_neg];split<;>simp


def exclusion (p : Finset κ) := univ.filter fun i:ι=> ∀ j ∈ p, Disjoint (X i).extent (B j).extent

def braces (i : Finset (ι ⊕ κ)) := unmark (Sum.elim (Plug.regular ∘ X) (Plug.raid ∘ B)) i
omit [DecidableEq ι] in
lemma plucks (u : Finset ι) (v : Finset κ) (U) : braces X B (u.disjSum v) (flags t U) ↔ Lifted.gather B v U∧ packed (fun i=>(X i).extent) u∧ u⊆exclusion X B v:= by
  let S:=(Sum.elim (Plug.regular ∘ X) (Plug.raid ∘ B)); let I:=u.disjSum v
  have hv : I.biUnion (fun i=> (S i).inventory)=v.biUnion (fun i=> (B i).inventory):= by
    ext;rw [mem_biUnion,mem_biUnion]; constructor
    · rintro ⟨i|i,hi,hx⟩;exact False.elim (notMem_empty _ hx); exact ⟨i,inr_mem_disjSum.mp hi,hx⟩
    rintro ⟨i,hi,h⟩;exact ⟨.inr i,inr_mem_disjSum.mpr hi,h⟩
  constructor
  · rintro ⟨hd,h⟩
    have h₁ : (v:Set κ).PairwiseDisjoint (fun i=> (B i).extent):= fun i hi j hj hn=> hd (inr_mem_disjSum.mpr hi) (inr_mem_disjSum.mpr hj) (fun h=> hn (Sum.inr.inj h))
    exact ⟨⟨h₁,hv.symm.trans h⟩,(fun i hi j hj hn=> hd (inl_mem_disjSum.mpr hi) (inl_mem_disjSum.mpr hj) (fun h=> hn (Sum.inl.inj h))),fun i hi=> mem_filter.mpr ⟨mem_univ _,fun j hj=> hd (inl_mem_disjSum.mpr hi) (inr_mem_disjSum.mpr hj) (by simp)⟩⟩
  rintro ⟨h,hv',ht⟩
  refine ⟨fun i hi j hj he=> ?_,hv.trans h.2⟩
  rcases i with i|i<;>rcases j with j|j
  · exact hv' (inl_mem_disjSum.mp hi) (inl_mem_disjSum.mp hj) (fun h=> he (congr_arg _ h))
  · exact (mem_filter.mp (ht (inl_mem_disjSum.mp hi))).2 _ (inr_mem_disjSum.mp hj)
  · exact ((mem_filter.mp (ht (inl_mem_disjSum.mp hj))).2 _ (inr_mem_disjSum.mp hi)).symm
  exact h.1 (inr_mem_disjSum.mp hi) (inr_mem_disjSum.mp hj) (fun h=> he (congr_arg _ h))

omit [DecidableEq ι] in
lemma sunset (U):
    deck_at (Sum.elim (Plug.regular ∘ X) (Plug.raid ∘ B)) U = ∑ v : Finset κ,Lifted.pack B v U*chair (feet X) (fun i=>(X i).amount t U) (exclusion X B v):= by
  let S : ι⊕κ → Plug G ζ t:= Sum.elim (Plug.regular ∘ X) (Plug.raid ∘ B); let f (i) := if braces X B i (flags t U) then ∏ j∈i,(S j).tolls U else 0
  unfold deck_at; rw [Finset.sum_filter]
  have h : (∑ i : Finset (ι⊕κ),f i)= ∑ p : Finset ι ×Finset κ,f (p.1.disjSum p.2):= Fintype.sum_equiv Finset.sumEquiv.toEquiv _ _ fun i=> (congr_arg f (Finset.sumEquiv.symm_apply_apply i)).symm
  change (∑ i,f i)= _; rw [h,Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro j _
  unfold Lifted.pack; split
  · rename_i hg; rw [chair,mul_sum]; let v:=exclusion X B j
    rw [← sum_subset (subset_univ v.powerset)]; apply sum_congr rfl; intro i hi
    unfold f; by_cases he:packed (feet X) i
    · rw [if_pos he,if_pos ((plucks X B i j U).mpr ⟨hg,he,mem_powerset.mp hi⟩),prod_disjSum,mul_comm];rfl
    rw [if_neg he,mul_zero]; exact if_neg (fun h=> he (((plucks X B i j U).mp h).2.1))
    intro i _ hi; exact if_neg (fun h=> hi (mem_powerset.mpr (((plucks X B i j U).mp h).2.2)))
  rename_i hh;rw [zero_mul]; refine Finset.sum_eq_zero fun i _=> ?_; exact if_neg (fun h=>hh ((plucks ..|>.1 h).1))

lemma barred (s : MergeLog X) (v : Finset κ) : (∀ i∈s.val,i∈exclusion X B v) ↔ ¬earns (Plug.raid ∘ B) (negXs (t:=t) X) s v:= by
  constructor
  · rintro h ⟨j,hj,h₁,-⟩; obtain ⟨x,hx,hX⟩:=h₁; obtain ⟨u,hu,hz⟩:=mem_biUnion.mp (show x∈s.val.biUnion (feet X) from hX)
    exact disjoint_left.mp ((mem_filter.mp (h u hu)).2 j hj) hz hx
  intro h i hi; refine mem_filter.mpr ⟨mem_univ _,fun j hj=> disjoint_left.mpr ?_⟩; intro x hv ht;exact h ⟨j,hj,⟨x,ht,(show x∈s.val.biUnion (feet X) from mem_biUnion.mpr ⟨_,hi,hv⟩)⟩, fun _=> (B j).needed⟩
lemma lightning (U : Config G n) (v : Finset κ) : chair (feet X) (fun i=>(X i).amount t U) (exclusion X B v) =
    Poly.pass (∑ p : MergeLog X,(Bond X p).amount t U) * ∏ i∈univ.filter (fun j=>earns (Plug.raid ∘ B) (negXs X) j v), ((raised (t:=t) (negXs X i)).covets U+1):= by
  let F(p: MergeLog X) := (Bond X p).amount t U; let g:= exclusion X B v; let D:= univ.filter (fun s:MergeLog X=>s.val⊆g); let E:=univ \ D
  have ht:univ.filter (fun j=>earns (Plug.raid ∘ B) (negXs X) j v)=E:= by
    ext i; rw [mem_filter]; simp only [mem_univ,true_and,E,D,mem_sdiff,mem_filter]
    rw [← not_not (a:=earns _ _ _ _), ← barred X B i v]; rfl
  have h i: (F i).part (quiet _)=0:= asleep _ ((Bond X i).chosen) _
  have hL (p:Finset (MergeLog X)): (∑ i∈p,F i).part (quiet _)=0:= by rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun _ _=> h _)
  have he : (∏ i∈E, ((raised (t:=t) (negXs X i)).covets U+1))=Poly.pass (- (∑ i∈E,F i)):= by
    rw [← Finset.sum_neg_distrib,pass_sum]; apply prod_congr rfl; intro i _; rw [← negs]; exact (solo _ _ ((Bond X i).chosen)).symm
    intro i _; rw [Poly.part_neg,h,neg_zero]
  rw [ht,he,← monarch]; change Poly.pass (∑ i∈D,F i)= Poly.pass (∑ i,F i)*Poly.pass _; rw [← pass_add _ _ (hL _),← sum_sdiff (f:=F) (subset_univ D)]
  · congr 1; unfold E;abel
  rw [Poly.part_neg,hL,neg_zero]

-- Normal separate LOG
lemma put_in (U) : deck_at (Sum.elim (Plug.regular ∘ X) (Plug.raid ∘ B)) U = Poly.pass (∑ p:MergeLog X,(Bond X p).amount t U) * embellished (Plug.raid ∘ B) (negXs X) U:= by
  rw [sunset,embellished,Finset.sum_filter,Finset.mul_sum]; apply sum_congr rfl; intro i _
  rw [Lifted.pack]; split
  · rename_i ht; rw [if_pos (show unmark (Plug.raid ∘ B) i (flags t U) from ht),lightning]; rw [mul_left_comm];rfl
  rename_i ht; rw [if_neg (show ¬unmark (Plug.raid ∘ B) i (flags t U) from ht),mul_zero,zero_mul]
end

private lemma solves [DecidableEq ι] (U : Config G n) :
    let X:= sunny S; let D:= evening S
    let T:=panel (Plug.raid ∘ D) (negXs X)
    deck_at S U=Poly.pass (∑ i : MergeLog X,(Bond X i).amount t U) * deck_at T U:= by
  intro X D T
  let Z : Bright S ⊕ Dimmed S → Plug G ζ t := Sum.elim (fun i=> Plug.regular (X i)) (fun i=> Plug.raid (D i))
  have ht: deck_at (S:=Z) U=deck_at (Z ∘ drain S) U:= (emblem (drain S) Z U).symm
  calc
    _ = deck_at (Z ∘ drain S) U:= congr_arg (fun i:ι→ Plug G ζ t=>deck_at i U) (show S=_ from drunk S)
    _ = deck_at Z U:= ht.symm
    _ = _:= Eq.trans (put_in X D U) (congr_arg (fun p:veil V=> (Poly.pass (∑ i : MergeLog X,(Bond X i).amount t U))*p) (flood (Plug.raid ∘ D) (negXs X) U).symm)
lemma aftermath (P : κ → Lining G ζ t) (U):
    let v:=panel S P; let B:=sunny v
    let D:= evening v; embellished S P U= Poly.pass (∑ i : MergeLog B,(Bond B i).amount t U)*deck_at (panel (Plug.raid ∘ D) (negXs B)) U:= by
  intro v B D; exact Eq.trans (flood S P U).symm (solves v U)
end YM.Next.Rank.Flux
