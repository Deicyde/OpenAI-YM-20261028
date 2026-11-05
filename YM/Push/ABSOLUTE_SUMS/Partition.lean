import YM.Push.ABSOLUTE_SUMS.Ursell

/-!
# Hard cluster log applicability: the coefficient identity (I)

Use an ordinary graph-component identity, here rooted at one position,
with canonical summation within the actual overlap graph. In particular
no distinctness assumption on tuples and no forest approximation to
*compute* the coefficient.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Partition
open Relation Graph Ursell Finset
open scoped BigOperators Classical
variable {α ι : Type*} [DecidableEq α] [Fintype α]

-- all graphs valuation

def allMass (T : Network α) := ∑ i∈T.powerset, alternating i

omit [Fintype α] in
lemma allMass_eq (T : Network α) : allMass T = if T=∅ then 1 else 0 := by
  by_cases h : T=∅
  · simp [h,allMass,alternating]
  have hh := Finset.prod_one_add (f:=fun _ : Finset α => (-1:ℝ)) T
  simpa [allMass,h,alternating,card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr h),eq_comm] using hh.symm

section Restricted

-- ambient actual assignments `z`, restricted to subgraph

def restrict (s : Finset α) (z : α → ι) := fun i : ↥s => z i.val
private def edge (s : Finset α) (u : Finset ↥s) := u.image (fun i => (i.val:α))
private def place (s : Finset α) (G : Network ↥s) := G.image (edge s)

omit [Fintype α] in
private lemma injection (s : Finset α) : Function.Injective (edge s) :=
    Finset.image_injective Subtype.val_injective
omit [Fintype α] in
private lemma placed_mem (s : Finset α) (G : Network ↥s) (e : Finset ↥s) :
    edge s e ∈ place s G ↔ e ∈ G := by
  constructor
  · intro he; obtain ⟨i,hi,h⟩ := mem_image.mp he; exact injection s h ▸ hi
  intro he; exact mem_image_of_mem _ he
omit [Fintype α] in
private lemma witnesses (s : Finset α) (G : Network ↥s) {i : Finset α} (hi : i∈place s G) : i⊆s := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hi
  intro x hx; obtain ⟨x,hx,rfl⟩ := mem_image.mp hx; exact x.property
omit [Fintype α] in
private lemma pair_map (s : Finset α) (u v : ↥s) : edge s {u,v} = {u.val,v.val} := by simp [edge]
omit [Fintype α] in
private lemma linked (s : Finset α) (G : Network ↥s) (u v : ↥s) :
    link (place s G) u.val v.val ↔ link G u v := by
  unfold link; rw [← pair_map,placed_mem]; exact and_congr_left fun _ => ⟨fun h hn => h (hn ▸ rfl),
    fun h hn => h (Subtype.ext hn)⟩
private lemma local_edges (s : Finset α) (R : ι → ι → Prop) (z : α → ι) (e : Finset ↥s) :
    edge s e ∈ pot R z ↔ e∈pot R (restrict s z) := by
  have he : (edge s e).card = e.card := Finset.card_image_of_injective _ Subtype.val_injective
  rw [potential_mem,potential_mem,he]; apply and_congr_right; intro he
  constructor
  · intro h i hi j hj hk; refine h _ (mem_image_of_mem _ hi) _ (mem_image_of_mem _ hj) ?_
    exact fun h => hk (Subtype.ext h)
  intro h i hi j hj hk
  obtain ⟨i,hi2,rfl⟩ := mem_image.mp hi
  obtain ⟨j,hj2,rfl⟩ := mem_image.mp hj
  exact h i hi2 j hj2 (fun h => hk (congr_arg Subtype.val h))

private def part (s : Finset α) (G : Network α) : Network ↥s :=
    univ.filter (fun e => edge s e ∈ G)
omit [Fintype α] in
private lemma part_mem (s : Finset α) (G : Network α) (e : Finset ↥s) :
    e∈ part s G ↔ edge s e∈G := by simp only [part,mem_filter,mem_univ,true_and]
omit [Fintype α] in
private lemma inverse_range (s : Finset α) (G : Network α) (u : Finset α) :
    u ∈ place s (part s G) ↔ u ⊆ s ∧ u∈G := by
  constructor
  · intro h; refine ⟨witnesses s _ h,?_⟩
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h; exact (part_mem ..).mp hi
  rintro ⟨h,hu⟩
  let t := univ.filter (fun i : s => i.val∈u)
  have ht : edge s t=u := by
    ext i; rw [edge,mem_image]; constructor
    · rintro ⟨i,hi,rfl⟩; exact (mem_filter.mp hi).2
    intro hi; exact ⟨⟨i,h hi⟩,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩
  rw [← ht,placed_mem,part_mem,ht]; exact hu

-- Connected component of position o in physical graph.

def island (o : α) (G : Network α) := univ.filter (ReflTransGen (link G) o)
private lemma inside (o i : α) (G : Network α) : i∈island o G ↔ ReflTransGen (link G) o i := by
  simp [island]

-- Graphs in a fixed fiber, parametrized by the two independent graphs.

private def splitGraphs (s : Finset α) (R : ι → ι → Prop) (z : α → ι) :=
    (Graph.connectedGroups (pot R (restrict s z))) ×ˢ (pot R (restrict sᶜ z)).powerset
private def assembled (s : Finset α) (p : Network ↥s × Network ↥(sᶜ)) :=
    place s p.1 ∪ place sᶜ p.2

omit [Fintype α] in
private lemma block (s t : Finset α) (G : Network ↥s) (H : Network ↥t) (ht : Disjoint s t)
    {R : ι → ι → Prop} {z : α → ι} (hH : H ⊆ pot R (restrict t z)) : Disjoint (place s G) (place t H) := by
  refine Finset.disjoint_left.mpr fun i hi he => ?_
  have h1 := witnesses _ _ hi; have h2 := witnesses _ _ he
  obtain ⟨e,he2,rfl⟩ := mem_image.mp he
  have hv := (potential_mem R (restrict t z) e).mp (hH he2)
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0<e.card by rw [hv.1]; norm_num)
  have hy : y.val∈edge t e := mem_image_of_mem _ hy
  exact Finset.disjoint_left.mp ht (h1 hy) (h2 hy)

private lemma main_to (s : Finset α) (o : α) (ho : o∈s)
    {R : ι → ι → Prop} {z : α → ι} (p : Network ↥s × Network ↥(sᶜ))
    (hp : p∈splitGraphs s R z) : assembled s p∈ (pot R z).powerset ∧ island o (assembled s p)=s := by
  obtain ⟨hk,hh⟩ := mem_product.mp hp
  obtain ⟨hk,hg⟩ := Graph.belongs.mp hk
  have h {s : Finset α} (G : Network ↥s) (h : G⊆ pot R (restrict s z)) : place s G⊆pot R z := by
    intro i hi; obtain ⟨e,he,rfl⟩ := mem_image.mp hi; exact (local_edges ..).mpr (h he)
  refine ⟨Finset.mem_powerset.mpr (Finset.union_subset (h _ hk) (h _ (mem_powerset.mp hh))),?_⟩
  let Y := assembled s p
  have he (i : s) : ReflTransGen (link Y) o i.val := by
    have he : ∀ (a b : s), ReflTransGen (link p.1) a b → ReflTransGen (link Y) a.val b.val := by
      intro a b h; induction h with
      | refl => exact .refl
      | @tail b c _ hs IH =>
        have hy := (linked s p.1 b c).2 hs
        exact IH.tail ⟨hy.1,Finset.mem_union_left _ hy.2⟩
    exact he ⟨o,ho⟩ i (hg _ _)
  ext i; rw [inside]; constructor
  · intro he; induction he with
    | refl => exact ho
    | @tail b c _ hs IH =>
      rcases Finset.mem_union.mp hs.2 with hk|hk
      · exact witnesses s p.1 hk (by simp)
      exact absurd IH (mem_compl.mp (witnesses sᶜ p.2 hk (by simp)))
  intro hi; exact he ⟨_,hi⟩

private lemma main_back {R : ι → ι → Prop} {z : α → ι} (o : α) (G : Network α)
    (hG : G ∈ (pot R z).powerset) :
    let s := island o G
    (part s G,part sᶜ G) ∈ splitGraphs s R z ∧ assembled s (part s G,part sᶜ G)=G := by
  intro s
  have hc (s : Finset α) : part s G ⊆ pot R (restrict s z) := fun i hi =>
    (local_edges ..).mp (mem_powerset.mp hG ((part_mem s G _).mp hi))
  have ho : o ∈ s := (inside o o G).2 .refl
  have hi i (h : ReflTransGen (link G) o i) :
      ReflTransGen (link (part s G)) (⟨o,ho⟩ : s) ⟨i,(inside o i G).mpr h⟩ := by
    induction h with
    | refl => exact .refl
    | @tail a b hz hh IH =>
      apply IH.tail; unfold link
      constructor
      · exact fun h => hh.1 (congr_arg Subtype.val h)
      rw [part_mem,pair_map]; exact hh.2
  refine ⟨mem_product.mpr ⟨Graph.belongs.mpr ⟨hc s,?_⟩,Finset.mem_powerset.mpr (hc _)⟩,?_⟩
  · intro i j
    have ht : ReflTransGen (link (part s G)) i (⟨o,ho⟩:s) := by
      have ht (i j) (h : ReflTransGen (link (part s G)) i j) : ReflTransGen (link (part s G)) j i := by
        induction h with
        | refl => exact .refl
        | tail _ hx IH => exact .head (Graph.backwards hx) IH
      exact ht _ _ (hi i.val ((inside ..).mp i.property))
    exact ht.trans (hi j.val ((inside ..).mp j.property))
  ext i
  unfold assembled
  dsimp only; rw [mem_union,inverse_range,inverse_range]; constructor
  · rintro (h | h) <;> exact h.2
  intro hh
  by_cases h : i⊆sᶜ
  · exact Or.inr ⟨h,hh⟩
  obtain ⟨y,hy,hY⟩ := not_subset.mp h
  have hy' : y∈s := by simpa using hY
  refine Or.inl ⟨fun j hj => ?_, hh⟩
  by_cases he : y=j
  · exact he ▸ hy'
  have h : ({y,j} : Finset α)=i := by
    apply Finset.eq_of_subset_of_card_le
    · exact insert_subset hy (singleton_subset_iff.mpr hj)
    rw [(potential_mem R z i |>.mp (mem_powerset.mp hG hh)).1, Finset.card_pair he]
  exact (inside ..).2 (ReflTransGen.tail ((inside ..).mp hy') (show link G y j from ⟨he, h ▸ hh⟩))

private lemma split_price {R : ι → ι → Prop} {z : α → ι} {s : Finset α}
    (p : Network ↥s × Network ↥(sᶜ)) (hp : p∈splitGraphs s R z) :
    alternating (assembled s p)=alternating p.1*alternating p.2 := by
  unfold alternating assembled
  rw [Finset.card_union_of_disjoint (block s sᶜ p.1 p.2 disjoint_compl_right
    (mem_powerset.mp (mem_product.mp hp).2)),pow_add]
  rw [place,place,Finset.card_image_of_injective _ (injection s),Finset.card_image_of_injective _
    (injection sᶜ)]

private lemma main_inj {R : ι → ι → Prop} {z : α → ι} (s : Finset α)
    (p : Network ↥s × Network ↥(sᶜ)) (hp : p∈splitGraphs s R z)
    (q : Network ↥s × Network ↥(sᶜ)) (hq : q∈splitGraphs s R z)
    (he : assembled s p=assembled s q) : p=q := by
  have unique_part {t u : Finset α} (a a' : Network ↥t) (b b' : Network ↥u)
      (h : place t a ∪ place u b=place t a' ∪ place u b') (hd : Disjoint t u)
      (hb : b⊆pot R (restrict u z)) (hb' : b'⊆pot R (restrict u z)) : a=a' := by
    apply Finset.image_injective (injection t)
    change place t a = place t a'
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp (h ▸ Finset.mem_union_left (place u b) hi) with hh|hh
      · exact hh
      exact absurd hh (Finset.disjoint_left.mp (block t u a b' hd hb') hi)
    intro hi
    rcases Finset.mem_union.mp (h.symm ▸ Finset.mem_union_left (place u b') hi) with hh|hh
    · exact hh
    exact absurd hh (Finset.disjoint_left.mp (block t u a' b hd hb) hi)
  apply Prod.ext
  · exact unique_part _ _ _ _ he disjoint_compl_right (mem_powerset.mp (mem_product.mp hp).2)
      (mem_powerset.mp (mem_product.mp hq).2)
  unfold assembled at he; rw [Finset.union_comm,Finset.union_comm (place s q.1)] at he
  exact unique_part _ _ _ _ he disjoint_compl_left (Graph.belongs.mp (mem_product.mp hp).1).1
    (Graph.belongs.mp (mem_product.mp hq).1).1

/-- Split off the connected component of position o. -/
theorem partition (R : ι → ι → Prop) (z : α → ι) (o : α) :
    allMass (pot R z) = ∑ s ∈ (univ : Finset (Finset α)) with o ∈ s,
      coefficient R (restrict s z)*allMass (pot R (restrict sᶜ z)) := by
  let u := (pot R z).powerset
  let a := (univ : Finset (Finset α)).filter (fun s => o ∈ s)
  have he : (∑ s∈a, ∑ x∈u with island o x = s, alternating x)= allMass (pot R z) :=
    Finset.sum_fiberwise_of_maps_to (g:= island o) (s:=u) (t:=a) (fun x _ => Finset.mem_filter.mpr ⟨mem_univ _,(inside o o x).2 .refl⟩) alternating
  rw [← he]; apply Finset.sum_congr rfl; intro s hs
  have ho : o∈s := (mem_filter.mp hs).2
  calc
    _ = ∑ p∈splitGraphs s R z, alternating p.1 * alternating p.2 := by
      symm
      apply Finset.sum_bij (fun a _ => assembled s a) (fun a ha => mem_filter.mpr (main_to s o ho a ha))
        (main_inj s) ?_ (fun p hp => (split_price p hp).symm)
      intro b hb; obtain ⟨hb2,hc⟩ := mem_filter.mp hb
      subst s
      obtain ⟨h,e⟩ := main_back (R:=R) (z:=z) o b hb2; exact ⟨_,h,e⟩
    _ = _ := by unfold splitGraphs coefficient Graph.mass allMass; rw [Finset.sum_product, sum_mul]
                simp only [mul_sum]
end Restricted
end YM.Push.AbsoluteSums.Partition
