import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Animals
import YM.Work.E01


/-!
# Mandatory defect packet alphabet

The three typed seeds are physical indices, not coordinates
in a sector-dependent chart.

They can COINCIDE spatially.

Output support
is the whole union of coarse halos including incident points/projections.

Take `l = 500` for E's radii, or predeclare a larger halo factor as
needed.

We impose no period-size assumption on these counts.

One address in this alphabet counts exactly a SET of seeds, nonempty
with overlapping-halo connectivity. There is no default-only address per
every sector table in the alphabet, no sum over unrealized completions
or choices of witnesses attached to a set. In applications the grammar
has to see to that, or pay also for the variants. Tag / field variables
here do not multiply the count; they have to be retained/coupled when
proving uniform per-term weight estimates. `Teller` predicates use the
precise `Stores` data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Packets
open Lattice Wilson Pressure RG Finset Animals Lattice.Corona Relation
open scoped BigOperators Topology Classical

variable {c f : Side} (S : StepData c f)

abbrev Seed (_S : StepData c f) := Cell f ⊕ Bond c ⊕ Site c

def seeds (A : Stores S) : Finset (Seed S) := A.costs.disjSum (A.aisles.disjSum A.flags)

def store (s : Finset (Seed S)) : Stores S :=
  ⟨s.toLeft,s.toRight.toLeft,s.toRight.toRight⟩

lemma store_seeds (A : Stores S) : store S (seeds S A) = A := by
  simp only [store,seeds,toLeft_disjSum,toRight_disjSum]

lemma seeds_store (s : Finset (Seed S)) : seeds S (store S s) = s := by
  ext i; rcases i with p|b|x <;> simp [store,seeds]

def sectorAlphabet : Stores S ≃ Finset (Seed S) :=
  ⟨seeds S,store S,store_seeds S,seeds_store S⟩

lemma seeds_card (A : Stores S) : (seeds S A).card = A.shares := by
  simp only [seeds,Finset.card_disjSum,Stores.shares,Nat.add_assoc]

lemma store_price (s : Finset (Seed S)) : (store S s).shares=s.card := by
  rw [← seeds_card S,seeds_store]

def anchor : Seed S → Site c
  | .inl p => S.ratio.parent p.1
  | .inr (.inl b) => b.1
  | .inr (.inr x) => x

def points : Seed S → Support c
  | .inl p => startPos S p
  | .inr (.inl b) => pinPos b
  | .inr (.inr x) => {x}

def skin (l B : ℕ) (i : Seed S) := halo (l*B) (points S i)

def support (l B : ℕ) (s : Finset (Seed S)) := s.biUnion (skin S l B)

def Whole (l B : ℕ) (s : Finset (Seed S)) := Ac.Spark (skin S l B) s

def connected (l B : ℕ) (A : Stores S) := Whole S l B (seeds S A)

lemma place_reads (A : Stores S) : (seeds S A).biUnion (points S) = A.place := by
  ext x
  rw [mem_biUnion,Stores.place,mem_union,mem_union]; constructor
  · rintro ⟨p,hp,hx⟩; rcases p with p|b|y
    · exact Or.inl (Or.inl (mem_biUnion.mpr ⟨p,inl_mem_disjSum.mp hp,hx⟩))
    · exact Or.inl (Or.inr (mem_biUnion.mpr ⟨b,by simpa [seeds] using hp,hx⟩))
    obtain rfl := mem_singleton.mp hx; exact Or.inr (by simpa [seeds] using hp)
  · rintro ( (h | h) | h )
    · obtain ⟨p,hp,hx⟩ := mem_biUnion.mp h; exact ⟨.inl p,by simp [seeds,hp],hx⟩
    · obtain ⟨p,hp,hx⟩ := mem_biUnion.mp h; exact ⟨.inr (.inl p),by simp [seeds,hp],hx⟩
    exact ⟨.inr (.inr x),by simp [seeds,h],mem_singleton_self x⟩

lemma support_reads (A : Stores S) (l B : ℕ) : support S l B (seeds S A) = A.dome (l*B) := by
  ext x
  rw [support, Stores.dome, halo_spec, ← place_reads S, mem_biUnion]
  constructor
  · rintro ⟨i,hi,h⟩
    obtain ⟨a,ha,hx⟩ := halo_spec.mp h
    exact ⟨a,mem_biUnion.mpr ⟨i,hi,ha⟩,hx⟩
  · rintro ⟨a,ha,hx⟩
    obtain ⟨i,hi,H⟩ := mem_biUnion.mp ha
    exact ⟨i,hi,halo_spec.mpr ⟨a,H,hx⟩⟩

lemma contains (i : Seed S) : anchor S i ∈ points S i := by
  rcases i with p|b|y
  · exact mem_image_of_mem _ (Work.E01.base_touched p)
  · exact mem_insert_self ..
  exact mem_singleton_self _

lemma price_one (i : Seed S) (x : Site c) (hx : x ∈ points S i) :
    separation (anchor S i) x ≤ 1 := by
  rcases i with p|b|y
  · obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    change separation (S.ratio.parent p.1) (S.ratio.parent y) ≤ 1
    have h : S.patch.L.val*separation (S.ratio.parent p.1) (S.ratio.parent y) ≤ 2+S.patch.L.val :=
      (Corona.foreshorten S.ratio p.1 y).trans (Nat.add_le_add_right (Work.E01.sep_touched p y hy) _)
    by_contra! he
    have hi := Nat.mul_le_mul_left S.patch.L.val he
    have hs := S.patch.coarse
    omega
  · change x ∈ insert _ {_} at hx; rcases mem_insert.mp hx with rfl|h
    · simp [anchor]
    rw [mem_singleton.mp h]; exact Work.E01.sep_step_le ..
  rw [mem_singleton.mp hx]; simp [anchor]

lemma contained (l B : ℕ) (i : Seed S) : anchor S i ∈ skin S l B i :=
  halo_subset _ _ (contains S i)

lemma price_skin (l B : ℕ) (i : Seed S) (x : Site c) (hx : x ∈ skin S l B i) :
    separation (anchor S i) x ≤ l*B+1 := by
  obtain ⟨y,hy,h⟩ := halo_spec.mp hx
  apply (separation_triangle _ y x).trans
  have hi := price_one S i y hy
  omega





lemma support_nonempty (l B : ℕ) (s : Finset (Seed S)) :
    (support S l B s).Nonempty ↔ s.Nonempty := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨i,hi,-⟩ := mem_biUnion.mp hv
    exact ⟨i,hi⟩
  rintro ⟨i,hi⟩
  exact ⟨anchor S i,mem_biUnion.mpr ⟨i,hi,contained S l B i⟩⟩

/-- Number of `B`-balls paying for the enlarged skin of one seed. This
pre-L constant includes `B=0`. -/
def seedCover (l : ℕ) := ballCost (l+1)

lemma cover_skin (l B : ℕ) (i : Seed S) : coverNumber B (skin S l B i) ≤ seedCover l := by
  have h : skin S l B i ⊆ neighbors (l*B+1) (anchor S i) := fun x hx =>
    (neighbors_mem ..).mpr (price_skin S l B i x hx)
  apply (Corona.cover_mono h B).trans
  by_cases hh : 0 < B
  · apply (Corona.cover_mono (D:=halo (l*B+1) {anchor S i})
      (halo_mono (show l*B+1 ≤ (l+1)*B by rw [Nat.add_mul,Nat.one_mul]; omega)
        (Finset.Subset.refl _)) B).trans (Corona.tile _ _ _ hh)
  interval_cases B
  let Y := neighbors 1 (anchor S i)
  simp only [Nat.mul_zero,Nat.zero_add]
  change coverNumber 0 Y ≤ _
  have he x (b : ℕ) : Ships ({x} : Support c) b := by
    intro a ha b hb; rw [mem_singleton.mp ha,mem_singleton.mp hb]
  calc
    _ ≤ Y.card := Corona.list_cost _ ⟨halo_subset 0 Y,
      ship_halo 0 (ship_halo 1 (he _ _))⟩
    _ ≤ ballCost 1 := neighbors_card ..
    _ ≤ _ := by unfold seedCover ballCost; gcongr <;> omega

lemma cover_support (l B : ℕ) (s : Finset (Seed S)) (h : Whole S l B s) :
    coverNumber B (support S l B s) ≤ s.card*seedCover l := by
  apply (Ac.cover (skin S l B) B h).trans
  calc
    _ ≤ ∑ _i ∈ s, seedCover l := sum_le_sum fun i _ => cover_skin S l B i
    _ = _ := by simp



/-- Fine positions and physical types retained in degeneracy bounds. -/
def typesAt (L : Side) := L.val ^ 4 * Fintype.card PlaqAxes + Fintype.card Axis + 1

lemma typesAt_ge (L : Side) : 1 ≤ typesAt L := by unfold typesAt; omega

def homes (Y : Support c) : Finset (Seed S) := univ.filter (fun i => anchor S i ∈ Y)

lemma homes_card (Y : Support c) : (homes S Y).card ≤ Y.card * typesAt S.patch.L := by
  let fine := ((Y ×ˢ (univ : Support S.ratio.count)).image S.ratio.assemble) ×ˢ
    (univ : Finset PlaqAxes)
  let noise := Y ×ˢ (univ : Finset Axis)
  have h : homes S Y ⊆ fine.disjSum (noise.disjSum Y) := by
    intro a h
    have hh := (mem_filter.mp h).2
    rcases a with p|b|x
    · refine inl_mem_disjSum.mpr (mem_product.mpr ⟨mem_image.mpr ?_,mem_univ _⟩)
      exact ⟨(S.ratio.parent p.1,S.ratio.residue p.1),mem_product.mpr ⟨hh,mem_univ _⟩,
        S.ratio.unpack_at p.1⟩
    · exact inr_mem_disjSum.mpr (inl_mem_disjSum.mpr (mem_product.mpr ⟨hh,mem_univ _⟩))
    exact inr_mem_disjSum.mpr (inr_mem_disjSum.mpr hh)
  have he : fine.card ≤ Y.card * S.ratio.count.val^4 * Fintype.card PlaqAxes := by
    rw [card_product, card_univ]
    apply Nat.mul_le_mul_right
    exact Finset.card_image_le.trans (by rw [card_product,card_univ,Lattice.site_card])
  apply (Finset.card_le_card h).trans
  rw [card_disjSum,card_disjSum, show noise.card = Y.card * Fintype.card Axis by rw [card_product,card_univ]]
  change fine.card + (_ + Y.card) ≤ _
  apply (Nat.add_le_add_right he _).trans_eq
  change Y.card * S.patch.L.val^4 * _ + (_+_) = _
  unfold typesAt; ring

def hitChoices (l B : ℕ) (x : Site c) := homes S (neighbors (l*B+1) x)
def neighborChoices (l B : ℕ) (i : Seed S) :=
  homes S (neighbors (2*(l*B+1)) (anchor S i))

def hitCost (L : Side) (l B : ℕ) := ballCost (l*B+1) * typesAt L
def stepCost (L : Side) (l B : ℕ) := ballCost (2*(l*B+1)) * typesAt L

lemma step_ge (L : Side) (l B : ℕ) : 1 ≤ stepCost L l B := by
  apply le_trans (by simp : 1 ≤ 1 * 1)
  exact Nat.mul_le_mul (neighbors_ge _) (typesAt_ge L)

lemma hit_card (l B : ℕ) (x : Site c) : (hitChoices S l B x).card ≤ hitCost S.patch.L l B :=
  (homes_card S _).trans (Nat.mul_le_mul_right _ (neighbors_card ..))
lemma step_card (l B : ℕ) (x : Seed S) : (neighborChoices S l B x).card ≤ stepCost S.patch.L l B :=
  (homes_card S _).trans (Nat.mul_le_mul_right _ (neighbors_card ..))

lemma hit_mem (l B : ℕ) (i : Seed S) (x : Site c) (hx : x ∈ skin S l B i) : i∈hitChoices S l B x :=
  mem_filter.mpr ⟨mem_univ _,(neighbors_mem ..).mpr ((separation_comm ..).trans_le
    (price_skin S l B i x hx))⟩

lemma reverse_mem (l B : ℕ) {a b : Seed S} (hb : b∈neighborChoices S l B a) :
    a∈neighborChoices S l B b := mem_filter.mpr ⟨mem_univ _,neighbors_back _ (mem_filter.mp hb).2⟩

lemma step_mem (l B : ℕ) (i j : Seed S) (h : Ac.meets (skin S l B) j (skin S l B i)) :
    j∈neighborChoices S l B i := by
  obtain ⟨x,h1,h2⟩ := h
  have hu := price_skin S l B i x h1; have hv := price_skin S l B j x h2
  refine mem_filter.mpr ⟨mem_univ _,(neighbors_mem ..).mpr ?_⟩
  apply (separation_triangle _ x _).trans; rw [separation_comm x]
  omega

lemma price_linked (l B : ℕ) (s : Finset (Seed S)) (hs : Whole S l B s) :
    Animals.Linked (neighborChoices S l B) s :=
  fun i hi j hj => ReflTransGen.mono (fun a b (h : Ac.bonds (skin S l B) s a b) =>
    ⟨h.1,h.2.1,step_mem S _ _ a b h.2.2⟩) _ _ (hs.2 i hi j hj)



lemma count (l B k : ℕ) (x : Site c) (s : Finset (Finset (Seed S)))
    (h : ∀ p∈s, p.card=k ∧ Whole S l B p ∧ x∈support S l B p) :
    s.card ≤ hitCost S.patch.L l B * (stepCost S.patch.L l B^2)^k := by
  have he := step_card S l B
  apply le_trans _ (Nat.mul_le_mul_right ((stepCost S.patch.L l B^2)^k) (hit_card S l B x))
  apply Animals.animals (neighborChoices S l B) (reverse_mem S l B) (step_ge ..) he s _ k
  intro p hp
  obtain ⟨he,hh,hp⟩ := h p hp
  obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hp
  exact ⟨he,price_linked S l B p hh,i,hi,hit_mem S l B i x hx⟩

lemma stores_count (l B k : ℕ) (x : Site c) (s : Finset (Stores S))
    (h : ∀ A∈s, A.shares=k ∧ connected S l B A ∧ x∈A.dome (l*B)) :
    s.card ≤ hitCost S.patch.L l B * (stepCost S.patch.L l B^2)^k := by
  calc
    _ = (s.image (seeds S)).card := (Finset.card_image_of_injective _
      (sectorAlphabet S).injective).symm
    _ ≤ _ := count S _ _ _ x _ fun p hp => by
      obtain ⟨A,hA,rfl⟩ := mem_image.mp hp
      obtain ⟨hi,hp,hx⟩ := h A hA
      exact ⟨(seeds_card S A).trans hi,hp,support_reads S A l B ▸ hx⟩
/-- Enumerate sectors by disjoint-support seed packets (allowing in
particular the empty set of packets). This is ONLY the seed records,
not a factorization of any sector integral. -/
def pieces (l B : ℕ) (A : Stores S) := Ac.Parts (skin S l B) (seeds S A)

lemma pieces_price (l B : ℕ) (A : Stores S) :
    (∀ s∈pieces S l B A, Whole S l B s) ∧
    ((pieces S l B A): Set (Finset (Seed S))).PairwiseDisjoint (support S l B) ∧
    (pieces S l B A).biUnion id = seeds S A ∧
    ∑ s∈ pieces S l B A, s.card = A.shares := by
  have hi := Ac.reconstruct (skin S l B) (seeds S A)
  refine ⟨fun s hs => (Ac.lives (skin S l B) _ hs).2, Ac.separate (skin S l B) _, hi,?_⟩
  rw [← seeds_card S]
  exact (Finset.card_biUnion (Ac.different (skin S l B) (seeds S A))).symm.trans
    (congr_arg Finset.card hi)



lemma pieces_of (l B : ℕ) (Q : Finset (Finset (Seed S))) (he : ∀ s∈Q, Whole S l B s)
    (hd : (Q:Set (Finset (Seed S))).PairwiseDisjoint (support S l B)) :
    pieces S l B (store S (Q.biUnion id))=Q := by
  rw [pieces,seeds_store]; exact Ac.separates (skin S l B) Q he hd

end YM.Push.AbsoluteSums.Packets
