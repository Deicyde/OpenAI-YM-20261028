import YM.Push.ABSOLUTE_SUMS.Breadth

/-!
# Overlap graph tree bound

Penrose-style interval here with a breadth-first parent .
Graphs read unordered pairs from a Finset. To pay the hard-core/log
multiplicity we need ABS OF THE ALTERNATING SUM, not open it in
absolute value. Vertices represent occurrence indices, not addresses
(two occurrences of the same address can be adjacent).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Graph
open Trees Relation Finset
open scoped Classical BigOperators

abbrev Network (α : Type*) := Finset (Finset α)

def link {α : Type*} [DecidableEq α] (g : Network α) (i j : α) := i≠j ∧ ({i,j} : Finset α)∈g
lemma backwards {α : Type*} [DecidableEq α] {g : Network α} {i j : α} (h : link g i j) : link g j i :=
    ⟨Ne.symm h.1, (Finset.pair_comm j i) ▸ h.2⟩

-- the coefficient is used at NONEMPTY α.
def reaches {α : Type*} [DecidableEq α] (g : Network α) : Prop := ∀ i j, ReflTransGen (link g) i j

def alternating {α : Type*} (g : Finset α) : ℝ := (-1)^g.card
def connectedGroups {α : Type*} [DecidableEq α] (S : Network α) := S.powerset.filter reaches
def mass {α : Type*} [DecidableEq α] (S : Network α) := ∑ g∈connectedGroups S, alternating g

lemma belongs {α : Type*} [DecidableEq α] {T G : Network α} : G∈connectedGroups T ↔ G ⊆ T ∧ reaches G := by
  simp [connectedGroups]

private lemma interval {α : Type*} (U L : Finset α) (S : Finset (Finset α)) (hl : L ⊆ U)
    (h : ∀ i, i∈S ↔ L⊆i ∧ i⊆U) : |∑ i∈S, alternating i| ≤ 1 := by
  by_cases he : L=U
  · have he' : S={U} := by ext a; rw [h,mem_singleton,Finset.Subset.antisymm_iff]; simp [he,and_comm]
    simp [he',alternating,abs_pow]
  have hh : ∃ i∈U,i∉L := by
    by_contra! H
    exact he (Finset.Subset.antisymm hl H)
  obtain ⟨i,hu,hL⟩ := hh
  let f (s : Finset α) := if i∈s then s.erase i else insert i s
  have hg s (hs : s∈S) : f s∈S := by
    obtain ⟨h1,h2⟩ := (h s).mp hs; rw [h]; unfold f; split
    next hi => exact ⟨fun a ha => mem_erase.mpr ⟨fun hz => hL (hz ▸ ha), h1 ha⟩,
      fun _ hh => h2 (mem_of_mem_erase hh)⟩
    next hi => exact ⟨fun a ha => mem_insert_of_mem (h1 ha),insert_subset hu h2⟩
  have hc s : f (f s)=s := by
    by_cases h : i∈s
    · simp [f,h]
    simp [f,h]
  have hn s : f s ≠ s := by
    by_cases he : i∈s
    · have he' : i∉f s := by simp [f,he]
      exact fun h => he' (h.symm ▸ he)
    have he' : i∈f s := by simp [f,he]
    exact fun h => he (h ▸ he')
  have he : ∑ i∈S, alternating i = 0 := Finset.sum_involution (fun a _ => f a)
    (fun a _ => by
      unfold alternating f; split
      next h => rw [← Finset.card_erase_add_one h,pow_succ]; ring
      next h => rw [Finset.card_insert_of_notMem h,pow_succ]; ring)
    (fun a _ _ => hn a) hg (fun a _ => hc a)
  rw [he,abs_zero]; norm_num

section Bound
variable {α : Type*} [DecidableEq α]
local notation "V" => Option α

lemma grown {p : α → V} {R : Network V} {f : V → ℕ} {d : V → ℕ} (h : Breadth.Built (link R) f p d) :
    reaches R := by
  intro i j
  have ht : ReflTransGen (link R) i none := by
    have he x y (h : ReflTransGen (link R) x y) : ReflTransGen (link R) y x := by
      induction h with
      | refl => exact .refl
      | tail _ hs IH => exact .head (backwards hs) IH
    exact he none i (Breadth.made h i)
  exact ht.trans (Breadth.made h j)

/-- Every possible breadth-first parent, forgetting the order test. -/
def sprouts (T : Network V) (p : α → V) := Ranked p ∧ ∀ i, link T (p i) (some i)

def stem [Fintype α] (p : α → V) : Network V := univ.image (fun i : α => ({p i, some i}:Finset V))

-- Rule permitted for adding an extra edge; use singleton graphs for clarity.
private def token [Fintype α] (T : Network V) (p : α → V) (d f : V → ℕ) : Network V := T.filter
    (fun e => (∀ i j, link {e} i j → d j ≤ d i+1) ∧
      (∀ i j, link {e} j (some i) → d j+1=d (some i) → f (p i) ≤ f j))

private lemma allowed_range [Fintype α] (T : Network V) (p : α → V)
    (d f : V → ℕ) (G : Network V) (h : Breadth.Built (link G) f p d) (hG : G ⊆ T) :
    stem p ⊆ G ∧ G ⊆ token T p d f := by
  refine ⟨fun i hi => ?_,fun e he => ?_⟩
  · obtain ⟨i,-,rfl⟩ := mem_image.mp hi
    exact (h.edges i).2
  have hi (i j : V) (h : link {e} i j) : link G i j :=
    ⟨h.1,(Finset.mem_singleton.mp h.2).symm ▸ he⟩
  exact mem_filter.mpr ⟨hG he,fun i j ht => h.paths _ _ (hi i j ht),fun i j ht =>
    h.least _ _ (hi j (some i) ht)⟩

private lemma ranges_allowed [Fintype α] (T : Network V) (p : α → V)
    (d f : V → ℕ) (G : Network V) (h : Breadth.Growth p d)
    (hl : stem p ⊆ G) (hu : G ⊆ token T p d f) : Breadth.Built (link G) f p d := by
  have hi i j (hb : link G i j) : link ({ {i,j}} : Network V) i j := ⟨hb.1,mem_singleton_self _⟩
  refine ⟨h,fun i => ?_,fun i j he => (mem_filter.mp (hu he.2)).2.1 _ _ (hi _ _ he),
    fun i j he => (mem_filter.mp (hu he.2)).2.2 i j (hi _ _ he)⟩
  exact ⟨fun eq => by have he := h.next i; rw [eq] at he; omega,
    hl (mem_image_of_mem _ (mem_univ _))⟩

/-- Absolute bound needed in the normalized tuple sum. -/
theorem pay [Fintype α] (T : Network V) :
    |mass T| ≤ ∑ p : α → V, if sprouts T p then (1:ℝ) else 0 := by
  let f := fun i : V => (Fintype.equivFin V i).val
  have hf : Function.Injective f := fun i j h => (Fintype.equivFin _).injective (Fin.ext h)
  let g := connectedGroups T
  have hw R (hr : R∈g) := Breadth.build (link R) f ((belongs.mp hr).2 none)
  let seed (R : Network V) := if h:R∈g then (hw R h).choose else fun _ : α => (none:V)
  have hs R (h : R∈g) : ∃ d, Breadth.Built (link R) f (seed R) d := by
    rw [show seed R = _ from dif_pos h]; exact (hw R h).choose_spec
  have he (p : α → V) :
      let a := g.filter (fun R => seed R=p)
      |∑ R∈a, alternating R| ≤ if sprouts T p then 1 else 0 := by
    intro a
    rcases a.eq_empty_or_nonempty with h|h
    · rw [h,sum_empty,abs_zero]; split <;> norm_num
    obtain ⟨R,hr⟩ := h
    obtain ⟨hr',hp⟩ := mem_filter.mp hr
    obtain ⟨d,hd⟩ := hs R hr'; rw [hp] at hd
    have hk := (belongs.mp hr').1
    have ha := allowed_range T p d f R hd hk
    rw [if_pos (show sprouts T p from ⟨Breadth.growth_ranked hd.toGrowth,
      fun i => ⟨(hd.edges i).1,hk (hd.edges i).2⟩⟩)]
    refine interval (token T p d f) (stem p) a (Subset.trans ha.1 ha.2) ?_
    intro x; rw [mem_filter]; constructor
    · rintro ⟨h,hx⟩
      obtain ⟨t,ht⟩ := hs x h; rw [hx] at ht
      rw [Breadth.unique_growth hd.toGrowth ht.toGrowth] at ht
      exact allowed_range _ _ _ _ x ht (belongs.mp h).1
    rintro ⟨hl,hu⟩
    have ht := ranges_allowed T p d f x hd.toGrowth hl hu
    have hx : x∈g := belongs.mpr ⟨Subset.trans hu (filter_subset ..),grown ht⟩
    obtain ⟨y,hy⟩ := hs x hx
    exact ⟨hx, Breadth.unique f hf hy ht⟩
  change |∑ R∈g, alternating R| ≤ _
  rw [← Finset.sum_fiberwise g seed alternating]
  exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => he i)
end Bound
end YM.Push.AbsoluteSums.Graph
