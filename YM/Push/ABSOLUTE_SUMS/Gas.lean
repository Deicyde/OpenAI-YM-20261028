import YM.Push.ABSOLUTE_SUMS.Coef

/-! # Hard-core compatible gas, factorials in finite populations -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Gas
open Coef Partition Relation Graph Ursell Finset
open scoped BigOperators Classical
variable {ι α : Type*} (R : ι → ι → Prop) (w : ι → ℝ)

def separated (s : Finset ι) : Prop := ∀ i∈s,∀ j∈s,i≠j → ¬ R i j

def value (s : Finset ι) : ℝ := if separated R s then ∏ i∈s,w i else 0

-- guards
structure Hard : Prop where
  diag : ∀ i, R i i
  symm : ∀ i j, R i j → R j i

def good (z : α → ι) : Prop := ∀ i j, i≠j → ¬ R (z i) (z j)

lemma void_iff [Fintype α] (z : α → ι) (hr : Hard R) : pot R z=∅ ↔ good R z := by
  constructor
  · intro h i j hh H
    have he : ({i,j}:Finset α)∈pot R z := by
      rw [potential_mem]; refine ⟨Finset.card_pair hh,?_⟩
      intro a ha b hb hn
      simp only [mem_insert,mem_singleton] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | contradiction | exact H | exact hr.symm _ _ H
    rw [h] at he; simp at he
  intro h; apply Finset.eq_empty_iff_forall_notMem.mpr fun i hi => ?_
  obtain ⟨he,hp⟩ := (potential_mem ..).mp hi
  obtain ⟨x,y,hxy,H⟩ := Finset.card_eq_two.mp he
  rw [H] at hp; exact h x y hxy (hp x (by simp) y (by simp) hxy)

lemma injective_good (z : α → ι) (hr : Hard R) (h : good R z) : Function.Injective z := by
  intro i j he; by_contra hh; exact h _ _ hh (by rw [he]; exact hr.diag _)

section Finitely
variable [Fintype ι]

def polyAt (t : ℝ) := ∑ s, t^s.card * value R w s

private abbrev Range (α ι : Type*) := Σ s : Finset ι, α ≃ ↥s
private def choice (z : Range α ι) : α → ι := fun i => (z.2 i).val

omit [Fintype ι] in
private lemma picked (s : Finset ι) (e : α ≃ ↥s) : good R (choice ⟨s,e⟩) ↔ separated R s := by
  have hb i j (h : choice ⟨s,e⟩ i=choice ⟨s,e⟩ j) : i=j := e.injective (Subtype.ext h)
  constructor
  · intro h i hi j hj he hr
    obtain ⟨x,hx⟩ := e.surjective ⟨i,hi⟩; obtain ⟨y,hy⟩ := e.surjective ⟨j,hj⟩
    apply h x y
    · rintro rfl; rw [hx] at hy; exact he (congr_arg Subtype.val hy)
    unfold choice; dsimp only; rw [hx,hy]; exact hr
  intro h i j he
  exact h _ (e i).property _ (e j).property (fun hz => he (hb i j hz))

omit [Fintype ι] in
private lemma basis (n : ℕ) (z : Fin n → ι) (hz : Function.Injective z) :
    ∃ s : Finset ι, ∃ e : Fin n ≃ ↥s, choice ⟨s,e⟩=z := by
  let s := univ.image z
  let i : Fin n → ↥s := fun j => ⟨_, Finset.mem_image_of_mem z (mem_univ j)⟩
  have he : Function.Bijective i := by
    refine ⟨fun a b h => hz (congr_arg Subtype.val h),fun a => ?_⟩
    obtain ⟨b,hb⟩ := a; obtain ⟨k,_,rfl⟩ := mem_image.mp hb; exact ⟨k,rfl⟩
  exact ⟨s,Equiv.ofBijective i he, rfl⟩

lemma row (n : ℕ) (hr : Hard R) : gasRow R w n =
    ∑ s ∈ univ.powersetCard n,value R w s := by
  unfold gasRow; have hn : (n.factorial:ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hn]
  let s := (univ : Finset ι).powersetCard n
  let u := s.filter (separated R)
  let f := fun s : Finset ι => ∏ i∈s,w i
  let U : Finset (Range (Fin n) ι) := u.sigma fun _ => univ
  let V := univ.filter (good R (α:= Fin n))
  let g := fun z : Fin n → ι => ∏ i,w (z i)
  have h i (hi : i∈U) : choice i ∈ V := by
    have he := (mem_filter.mp (mem_sigma.mp hi).1).2
    exact mem_filter.mpr ⟨mem_univ _,(picked R i.1 i.2).mpr he⟩
  have hx : Function.Injective (@choice ι (Fin n)) := by
    have hh (i : Range (Fin n) ι) : univ.image (choice i)=i.1 := by
      ext a; constructor
      · intro h; obtain ⟨k,hk,rfl⟩ := mem_image.mp h; exact (i.2 k).property
      intro h; obtain ⟨k,hk⟩ := i.2.surjective ⟨a,h⟩
      exact mem_image.mpr ⟨k,mem_univ _,congr_arg Subtype.val hk⟩
    rintro ⟨a,b⟩ ⟨c,d⟩ e
    have ha : a=c := by rw [← (show _ = a from hh ⟨a,b⟩),← (show _ = c from hh ⟨c,d⟩),e]
    subst c
    congr; exact Equiv.ext fun x => Subtype.ext (congr_fun e x)
  have hb i (hi : i∈V) : ∃ j, ∃ (_:j∈U), choice j=i := by
    have he := (mem_filter.mp hi).2
    obtain ⟨s,e,h⟩ := basis n i (injective_good R i hr he)
    refine ⟨⟨s,e⟩,mem_sigma.mpr ⟨mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨subset_univ _,?_⟩,(picked R s e).mp (h.symm ▸ he)⟩,mem_univ _⟩,h⟩
    simpa using Fintype.card_congr e.symm
  have he : (∑ i∈s,value R w i) = ∑ i∈u, f i := (sum_filter _ _).symm
  rw [he]
  calc
    all R w (Fin n) = ∑ z∈V,g z := by
      unfold all; rw [sum_filter]; apply sum_congr rfl; intro z _
      -- insert the hard-core guard including duplicates
      classical
      rw [Partition.allMass_eq]
      by_cases he : good R z
      · rw [if_pos ((void_iff R z hr).mpr he), one_mul,if_pos he]
      rw [if_neg (fun h => he ((void_iff R z hr).mp h)),zero_mul, if_neg he]
    _ = ∑ i∈U, f i.1 := by
      symm; apply Finset.sum_bij (fun a _ => choice a) h (fun i hi j hj hh => hx hh) hb
      intro i hi; unfold f g
      rw [prod_subtype i.1 (p:=(·∈i.1)) (fun _ => Iff.rfl)]
      exact (Fintype.prod_equiv i.2 _ _ fun k => rfl).symm
    _ = _ := by
      rw [sum_sigma,sum_mul]; apply sum_congr rfl; intro i hi
      have h : i.card=n := (mem_powersetCard.mp (mem_filter.mp hi).1).2
      change ∑ _z : (Fin n ≃ ↥i),f i = f i * ↑n.factorial
      rw [sum_const,card_univ, Fintype.card_equiv (Fintype.equivOfCardEq
        (show Fintype.card (Fin n) = Fintype.card ↥i by simp [h])),Fintype.card_fin]
      simp only [nsmul_eq_mul, mul_comm]

lemma rows_above (hr : Hard R) (m : ℕ) (h : Fintype.card ι < m) : gasRow R w m = 0 := by
  rw [row R w m hr]
  have he : ((univ : Finset ι).powersetCard m)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => by
    obtain ⟨h1,h2⟩ := mem_powersetCard.mp hi; have he := i.card_le_univ; omega)
  rw [he,sum_empty]

lemma sums (t : ℝ) (hr : Hard R) :
    ∑ i ∈ range (Fintype.card ι+1), gasRow R w i * t^i = polyAt R w t := by
  unfold polyAt
  have hh (s : Finset ι) (hs : s∈(univ:Finset (Finset ι))) : s.card ∈ range (Fintype.card ι+1) :=
    mem_range.mpr (Nat.lt_add_one_of_le s.card_le_univ)
  rw [← sum_fiberwise_of_maps_to hh]
  apply sum_congr rfl; intro i hi
  rw [row R w i hr,sum_mul,Finset.powersetCard_eq_filter]
  apply sum_congr (by simp)
  intro j hj; rw [(mem_filter.mp hj).2,mul_comm]
end Finitely
end YM.Push.AbsoluteSums.Gas
