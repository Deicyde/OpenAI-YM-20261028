import YM.Push.ABSOLUTE_SUMS.Parent

/-!
# Breadth-first parent for a rooted enumeration

Needed twice: choosing a parent map (not spending multiple copies
of an address), and opening the hard overlap Ursell multiplicity
with an interval argument. No hidden graph/degree restrictions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees.Breadth
open Relation
open scoped Classical

variable {α : Type*}
local notation "V" => Option α

-- oriented from root outwards.
private def Found (R : V → V → Prop) (x : V) : ℕ → Prop
  | 0 => x=none
  | m+1 => ∃ i, R i x ∧ Found R i m

private lemma walks (R : V → V → Prop) (x : V) (h : ReflTransGen R none x) : ∃ k, Found R x k := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @tail a b _ hc IH =>
    obtain ⟨k,h⟩ := IH
    exact ⟨k+1,a,hc,h⟩

structure Growth (p : α → V) (d : V → ℕ) : Prop where
  seed : d none=0
  next : ∀ i, d (some i) = d (p i)+1

structure Built (R : V → V → Prop) (code : V → ℕ) (p : α → V) (d : V → ℕ) : Prop
    extends Growth p d where
  edges : ∀ i, R (p i) (some i)
  paths : ∀ i j, R i j → d j ≤ d i+1
  least : ∀ i j, R j (some i) → d j+1=d (some i) → code (p i) ≤ code j

lemma growth_ranked {p : α → V} {d : V → ℕ} (h : Growth p d) : Ranked p :=
    ⟨fun i => d (some i), fun i j he => by simpa only [h.next i,he] using
      (show d (some j) < d (some j)+1 by omega)⟩

lemma unique_growth {p : α → V} {d t : V → ℕ} (h : Growth p d) (ht : Growth p t) : t=d := by
  have he : ∀ k : ℕ, ∀ j, d j ≤ k → t j=d j := by
    intro k; induction k with
    | zero =>
      intro i hi; cases i with
      | none => rw [h.seed,ht.seed]
      | some i => have he := h.next i; omega
    | succ k IH =>
      intro i hi; cases i with
      | none => rw [h.seed,ht.seed]
      | some i => rw [h.next,ht.next,IH _ (by have he := h.next i; omega)]
  exact funext fun i => he _ _ le_rfl

lemma made {R : V → V → Prop} {f : V → ℕ} {p : α → V} {d : V → ℕ} (h : Built R f p d) :
    ∀ i, ReflTransGen R none i := by
  have he : ∀ k : ℕ, ∀ i, d i ≤ k → ReflTransGen R none i := by
    intro k; induction k with
    | zero =>
      intro i hi; cases i with
      | none => exact .refl
      | some i => have he := h.next i; omega
    | succ k IH =>
      intro i hi; cases i with
      | none => exact .refl
      | some i => exact .tail (IH (p i) (by have he := h.next i; omega)) (h.edges i)
  exact fun i => he _ _ le_rfl

lemma unique {R : V → V → Prop} (f : V → ℕ) (hf : Function.Injective f) {p q : α → V}
    {d t : V → ℕ} (hp : Built R f p d) (hq : Built R f q t) : p=q := by
  have he {p q : α → V} {d t} (hp : Built R f p d) (hq : Built R f q t) : t ≤ d := by
    have he : ∀ k : ℕ, ∀ i, d i ≤ k → t i ≤ d i := by
      intro k; induction k with
      | zero =>
        intro i hi; cases i with
        | none => rw [hp.seed,hq.seed]
        | some i => have he := hp.next i; omega
      | succ k IH =>
        intro i hi; cases i with
        | none => rw [hp.seed,hq.seed]
        | some i =>
          have hl := hp.next i
          have he := IH (p i) (by omega)
          have hk := hq.paths _ _ (hp.edges i)
          omega
    exact fun i => he _ _ le_rfl
  obtain rfl := le_antisymm (he hp hq) (he hq hp)
  exact funext fun i => hf (le_antisymm
    (hp.least _ _ (hq.edges i) (hq.next i).symm) (hq.least _ _ (hp.edges i) (hp.next i).symm))

lemma build (R : V → V → Prop) (f : V → ℕ) (h : ∀ i, ReflTransGen R none i) :
    ∃ (p : α → V) (d : V → ℕ), Built R f p d := by
  have hw i := walks R i (h i)
  let d := fun i => Nat.find (hw i)
  have he (i) : Found R i (d i) := Nat.find_spec (hw i)
  have hd (i) (k) (ha : Found R i k) : d i ≤ k := Nat.find_min' _ ha
  have hr i j (h : R i j) : d j ≤ d i+1 := hd j (d i+1) ⟨_,h,he i⟩
  have hi (i : α) : ∃ k, ∃ x, R x (some i) ∧ d (some i)=d x+1 ∧ f x=k := by
    have hs := he (some i)
    cases hh : d (some i) with
    | zero => rw [hh] at hs; contradiction
    | succ k =>
      rw [hh] at hs
      obtain ⟨x,hx,H⟩ := hs
      have hm := hd x k H
      have hg := hr x (some i) hx
      exact ⟨f x,x,hx,by omega,rfl⟩
  choose p hp hp' hy using fun i => Nat.find_spec (hi i)
  exact ⟨p,d,⟨⟨Nat.eq_zero_of_le_zero (hd none 0 rfl),hp'⟩,hp,hr,by
    intro i j he hd
    rw [hy]
    exact Nat.find_min' _ ⟨j,he,hd.symm,rfl⟩⟩⟩
end YM.Push.AbsoluteSums.Trees.Breadth
