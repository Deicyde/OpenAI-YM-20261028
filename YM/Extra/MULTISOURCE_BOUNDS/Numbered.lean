import Mathlib.Combinatorics.SimpleGraph.Acyclic
import YM.Extra.MULTISOURCE_BOUNDS.Root

/-!
# Counting repeated choices on a numbered rooted tree

Two estimates: sum of products of
child kernels by peeling in decreasing depth; and daughter-factorial
budget over parent maps.

We allow an exponential 4^(n-1) in the latter (paid
by **per-vertex** smallness), avoiding a tree enumeration formula.

Even ALL
functions from the n-1 daughters to n numbered vertices can be afforded:
for a fixed outdegree multiset of values (parent names with repetition),
assign distinct numbers in each fibre; at most (n-1)! possibilities after
multiplying by all the daughter factorials.

This is not dividing a marker's
claim count by n!: factorials for repeated log terms must be actually supplied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.Numbered
open Function Finset
open scoped BigOperators Classical

section Count
variable {α β V : Type*} [Fintype α] [Fintype β]

def bag (f : α → β) := univ.val.map f

def numbers (f : α → β) : Sym β (Fintype.card α) := ⟨bag f, Multiset.card_map ..⟩

private abbrev copies (m : Sym β (Fintype.card α)) := {f : α → β // numbers f = m}
private def inventory (m : Sym β (Fintype.card α)) (b : β) := m.val.count b
private abbrev ways (m : Sym β (Fintype.card α)) (f : copies m) := ∀ b, {i // f.val i = b} ≃ Fin (inventory m b)

private def record {m : Sym β (Fintype.card α)} (x : Σ f : copies m,ways m f) :
    α ≃ Σ b, Fin (inventory m b) := (Equiv.sigmaFiberEquiv x.1.val).symm.trans (Equiv.sigmaCongrRight x.2)

omit [Fintype β] in
private theorem injects {m : Sym β (Fintype.card α)} : Injective (record (m:=m)) := by
  rintro ⟨f,X⟩ ⟨g,Y⟩ h; replace h := DFunLike.congr_fun h
  have hf : f=g := Subtype.ext (funext fun i => congr_arg Sigma.fst (h i))
  subst g; congr 1; funext b; ext ⟨i,hi⟩; subst b
  have := eq_of_heq (Sigma.mk.inj (h i)).2; exact congr_arg Fin.val this

omit [Fintype β] in
private theorem card_inventory {m : Sym β (Fintype.card α)} (f : copies m) (i : β) :
    Fintype.card {x // f.val x=i} = inventory m i := by
  classical
  conv_rhs => rw [← f.property,inventory,numbers]; dsimp [bag]
  rw [Fintype.card_subtype, Multiset.count_map]; change _ = ({x | i=f.val x} : Finset α).card
  simp_rw [@eq_comm β i]

variable {γ : Type*}
private def decode {m : Multiset β} (e : α ≃ m) (b : β) : {x : α // ((e x: m) : β)=b} ≃ Fin (m.count b) := {
  toFun x := Fin.cast (congr_arg (fun z => m.count z) x.property) (e x.val).2
  invFun i := ⟨e.symm ⟨b,i⟩, show ((e (e.symm (⟨b,i⟩:m)):m):β) = b by rw [e.apply_symm_apply]⟩
  left_inv x := Subtype.ext (e.symm_apply_eq.mpr (Sigma.ext x.property.symm (Fin.heq_ext_iff (by rw [x.property]) |>.mpr rfl)))
  right_inv i := by
    ext
    change (e (e.symm (⟨b,i⟩:m))).2.val=i.val; rw [e.apply_symm_apply] }

omit [Fintype β] in
private theorem bag_record (m : Multiset β) (e : α ≃ m) : bag (fun x => (e x).1) = m := by
  have h := congr_arg (fun t : Finset m => t.val.map (fun i : m => i.1)) (map_univ_equiv e)
  exact ((Multiset.map_map ..).symm.trans h).trans (Multiset.map_univ_coe m)

omit [Fintype β] in
private theorem surjects {m : Sym β (Fintype.card α)} : Surjective (record (m:=m)) := by
  intro e
  let e : α ≃ m.val := e
  let f : copies m := ⟨fun x => (e x).1, Subtype.ext (bag_record m.val e)⟩
  let g : ways m f := fun b => decode e b
  exact ⟨⟨f,g⟩,Equiv.ext (fun i => by change (⟨(e i).1,Fin.cast rfl (e i).2⟩:m.val) = e i; simp)⟩

def divisor (m : Multiset γ) : ℕ := ∏ i∈m.toFinset, (m.count i).factorial

theorem divisor_pos (m : Multiset γ) : 0 < (divisor m:ℝ) := Nat.cast_pos.mpr (prod_pos fun _ _ => Nat.factorial_pos _)

theorem pack_count (m : Sym β (Fintype.card α)) : Fintype.card {f : α → β // numbers f = m} * divisor m.val =
    (Fintype.card α).factorial := by
  have he := Fintype.card_of_bijective ⟨injects,surjects (m:=m)⟩
  let e : α ≃ m.val := Fintype.equivOfCardEq ((Multiset.card_coe _).trans m.property).symm
  rw [Fintype.card_sigma, Fintype.card_equiv (show α ≃ Σ b,Fin (inventory m b) from e)] at he
  refine Eq.trans ?_ he
  rw [show Fintype.card {f : α → β // numbers f = m} * divisor m.val = ∑ _ : copies m,divisor m.val by simp]
  refine sum_congr rfl fun x _ => ?_
  rw [divisor, prod_subset (subset_univ _) fun i _ hi => by
    rw [Multiset.count_eq_zero_of_notMem (fun h => hi (Multiset.mem_toFinset.mpr h))]; rfl]
  unfold ways; rw [Fintype.card_pi]
  refine prod_congr rfl fun i _ => Eq.symm ?_
  rw [Fintype.card_equiv (Fintype.equivFinOfCardEq (card_inventory x i)),card_inventory x i]; rfl

lemma load_le {m : Sym β (Fintype.card α)} :
    ∑ f : {f : α → β // numbers f = m}, ∏ b, (Fintype.card {x // f.val x=b}).factorial ≤ (Fintype.card α).factorial := by
  classical
  rcases isEmpty_or_nonempty (Σ f : copies m,ways m f) with hem|⟨x⟩
  · have hW : IsEmpty (copies m) := ⟨fun f => hem.false ⟨f,fun b => Fintype.equivFinOfCardEq (card_inventory f b)⟩⟩
    change ∑ f : copies m, _ ≤ _; rw [Fintype.sum_empty]; exact Nat.zero_le _
  have he := Fintype.card_le_of_injective (record (m:=m)) injects
  rw [Fintype.card_sigma,Fintype.card_equiv (record (Classical.choice x))] at he
  apply le_trans (le_of_eq ?_) he; apply sum_congr rfl; intro f _
  unfold ways; rw [Fintype.card_pi]; apply prod_congr rfl; intro b _
  rw [Fintype.card_equiv (Fintype.equivFinOfCardEq (card_inventory f b))]

theorem functions_le (hα : Fintype.card β = Fintype.card α + 1) :
    ∑ f : α → β, ∏ b, ((Fintype.card {x // f x=b}).factorial:ℝ) ≤ (4:ℝ)^Fintype.card α * (Fintype.card α).factorial := by
  classical
  let n := Fintype.card α
  have he : Fintype.card (Sym β n) ≤ 4^n := by
    rw [Sym.card_sym_eq_choose,hα,show Fintype.card α+1+n-1=n*2 by omega, mul_comm n]
    simpa only [pow_mul,show 2^2=(4:ℕ) by decide] using Nat.choose_le_two_pow (2*n) n
  exact_mod_cast (show ∑ f : α→β, ∏ b, (Fintype.card {x // f x=b}).factorial ≤ 4^n * n.factorial by
    rw [← Fintype.sum_fiberwise (numbers (α:=α) (β:=β))]; exact (sum_le_sum (fun b _ => load_le (m:=b))).trans <|
      by simpa using Nat.mul_le_mul_right (Nat.factorial n) he)

variable [Fintype V] (r : V)

def nonroot := univ.erase r

def daughters (p : V→V) (j : V) := ((nonroot r).filter fun i => p i=j).card

theorem nonroot_card : (nonroot r).card + 1 = Fintype.card V := card_erase_add_one (mem_univ _)

theorem allotted :
    (∑ p ∈ (univ.filter fun p : V→V => p r=r), ∏ j, ((daughters r p j).factorial:ℝ)) ≤
      (4:ℝ)^(nonroot r).card * (nonroot r).card.factorial := by
  classical
  let f (p : V→V) (x : nonroot r) := p x.val
  let W (p : ↥(nonroot r) → V) := ∏ j : V, ((Fintype.card {x // p x=j}).factorial : ℝ)
  let S := univ.filter (fun p : V→V => p r=r)
  have hi : Set.InjOn f (↑S) := by
    intro a ha b hb h; funext j
    by_cases hj : j=r
    · subst j; exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
    exact congr_fun h ⟨j,mem_erase.mpr ⟨hj,mem_univ _⟩⟩
  calc
    _ = ∑ p∈S, W (f p) := by
      refine sum_congr rfl fun p _ => prod_congr rfl fun j _ => ?_
      congr 2
      let e : ↥((nonroot r).filter fun i => p i = j) ≃ {x // f p x=j} := {
        toFun := fun x => ⟨⟨x.val,(mem_filter.mp x.property).1⟩,(mem_filter.mp x.property).2⟩
        invFun := fun x => ⟨x.val.val,mem_filter.mpr ⟨x.val.property,x.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      unfold daughters; rw [← Fintype.card_coe, Fintype.card_congr e]
    _ ≤ ∑ p,W p := by
      rw [← sum_image hi]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => prod_nonneg fun _ _ => Nat.cast_nonneg _)
    _ ≤ _ := by
      have he := functions_le (α:=↥(nonroot r)) (β:=V) (by rw [Fintype.card_coe,nonroot_card])
      rw [Fintype.card_coe] at he; convert! he using 2; ext; simp

end Count

section Peel
variable {V α : Type*} [DecidableEq V] [Fintype V] [Fintype α]

lemma sum_update (i : V) (g : (V → α) → ℝ) : ∑ v, ∑ a : α, g (Function.update v i a) = (Fintype.card α:ℝ)*∑ v, g v := by
  let E := Equiv.piSplitAt i fun _ : V => α
  have he (b : α × ({j // j ≠ i} → α)) (a : α) : Function.update (E.symm b) i a = E.symm (a,b.2) := by
    funext x; by_cases h : x=i
    · subst x; simp [E,Equiv.piSplitAt_symm_apply]
    rw [Function.update_of_ne h]; simp [E,Equiv.piSplitAt_symm_apply,h]
  rw [← Equiv.sum_comp E.symm (fun v => ∑ a, g (Function.update v i a)), ← Equiv.sum_comp E.symm g,
    Fintype.sum_prod_type,Fintype.sum_prod_type]; simp_rw [he]; rw [sum_const,card_univ,nsmul_eq_mul]; congr 1; rw [sum_comm]

lemma sum_root (G : α → ℝ) (r : V) : ∑ v : V → α, G (v r) = (Fintype.card α:ℝ)^(nonroot r).card * ∑ a,G a := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt r (fun _ => α)).symm, Fintype.sum_prod_type]; simp only [Equiv.piSplitAt_symm_apply,
    dite_true]
  have h : Fintype.card {x // x ≠ r} = (nonroot r).card := by rw [Fintype.card_subtype]; congr 1; ext; simp [nonroot]
  simp [h,mul_sum]

/-- Peel deepest daughter of the set (can even price a subset of the parent
edges). Root separately specified and kept to the end. No independence
between different physical integrations claimed: apply to the NUMERICAL
bound, not to probabilities in a sector. -/
private theorem cascade_rec (r : V) (p : V → V) (t : V → ℕ) (s : Finset V) (ht : ∀ i∈s,t (p i)<t i)
    (hr : r∉s) (F : α → ℝ) (K : α → α → ℝ) (Z : ℝ) (hf : ∀ i,0 ≤ F i)
    (hk : ∀ i j,0 ≤ K i j) (hZ : ∀ i, ∑ j, K i j ≤ Z) :
    (Fintype.card α:ℝ)^s.card * ∑ u : V→α,F (u r)*∏ i∈s,K (u (p i)) (u i) ≤ Z^s.card * ∑ u : V→α,F (u r) := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image s t hs
  let H (S : Finset V) (u : V→α) := F (u r)*∏ i∈S,K (u (p i)) (u i)
  have hH u : 0 ≤ H (s.erase i) u := mul_nonneg (hf _) (prod_nonneg fun _ _ => hk ..)
  have he u a : H s (Function.update u i a) = H (s.erase i) u * K (u (p i)) a := by
    have hr' : r≠i := fun h => hr (h ▸ hi)
    have hpi : p i≠i := ne_of_apply_ne _ (ht i hi).ne
    unfold H; rw [← prod_erase_mul s _ hi,Function.update_self,update_of_ne hr',update_of_ne hpi,← mul_assoc]; congr 2
    exact prod_congr rfl fun j hj => by
      obtain ⟨hj,hs⟩ := mem_erase.mp hj
      rw [update_of_ne hj,update_of_ne (ne_of_apply_ne t (((ht j hs).trans_le (hmax j hs)).ne))]
  have ht : (Fintype.card α:ℝ)*∑ u,H s u ≤ Z*∑ u,H (s.erase i) u := by
    rw [← sum_update i,mul_sum]; apply sum_le_sum; intro u _; simp_rw [he, ← mul_sum];
    rw [mul_comm Z]; exact mul_le_mul_of_nonneg_left (hZ _) (hH _)
  rcases isEmpty_or_nonempty α with hm|hm
  · haveI : IsEmpty (V→α) := ⟨fun v => hm.false (v r)⟩; simp
  have hz := (sum_nonneg fun j (_:j∈univ) => hk (Classical.choice hm) j).trans (hZ _)
  rw [← card_erase_add_one hi,pow_succ,pow_succ,mul_assoc,mul_right_comm _ Z]
  apply (mul_le_mul_of_nonneg_left ht (by positivity : 0≤ (Fintype.card α:ℝ)^(s.erase i).card)).trans
  rw [mul_left_comm,mul_comm _ Z]; exact mul_le_mul_of_nonneg_left (ih _ (erase_ssubset hi) (fun i hi => ‹∀ i∈s,t (p i)<t i› i (mem_of_mem_erase hi))
    (fun h => hr (mem_of_mem_erase h))) hz

theorem cascade (r : V) (p : V → V) (t : V → ℕ) (ht : ∀ i≠r,t (p i)<t i)
    (F : α → ℝ) (K : α → α → ℝ) (Z : ℝ) (hf : ∀ i,0 ≤ F i)
    (hk : ∀ i j,0 ≤ K i j) (hZ : ∀ i, ∑ j,K i j ≤ Z) :
    ∑ u : V→α,F (u r)*∏ i∈nonroot r,K (u (p i)) (u i) ≤ Z^(nonroot r).card * ∑ a, F a := by
  rcases isEmpty_or_nonempty α with hm|hm
  · haveI : IsEmpty (V→α) := ⟨fun v => hm.false (v r)⟩; simp
  have H := cascade_rec r p t (nonroot r) (fun i hi => ht i ((by simpa [nonroot] using hi) : i≠r)) (by simp [nonroot]) F K Z hf hk hZ
  refine le_of_mul_le_mul_left (a:=(Fintype.card α:ℝ)^(nonroot r).card) ?_ (by have hx := Fintype.card_pos (α:=α); positivity)
  rwa [sum_root,mul_left_comm] at H

end Peel
end YM.Extra.Multi.Numbered
