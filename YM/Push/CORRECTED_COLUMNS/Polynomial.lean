import YM.Overlay.Terminal

/-!
# Full subset algebra (uses `Marker`; NOT quotienting by repetitions of a field at different sites)

Cumulant and correction are at *slots*, on top of vacuum, to be
applied to every copy in the tiling. Uses the exact square-zero
exponential. We give pass formulas through singleton and pair for tests.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Marks
open Marker
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {V : Type*} [DecidableEq V] [Fintype V]

abbrev all (V : Type*) [DecidableEq V] [Fintype V] := Stock.census V
abbrev Algebra (V : Type*) [DecidableEq V] [Fintype V] := Marker.Poly (all V)
abbrev mode (p : Finset V) : (all V).Mode := ⟨p,Finset.mem_univ _⟩
abbrev part (F : Algebra V) (p : Finset V) := F.part (mode p)
lemma mode_inj {p q : Finset V} : mode p = mode q ↔ p=q := Subtype.ext_iff
lemma mode_empty : mode ∅=(all V).quiet := rfl


/-- No exponential l₁ losses hidden in this convolution. -/
lemma convolution (F H : Algebra V) (p : Finset V) :
    part (F*H) p = ∑ i∈p.powerset, part F i*part H (p \ i) := by
  let e : Finset V ≃ (all V).Mode := { toFun i := mode i, invFun := fun x => x.val,
                                        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have fig (x y : Finset V) : Poly.merges (mode x) (mode y) (mode p) ↔ x ⊆ p ∧ y=p \ x := by
    change Disjoint x y ∧ x∪y=p ↔ _
    constructor
    · rintro ⟨hd,rfl⟩; exact ⟨Finset.subset_union_left, (Finset.union_sdiff_cancel_left hd).symm⟩
    rintro ⟨h,rfl⟩; exact ⟨Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h⟩
  have hg i : (∑ y, if Poly.merges (mode i) y (mode p) then F.part (mode i)*H.part y else 0) =
      if i∈p.powerset then F.part (mode i)*part H (p \ i) else 0 := by
    by_cases h : i∈p.powerset
    · have hh := Finset.mem_powerset.mp h
      rw [if_pos h, Finset.sum_eq_single (mode (p \ i))]
      · rw [if_pos ((fig _ _).2 ⟨hh,rfl⟩)]
      · intro b _ hb
        rcases b with ⟨b,hb'⟩
        exact if_neg (fun he => hb (mode_inj.mpr ((fig i b).mp he).2))
      simp
    rw [if_neg h]
    apply Finset.sum_eq_zero
    rintro ⟨x,hx⟩ hx'
    exact if_neg fun he => h (Finset.mem_powerset.mpr ((fig i x).mp he).1)
  unfold part
  rw [Poly.part_mul, ← Equiv.sum_comp e (fun i => ∑ j, if Poly.merges i j (mode p) then _ else _)]
  change (∑ i, ∑ j, if Poly.merges (mode i) j (mode p) then F.part (mode i) * H.part j else 0) = _
  simp_rw [hg]
  rw [← Finset.sum_filter]; congr 1; ext x; simp

omit [Fintype V] in
private lemma tiny (i : V) : ({i}:Finset V).powerset={∅,{i}} := by
  rw [← Finset.insert_empty, Finset.powerset_insert]; simp
lemma mult_single (F H : Algebra V) (i : V) :
    part (F*H) {i} = part F ∅*part H {i} + part F {i} * part H ∅ := by
  rw [convolution]; simp [tiny]
lemma mult_pair (F H : Algebra V) (i j : V) (h : i ≠ j) :
    part (F*H) {i,j} = part F ∅*part H {i,j} + part F {i} * part H {j}
      + part F {j}*part H {i} + part F {i,j} * part H ∅ := by
  rw [convolution, Finset.sum_powerset_insert (by simpa)]
  have he : ({i,j} : Finset V) \ {j} = {i} := by ext; simp; grind
  have ht : ({i,j} : Finset V) \ {i} = {j} := by ext; simp; grind
  simp only [tiny,Finset.sum_pair (show (∅:Finset V)≠{j} by simp),Finset.insert_empty,he,ht,Finset.sdiff_empty,Finset.sdiff_self]; abel

lemma expo_price (L : Algebra V) (p : Finset V) (h : part L ∅=0) :
    part (Poly.pass L) p=∑ k∈ Finset.range (p.card+1),(k.factorial:ℂ)⁻¹*part (L^k) p := by
  unfold part Poly.pass
  simp_rw [Poly.part_sum,Poly.part_smul]
  symm; apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Finset.card_le_univ _)))
  intro k _ hk
  simp only [Finset.mem_range,not_lt] at hk
  rw [Poly.high L h k (mode p) hk,mul_zero]
lemma expo_none (L : Algebra V) (h : part L ∅=0) : part (Poly.pass L) ∅=1 := Poly.pass_part L h
lemma expo_single (L : Algebra V) (h : part L ∅=0) (i : V) : part (Poly.pass L) {i}=part L {i} := by
  have hh : mode {i}≠(all V).quiet := (all V).fire_hot _
  rw [expo_price L _ h]; simp [Finset.sum_range_succ,part,hh]
lemma expo_pair (L : Algebra V) (h : part L ∅=0) (i j : V) (hi : i ≠ j) :
    part (Poly.pass L) {i,j}=part L {i,j}+part L {i} * part L {j} := by
  have hh : mode {i,j} ≠ (all V).quiet := fun e => by
    have hc := mode_inj.mp (e.trans mode_empty.symm)
    simp at hc
  have hb : part (1 : Algebra V) {i,j}=0 := by simp [part,hh]
  have hw : ({i,j}:Finset V).card=2 := Finset.card_pair hi
  rw [expo_price L _ h,hw]
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,pow_zero,pow_one,hb,mul_zero,zero_add]
  rw [sq,mult_pair L L _ _ hi,h]
  norm_num
  ring

-- include zero part in uncorrected initial.
def ordinary (f : V → ℂ) : Algebra V := ∏ i : V, (1+Poly.send ((all V).fire i) (f i))
lemma basis_product (f : V → ℂ) (p : Finset V) :
    ∏ i∈p, Poly.send ((all V).fire i) (f i) = Poly.send (mode p) (∏ i∈p,f i) := by
  induction p using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,ih]; ext z
    rw [Poly.part_send]
    rw [show (Poly.send ((all V).fire i) (f i) * Poly.send (mode s) (∏ i∈s, f i)).part z = if Poly.merges ((all V).fire i) (mode s) z then _ else _ from
      Poly.cart ((all V).fire i) (mode s) z (f i) (∏ i∈s, f i)]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exfalso; apply h₂; apply Subtype.ext; simp only [← h₁.2]; simp [Census.fire]
    · subst z; exfalso; apply h₁; exact ⟨by simpa [Census.fire] using hi, by simp [Census.fire]⟩
    rfl
lemma selects (f : V → ℂ) (p : Finset V) : part (ordinary f) p = ∏ i∈p, f i := by
  unfold ordinary part
  rw [Finset.prod_one_add]; simp_rw [basis_product]
  rw [Poly.part_sum,Finset.sum_eq_single p]
  · simp
  · intro b hb h; simp only [Poly.part_send, mode_inj, if_neg (Ne.symm h)]
  simp

def adjusted (L : Algebra V) (f : V → ℂ) := Poly.pass (-L)*ordinary f


lemma corrected_single (L : Algebra V) (h : part L ∅=0) (f : V → ℂ) (s) :
    part (adjusted L f) {s} = f s - part L {s} := by
  have H : part (-L) ∅=0 := by change -part L ∅=0; rw [h,neg_zero]
  rw [adjusted, mult_single,expo_single _ H,expo_none _ H]; simp_rw [selects]
  simp [part,sub_eq_add_neg]

lemma corrected_pair (L : Algebra V) (h : part L ∅=0) (f : V → ℂ) (s t) (hst : s≠t) :
    part (adjusted L f) {s,t} = (f s-part L {s})*(f t-part L {t})-part L {s,t} := by
  have H : part (-L) ∅=0 := by change -part L ∅=0; rw [h,neg_zero]
  rw [adjusted, mult_pair _ _ _ _ hst,expo_single _ H,expo_single _ H,expo_pair _ H _ _ hst,expo_none _ H]
  simp_rw [selects]
  simp [part,hst]; ring
end YM.Push.Corrected.Marks
