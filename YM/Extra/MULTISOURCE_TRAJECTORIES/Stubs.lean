import YM.Extra.MULTISOURCE_TRAJECTORIES.Bands
import YM.Next.BOUNDARY.Core
import YM.Work.C03
/-!
# Absolute prices for the exact attachment dictionary

Raw provisional prices can be supplied by a separate estimate. This file
proves a combinatorial sufficient criterion on the entries BEFORE merging
(the residual part needs a genuine hit estimate together with old K;
there is no marker anchor at an unmarked K). At fixed finite volume one can
also simply shrink radii, a useful convergence/identity check but not the
uniform payment. Estimates about derivatives are for the unmasked payload
at all requested orders and with the actual threshold/distance norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Function Filter Lattice Wilson Overlay RG Marker Finset Mix
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side}

lemma budget_image {α β γ : Type*} {e : α → β} {d : α → γ} (he : Injective e) (hd : Injective d)
    {f : β → ℝ} {g : γ → ℝ} {u : ℝ} (hf : ∀ i,0≤f i) (hb : ∀ i∉Set.range e, f i=0)
    (h : SumBudget g u) (hh : ∀ i,f (e i) ≤ g (d i)) : SumBudget f u := by
  have hg : Summable (g ∘ d) := h.2.1.comp_injective hd
  have hs : Summable (f ∘ e) := hg.of_nonneg_of_le (fun i => hf (e i)) hh
  rw [SumBudget, ← he.tsum_eq (fun i hi => by by_contra hn; exact hi (hb i hn))]
  exact ⟨hf,(he.summable_iff hb).1 hs,(hs.tsum_le_tsum_of_inj d hd (fun j _ => h.1 j) hh h.2.1).trans h.2.2⟩

private lemma grain_zero (p : BudgetPoint) (S : Support n) (o : Site n) : grain p S (0 : Config G n → ℂ) o 0 := by
  refine ⟨fun _ => 0, fun _ => le_rfl,by simp,fun k hk hv U _ => ?_⟩
  rw [show (0 : Config G n → ℂ) = (fun _ => 0) from rfl,Work.G07.left_const]; simp

variable {V : Type} [DecidableEq V] {R : Census V} {P : Rep G n}
namespace Layers
variable {α : Type*} (X : Layers P R α)

structure Prices where
  jet : α → ℝ
  attach : α → ℝ
  K : ℕ → ℝ
  nonnegative i : 0≤jet i
  available i x : x∈(X.tag i).val → grain P.p (X.region i) (X.H i) (X.origins x) (jet i)
  residue i U : ‖X.residual i U‖ ≤ attach i
  boundK i U : ‖P.activities.K i U‖ ≤ K i

namespace Prices
variable {X} (Q : X.Prices)

def basic (i : Letter α) := i.elim Q.K Q.attach
lemma paid (i : Letter α) (U : Config G n) : ‖X.weight U i‖ ≤ Q.basic i := by
  cases i with
  | inr i => exact Q.residue ..
  | inl i => simpa [weight,basic] using Q.boundK i U
lemma basic_nn (i : Letter α) : 0 ≤ Q.basic i := (norm_nonneg _).trans (Q.paid i 1)

def bundle (c : X.Component) := ∏ l∈c.val,Q.basic l
lemma bundle_nn (c : X.Component) : 0 ≤ Q.bundle c := prod_nonneg fun i _ => Q.basic_nn i
lemma entry_bound (c : X.Component) (U : Config G n) : ‖X.entry c U‖ ≤ Q.bundle c := by
  unfold entry; split
  · rw [norm_prod]; exact prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => Q.paid i U)
  rw [norm_zero]; exact Q.bundle_nn _

variable [Countable α] [Nonempty V]

def quote (q : ℕ × ℕ) := if X.bands.entries q.1 q.2 = 0 then 0 else unpin Q.bundle 0 q.2

private lemma quote_zero {q : ℕ × ℕ} (h : X.bands.entries q.1 q.2=0) : Q.quote q=0 := if_pos h

def stubs : Stubs X.bands where
  a := unpin Q.jet 0
  k := Q.quote
  nonnegative i := by
    by_cases he : i∈Set.range (pin (α:=α))
    · obtain ⟨i,rfl⟩ := he; rw [unpin_pin]; exact Q.nonnegative i
    exact (unpin_blank _ _ he).ge
  usable p := by
    by_cases he : p.2∈Set.range (pin (α:=X.Component))
    · obtain ⟨c,hc⟩ := he; rw [quote,← hc,unpin_pin]; split
      · rfl
      exact Q.bundle_nn c
    rw [quote,unpin_blank _ _ he]; split <;> rfl
  kernels i := by
    by_cases he : i∈ Set.range (pin (α:=α))
    · obtain ⟨i,rfl⟩ := he; simp only [bands,unpin_pin]; exact Q.available i
    simp only [bands,unpin_blank _ _ he]; exact fun x _ => grain_zero ..
  supplies i j U := by
    by_cases he : j∈ Set.range (pin (α:=X.Component))
    · obtain ⟨c,rfl⟩ := he
      rw [quote]; split
      next h => simp only [h,Pi.zero_apply,norm_zero,le_refl]
      next h =>
        simp only [bands,unpin_pin,routed]; split
        · exact Q.entry_bound c U
        simp only [Pi.zero_apply,norm_zero]; exact Q.bundle_nn c
    simp [bands,quote,unpin_blank _ _ he]
  paid i := by
    rw [quote]; split
    · intro h; exact h.false.elim
    exact fun _ => ‹_ ≠ _›
end Prices

variable [Countable α] [Nonempty V] {X}

lemma funded_of_costs (Q : X.Prices) (h : Aperture P) (w : V → ℝ) (hw : ∀ i,0<w i) (δ u : ℝ) (b : Bool)
    (h₁ : ∀ i : V,SumBudget (fun j => if ranked (X.tag j)=b ∧ i∈(X.tag j).val then
      Poly.toll w (X.tag j) * loaf P.p (X.region j) δ (Q.jet j) else 0) u)
    (h₂ : ∀ i : V,SumBudget (fun c : X.Component => if ranked (X.stamp c)=b ∧ i∈(X.stamp c).val then
      Poly.toll w (X.stamp c)*loaf P.p (X.skin c.val) δ (Q.bundle c) else 0) u) : Q.stubs.funded w δ b u := by
  constructor
  · intro i
    apply budget_image (e:=pin (α:=α)) pin_injective injective_id _ _ (h₁ i)
    · intro j
      simp only [Stubs.crown,Prices.stubs,bands,unpin_pin,id_eq,le_refl]
    · intro j; split
      · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (Q.stubs.nonnegative j))
      rfl
    · intro j hj; split
      · simp [Stubs.crown,Prices.stubs,unpin_blank _ _ hj,loaf]
      rfl
  intro i
  let e := fun c : X.Component => (X.slot (.inr c), pin c)
  apply budget_image (e:=e) (fun c c' (h : e c=e c') => pin_injective (Prod.mk.inj h).2) injective_id _ _ (h₂ i)
  · intro c; dsimp only [Stubs.cord,Prices.stubs,Prices.quote,id_eq,bands,e]; simp only [unpin_pin]
    rw [← X.skin_slot _ h]
    split
    · refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) (Poly.worth hw _).le
      split
      · exact Q.bundle_nn c
      rfl
    rfl
  · intro j; split
    · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (Q.stubs.usable j))
    rfl
  · rintro ⟨j,k⟩ hj; split
    · suffices X.bands.entries j k=0 by simp [Stubs.cord,Prices.stubs,Q.quote_zero (q:=(j,k)) this,loaf]
      by_cases he : k∈Set.range (pin (α:=X.Component))
      · obtain ⟨c,rfl⟩ := he; simp only [bands,unpin_pin,routed]
        exact if_neg (fun he => hj ⟨c,Prod.ext he rfl⟩)
      exact unpin_blank _ _ he
    rfl

/-- One tree price at provisional or direct rates. At the singleton sale
can omit mixed-rank input; no committee with mixed input can resell as a
singleton. No forcedAllowance divisor demanded at Stubs here. -/
def rental (Q : X.Prices) (w : V → ℝ) (mix : Bool) (l : Letter α) := l.elim Q.K
  (fun i => if mix = true ∨ ranked (X.tag i)=false then Poly.toll w (X.tag i) * Q.attach i else 0)

omit [Countable α] [Nonempty V] in
lemma rent_nn (Q : X.Prices) (w : V → ℝ) (hw : ∀ i,0<w i) (mix : Bool) (l : Letter α) : 0 ≤ rental Q w mix l := by
  unfold rental; cases l with
  | inl i => exact Q.basic_nn (.inl i)
  | inr i => dsimp only [Sum.elim_inr]; split
             · exact mul_nonneg (Poly.worth hw _).le (Q.basic_nn (.inr i))
             rfl

omit [Countable α] [Nonempty V] in
lemma rent_eq (Q : X.Prices) (w : V → ℝ) (mix : Bool) (c : X.Component) (h : ranked (X.stamp c)=mix) :
    ∏ l∈c.val,rental Q w mix l = Poly.toll w (X.stamp c) * Q.bundle c := by
  have he (i) (hi : i ∈ c.val.toRight) : mix = true ∨ ranked (X.tag i)=false := by
    cases h' : mix <;> simp only [Bool.false_eq_true,false_or,true_or]
    rw [h'] at h
    have hS := subset_biUnion_of_mem (fun i => (X.tag i).val) hi
    have ht := card_le_card hS
    change _ ≤ (X.stamp c).val.card at ht
    simp only [ranked,decide_eq_false_iff_not] at h ⊢; omega
  rw [Prices.bundle,prod_sum_eq_prod_toLeft_mul_prod_toRight,prod_sum_eq_prod_toLeft_mul_prod_toRight,stamp,toll_union]
  dsimp only [rental,Prices.basic,Sum.elim_inl,Sum.elim_inr]
  rw [show ∏ x∈c.val.toRight, (if mix = true ∨ ranked (X.tag x)=false then Poly.toll w (X.tag x)*Q.attach x else 0)
      = ∏ x∈c.val.toRight,Poly.toll w (X.tag x)*Q.attach x from prod_congr rfl fun i hi => if_pos (he i hi),
      Finset.prod_mul_distrib]; ring

/-- A sufficient estimate entirely *before* gathering, in terms of entries
and vacuum sup tests rather than the existence of packet receipts. Uniform
under the displayed conditions, independent of number of letters. In
particular does require a support-exponent reserve on OLD unmarked K;
Lawful alone at exactly `p.supportExponent` doesn't give that reserve. -/
theorem financed [DecidableEq α] (Q : X.Prices) (h : Aperture P) (hr : X.Anchored) (w : V → ℝ) (hw : ∀ i,0<w i)
    (δ u γ : ℝ) (mix : Bool) (hδ : 0 ≤ δ) (hg : 0≤γ) (hu : Real.exp γ - 1 ≤ u) (hv : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1)
    (hc : ∀ i : V,SumBudget (fun j => if ranked (X.tag j)=mix ∧ i∈(X.tag j).val then
      Poly.toll w (X.tag j) * loaf P.p (X.region j) δ (Q.jet j) else 0) u)
    (hh : Ac.Hit X.area P.p.B (rental Q w mix) (P.p.supportExponent+δ+1) γ) : Q.stubs.funded w δ mix u := by
  apply funded_of_costs Q h w hw δ u mix hc
  intro i
  let R := Ac.roots X.area P.p.B (rental Q w mix) (P.p.supportExponent+δ) (X.origins i)
  have hx : SumBudget R (Real.exp γ-1) := Ac.forest _ _ (add_nonneg P.p.exponent_pos.le hδ) (rent_nn Q w hw mix) hh hv hg _
  apply budget_image injective_id (Subtype.val_injective (p:=X.Solid)) _ _ (show SumBudget R u from
    ⟨hx.1,hx.2.1,hx.2.2.trans hu⟩)
  · intro c; dsimp only [id_eq]; split
    next he =>
      have ho : X.origins i ∈ X.skin c.val := X.skin_slot (.inr c) h ▸ X.stamp_home h hr c he.2
      dsimp only [R,Ac.roots]; rw [if_pos ⟨c.property.join,ho⟩,loaf,rent_eq Q w mix c he.1,skin]
      exact le_of_eq (by rw [mul_left_comm])
    exact hx.1 _
  · intro c; split
    · exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_pos _).le (Q.bundle_nn c))
    rfl
  · simp
end Layers
end YM.Extra.Trajectories
