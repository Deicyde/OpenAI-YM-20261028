import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Animals
import YM.Push.ABSOLUTE_SUMS.Basic
import YM.Work.E01



/-!
# E Fproj follow-through: weighted per-old-anchor → charged hits

The support estimate and *complete* per-address input budget imply
hit/cover estimates after coarsening and halo/enlargement costs.
Includes winding and arbitrarily many address variants. This module is
ONLY price conversion; does not decide for any physical construction
whether the complete footprints fit (flag read, routes, orientation
queries etc). `X` in the resulting tests may be an enlarged dominating
footprint. Use on exact `EBound`/`KBound` inputs later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Footprint
open Lattice Lattice.Corona Finset RG Animals
open scoped Topology BigOperators Classical
variable {ι κ : Type*} {c f : Side}

/-- Per-fine-anchor budgets of given native address weights. `d` may
for example be coverNumber of old support, or the *true length* for
use with a path-price array. -/
def Anchored (o : ι → Site f) (b : ι → ℝ) (d : ι → ℕ) (A γ : ℝ) :=
  ∀ x : Site f, SumBudget (fun i => if o i=x then b i*Real.exp (A*d i) else 0) γ

-- Written separately to see exactly which constants enter a gate.

def reserve (A a v ε : ℝ) := 0≤a ∧ 0<ε ∧ a*v+2*ε≤A

def spread (P W : ℕ) := P*ballCost W

def degreeIncome (P W k : ℕ) (ε C γ a v : ℝ) := Real.exp (a*v)*γ*C * spread P W *
  (ε⁻¹^(4+k) * (4+k).factorial * Real.exp ε)

def payment (P W k : ℕ) (ε C γ a v : ℝ) := degreeIncome P W k ε C γ a v *
  (1-Real.exp (-ε))⁻¹

section General
variable (p : Site f → Site c) (P : ℕ)

def Population := ∀ Y : Support c, (univ.filter (fun x => p x∈Y)).card ≤ Y.card*P

private lemma locations (hp : Population p P) (W k : ℕ) (x : Site c) :
    let Y := neighbors (W*(1+k)) x
    (univ.filter (fun x => p x∈Y)).card ≤ spread P W*(1+k)^4 := by
  intro Y
  have h : ballCost (W*(1+k))≤ballCost W*(1+k)^4 := by
    unfold ballCost; rw [← mul_pow]; gcongr; nlinarith
  refine (hp Y).trans ?_
  unfold spread; rw [mul_assoc,Nat.mul_comm P]; exact Nat.mul_le_mul_right _
    ((neighbors_card ..).trans h)

-- A useful geometric test independent of `collapse`'s hypothesis
-- (e.g. other certified footprints can use the same accounting).
lemma assigned_tail (hp : Population p P) (o : ι → Site f) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (d : ι → ℕ) (X : ι → Support c) {A γ : ℝ} (ha : Anchored o b d A γ) (W k B : ℕ)
    {v v' : ℝ} (hW : ∀ i x, x∈X i → separation x (p (o i)) ≤ W*(1+d i))
    (hh : ∀ i, (coverNumber B (X i):ℝ) ≤ v + v'*d i)
    {C a ε : ℝ} (hC : 0 ≤ C) (hr : reserve A a v' ε) (g : ι → ℝ) (hg : ∀ i, 0≤g i)
    (hc : ∀ i, g i ≤ C*b i*(1+(d i:ℝ))^k) (m : ℕ) (x : Site c) :
    SumBudget (fun i => if m ≤ d i then (if x∈X i then g i * Real.exp (a*coverNumber B (X i)) else 0)
      else 0) (payment P W k ε C γ a v * Real.exp (-ε)^m) := by
  let z i := if x∈X i then g i*Real.exp (a*coverNumber B (X i)) else 0
  have hz i : 0 ≤ z i := by
    unfold z; split
    · exact mul_nonneg (hg i) (Real.exp_pos _).le
    · exact le_rfl
  have hy : 0 ≤ γ := budget_nonneg (ha 0)
  have he : 0 < ε := hr.2.1
  let D := degreeIncome P W k ε C γ a v
  have hi : 0 ≤ D := by unfold D degreeIncome; positivity
  have hx i : g i*Real.exp (a*coverNumber B (X i)) ≤
      b i * Real.exp (A*d i) * (C*(1+(d i:ℝ))^k * Real.exp (a*v-2*ε*d i)) := by
    have h := mul_le_mul_of_nonneg_left (hh i) hr.1
    have hv : a*(coverNumber B (X i):ℝ) ≤ A*d i+(a*v-2*ε*d i) := by
      have he := mul_le_mul_of_nonneg_right hr.2.2 (show 0 ≤ (d i:ℝ) by positivity)
      nlinarith
    refine (mul_le_mul (hc i) (Real.exp_monotone hv) (Real.exp_pos _).le ?_).trans_eq
      (by rw [Real.exp_add]; ring)
    have h := hb i; positivity
  unfold payment; rw [mul_right_comm _ (1-Real.exp _)⁻¹]
  refine budget_degrees_tail d hz hi (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)) ?_ m
  intro j s hj
  let t := s.filter (fun i => x∈X i)
  let Y := univ.filter (fun y => p y∈neighbors (W*(1+j)) x)
  let q i : ℝ := b i * Real.exp (A*d i)
  let E : ℝ := C*(1+(j:ℝ))^k * Real.exp (a*v-2*ε*j)
  have hE : 0 ≤ E := by unfold E; positivity
  have hu i (h : i∈t) : o i∈Y := by
    obtain ⟨h1,h2⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_univ _,(neighbors_mem ..).mpr ((hj i h1) ▸ hW i x h2)⟩
  have hq y : ∑ i∈t with o i=y, q i ≤ γ := by
    rw [Finset.sum_filter]; exact budget_sum (ha y) _
  have hY : (Y.card:ℝ) ≤ (spread P W:ℝ)*(1+(j:ℝ))^4 := by
    exact_mod_cast locations p P hp W j x
  change ∑ i ∈ s,z i ≤ _
  calc
    _ = ∑ i∈t, g i * Real.exp (a*coverNumber B (X i)) := (Finset.sum_filter _ _).symm
    _ ≤ ∑ i∈t, q i*E := sum_le_sum fun i h => by
      have H := hx i; unfold E q; rw [← hj i (mem_filter.mp h).1]; exact H
    _ = (∑ y∈Y, ∑ i∈t with o i=y,q i)*E := by rw [sum_fiberwise_of_maps_to hu,Finset.sum_mul]
    _ ≤ (Y.card*γ)*E := by
      have he : (∑ y∈Y, ∑ i∈t with o i=y,q i) ≤ ∑ _y∈Y,γ := sum_le_sum fun y _ => hq y
      simpa using mul_le_mul_of_nonneg_right he hE
    _ ≤ (spread P W*(1+(j:ℝ))^4*γ)*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hY hy) hE
    _ = (spread P W*γ*C*Real.exp (a*v-2*ε*j))*(1+(j:ℝ))^(4+k) := by unfold E; ring
    _ ≤ (spread P W*γ*C*Real.exp (a*v-2*ε*j)) *
        ((ε⁻¹^(4+k)*(4+k).factorial*Real.exp ε)*Real.exp (ε*j)) := by
        apply mul_le_mul_of_nonneg_left (polynomial_cost he (by positivity) _); positivity
    _ = D*Real.exp (-ε)^j := by
        unfold D degreeIncome; rw [← Real.exp_nat_mul]
        have he : Real.exp (a*v-2*ε*j)*Real.exp (ε*j) = Real.exp (a*v)*Real.exp ((j:ℝ)*(-ε)) := by
          simp only [← Real.exp_add]; ring_nf
        calc _ = Real.exp (a*v-2*ε*j) * Real.exp (ε*j) *
                (γ*C*spread P W*(ε⁻¹^(4+k)*(4+k).factorial*Real.exp ε)) := by ring
             _ = _ := by rw [he]; ring

lemma assigned (hp : Population p P) (o : ι → Site f) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (d : ι → ℕ) (X : ι → Support c) {A γ : ℝ} (ha : Anchored o b d A γ) (W k B : ℕ)
    {v v' : ℝ} (hW : ∀ i x, x∈X i → separation x (p (o i)) ≤ W*(1+d i))
    (hh : ∀ i, (coverNumber B (X i):ℝ) ≤ v + v'*d i)
    {C a ε : ℝ} (hC : 0 ≤ C) (hr : reserve A a v' ε) (g : ι → ℝ) (hg : ∀ i, 0≤g i)
    (hc : ∀ i, g i ≤ C*b i*(1+(d i:ℝ))^k) :
    Ac.Hit X B g a (payment P W k ε C γ a v) := by
  intro x; simpa using assigned_tail p P hp o b hb d X ha W k B hW hh hC hr g hg hc 0 x
end General

section Collapse
variable (p : Ratio c f) (l B M : ℕ)

def enlargement (X : Support f) := halo (l*B) (X.image p.parent)
def preCost := (ballCost (l+6):ℝ)
def conversion := 10*preCost l / p.count.val
-- deliberately simple position test (powers of this paid post-L).
def extentCost := (l+20)*B

lemma crowd : Population p.parent (p.count.val^4) := by
  intro Y
  calc
    _ ≤ ((Y ×ˢ (univ:Support p.count)).image p.assemble).card := by
      apply Finset.card_le_card
      intro i hi
      exact mem_image.mpr ⟨(p.parent i,p.residue i), mem_product.mpr ⟨(mem_filter.mp hi).2,
        mem_univ _⟩,p.unpack_at i⟩
    _ ≤ _ := card_image_le.trans (by rw [card_product,card_univ,Lattice.site_card])

lemma footprint (X : Support f) (hB : 0 < B) (hM : M ≤ 2*B) :
    (coverNumber B (enlargement p l B X):ℝ) ≤ preCost l + conversion p l * coverNumber M X := by
  have hp : 0 < (p.count.val:ℝ) := by positivity
  have he := Lattice.Corona.collapse p X M B hB hM l
  have hv : (p.count.val:ℝ)*coverNumber B (enlargement p l B X) ≤
      (p.count.val+10*(coverNumber M X:ℝ))*preCost l := by
    unfold enlargement preCost ballCost; exact_mod_cast he
  unfold conversion; field_simp; linarith

lemma where_from (X : Support f) {x : Site f} (hx : x∈X) {y : Site c}
    (hy : y ∈ enlargement p l B X) (hB : 0 < B) (hM : M ≤ 2*B) :
    separation y (p.parent x) ≤ extentCost l B*(1+coverNumber M X) := by
  obtain ⟨z,hz,he⟩ := halo_spec.mp hy
  obtain ⟨z,hz2,rfl⟩ := mem_image.mp hz
  have hh := extent X M hz2 hx
  have hl : separation (p.parent z) (p.parent x) ≤ separation z x + 1 := by
    have h := foreshorten p z x
    apply Nat.le_of_mul_le_mul_left _ p.count.property
    have he : 1 ≤ p.count.val := p.count.property
    apply h.trans
    rw [Nat.mul_add, Nat.mul_one]
    calc separation z x + _ = 1 * separation z x + p.count.val := by rw [one_mul]
         _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right (separation z x) he) _
  have he' := separation_triangle y (p.parent z) (p.parent x)
  rw [separation_comm _ y] at he
  apply he'.trans
  unfold extentCost
  nlinarith

lemma coarsen_tail (X : ι → Support f) (o : ι → Site f) (ho : ∀ i, o i∈X i) (b : ι → ℝ)
    (hb : ∀ i,0≤b i) {A γ : ℝ} (hh : Anchored o b (fun i => coverNumber M (X i)) A γ)
    (Y : ι → Support c) (he : ∀ i, Y i ⊆ enlargement p l B (X i))
    (hB : 0 < B) (hM : M ≤ 2*B)
    {C a ε : ℝ} (hC : 0 ≤ C) (hr : reserve A a (conversion p l) ε) (k : ℕ) (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hc : ∀ i, g i ≤ C*b i*(1+(coverNumber M (X i):ℝ))^k) (m : ℕ)
    (x : Site c) : SumBudget (fun i => if m ≤ coverNumber M (X i) then
      (if x∈Y i then g i * Real.exp (a*coverNumber B (Y i)) else 0) else 0)
      (payment (p.count.val^4) (extentCost l B) k ε C γ a (preCost l) * Real.exp (-ε)^m) := by
  refine assigned_tail p.parent _ (crowd p) o b hb _ Y hh (extentCost l B) k B
    (fun i x hx => where_from p l B M _ (ho i) (he i hx) hB hM)
    (fun i => ?_) hC hr g hg hc m x
  apply le_trans _ (footprint p l B M _ hB hM)
  exact_mod_cast cover_mono (he i) B

lemma coarsen (X : ι → Support f) (o : ι → Site f) (ho : ∀ i, o i∈X i) (b : ι → ℝ)
    (hb : ∀ i,0≤b i) {A γ : ℝ} (hh : Anchored o b (fun i => coverNumber M (X i)) A γ)
    (Y : ι → Support c) (he : ∀ i, Y i ⊆ enlargement p l B (X i))
    (hB : 0 < B) (hM : M ≤ 2*B)
    {C a ε : ℝ} (hC : 0 ≤ C) (hr : reserve A a (conversion p l) ε) (k : ℕ) (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hc : ∀ i, g i ≤ C*b i*(1+(coverNumber M (X i):ℝ))^k) :
    Ac.Hit Y B g a (payment (p.count.val^4) (extentCost l B) k ε C γ a (preCost l)) := by
  intro x; simpa only [Nat.zero_le,true_iff,↓reduceIte,pow_zero,mul_one] using
    coarsen_tail p l B M X o ho b hb hh Y he hB hM hC hr k g hg hc 0 x

lemma inspected_price (X : Support f) (hB : 0 < B) : enlargement p l B (inspected X) ⊆
    enlargement p (l+5) B X := by
  intro v hv
  obtain ⟨y,hy,hr⟩ := halo_spec.mp hv
  obtain ⟨y,hy2,rfl⟩ := mem_image.mp hy
  have hh : ∃ z∈X,separation z y ≤ 4 := by
    rcases mem_union.mp hy2 with he|he
    · exact ⟨y,he,by simp⟩
    obtain ⟨q,-,hq⟩ := mem_biUnion.mp he
    split at hq
    next h => simp at hq
    next h =>
      rw [Finset.not_disjoint_iff] at h
      obtain ⟨z,h1,h2⟩ := h
      have hy := Work.E01.sep_touched q y hq; have hh := Work.E01.sep_touched q z h2
      refine ⟨z,h1,(separation_triangle z q.1 y).trans ?_⟩
      rw [separation_comm z]; omega
  obtain ⟨z,hz,hh⟩ := hh
  refine halo_spec.mpr ⟨p.parent z,mem_image_of_mem _ hz,(separation_triangle _ (p.parent y) _).trans ?_⟩
  have hh' := foreshorten p z y; have he : 0 < p.count.val := p.count.property
  have hi : separation (p.parent z) (p.parent y) ≤ 5 := Nat.le_of_mul_le_mul_left
    (hh'.trans (show separation z y + p.count.val ≤ p.count.val * 5 by omega)) he
  rw [Nat.add_mul]; omega
end Collapse
end YM.Push.AbsoluteSums.Footprint
