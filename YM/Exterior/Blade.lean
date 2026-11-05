import YM.CellFourier.Shuttle

/-!
# Koszul blade matrix convention

Initial corner, increasing axes. Finite orthonormal coordinate types.
Convenient also for gestures on Laurent data. `left` is wedge with the
axis present. Tensor signs only within one blade.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Exterior
open Lattice Bloch Laurent Matrix Function Finset
open scoped Topology BigOperators ContDiff

abbrev Blade (α : Type*) (r : ℕ) := {s : Finset α // s.card=r}
variable {r : ℕ} {α A : Type*} [LinearOrder α]

def remove (i : α) (S : Blade α (r+1)) (h : i∈S.val) : Blade α r := ⟨S.val.erase i,by simp [card_erase_of_mem h,S.property]⟩

def pre (S : Finset α) (i : α) := (S.filter (fun a => a < i)).card

def parity (S : Finset α) (i : α) (A : Type*) [Ring A] := (-1:A)^pre S i

variable (A) [CommRing A]

/-- includes sign from insertion into sorted place. -/
def left (r : ℕ) (i : α) : Matrix (Blade α (r+1)) (Blade α r) A := Matrix.of fun S b =>
    if h : i∈S.val then if remove i S h=b then parity S.val i A else 0 else 0

lemma pre_lo (S : Finset α) {i j} (h : j ≤ i) : pre (S.erase i) j=pre S j := by
  unfold pre; congr 1; ext x
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨-,hx⟩,hi⟩; exact ⟨hx,hi⟩
  rintro ⟨hx,hi⟩; exact ⟨⟨(lt_of_lt_of_le hi h).ne,hx⟩,hi⟩

lemma pre_hi (S : Finset α) {i j} (h : i<j) (he : i∈S) : pre (S.erase i) j+1=pre S j := by
  unfold pre; rw [show (S.erase i).filter (· < j)=(S.filter (fun a => a < j)).erase i by ext; simp; tauto]; exact card_erase_add_one (by simp [*])

variable [Fintype α]

lemma eliminate (v : Blade α r → A) (b : Blade α (r+1)) (i : α) :
    (left A r i *ᵥ v) b = if h : i∈b.val then parity b.val i A * v (remove i b h) else 0 := by
  simp only [left,Matrix.mulVec,dotProduct, Matrix.of_apply]
  split <;> rename_i h <;> simp [ite_mul]

lemma weave (B : Matrix (Blade α r) (Blade α (r-1)) A) (x : Blade α (r+1)) (c : Blade α (r-1)) (i : α) :
    ((left A r i)*B) x c = if h : i∈x.val then parity x.val i A * B (remove i x h) c else 0 := eliminate ..

lemma square_zero (r : ℕ) (i : α) : left A (r+1) i * left A r i=0 := by
  ext a b
  have he : _ = if h : i∈a.val then parity a.val i A * left A r i (remove i a h) b else 0 := eliminate A (fun x => left A r i x b) a i
  change Matrix.mulVec _ _ a = _; rw [he]; split <;> rename_i H
  · simp [left,remove]
  rfl

lemma anticomm_le (r : ℕ) (i j : α) (h : i<j) : left A (r+1) i * left A r j=-(left A (r+1) j * left A r i) := by
  ext a b
  rw [Matrix.neg_apply]; change Matrix.mulVec _ _ a= -(Matrix.mulVec _ _ a)
  rw [eliminate,eliminate]
  by_cases ha : i∈ a.val
  · by_cases hb : j∈ a.val
    · have hS : j∈(remove i a ha).val := by simp [remove,h.ne',hb]
      have hT : i∈(remove j a hb).val := by simp [remove,h.ne,ha]
      simp only [ha,hb,↓reduceDIte,left,Matrix.of_apply,hS,hT]
      rw [show remove j _ hS= remove i _ hT by ext; simp [remove]; tauto]; split_ifs
      · unfold parity
        rw [← pre_hi a.val h ha,show pre (remove j a hb).val i=pre a.val i from pre_lo a.val h.le, pow_succ]; simp only [remove]; ring
      simp
    simp [ha,hb,left,remove]
  by_cases hb : j∈a.val <;> simp [ha,hb,left, remove]

lemma anticomm (r : ℕ) (i j : α) : left A (r+1) i * left A r j=-(left A (r+1) j * left A r i) := by
  rcases lt_trichotomy i j with h|h|h
  · exact anticomm_le _ _ _ _ h
  · rw [h,square_zero]; simp
  rw [anticomm_le A r j i h,neg_neg]

variable {A}
def wedge (r : ℕ) (q : α → A) := ∑ i, q i • left A r i

lemma d_d (r : ℕ) (q : α → A) : wedge (r+1) q * wedge r q=0 := by
  unfold wedge; rw [Matrix.sum_mul]; simp_rw [Matrix.mul_sum]
  let m := fun i j => q i • left A (r+1) i * q j • left A r j
  change ∑ i, ∑ j, m i j=0
  have hh (i j) : m i j= -m j i := by
    unfold m; rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul, Matrix.smul_mul,
      anticomm A _ i, smul_neg,smul_neg, smul_comm (q j) (q i)]
  have hz (i) : m i i=0 := by simp [m,square_zero]
  have hl (s : Finset α) : ∑ i∈s, ∑ j∈s, m i j=0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [sum_insert hi,sum_insert hi,hz]
      simp_rw [sum_insert hi, sum_add_distrib,ih,zero_add,add_zero]
      rw [show (∑ j ∈ s, m i j) = -∑ j∈s, m j i by
        rw [← Finset.sum_neg_distrib]; exact sum_congr rfl fun j _ ↦ hh i j,neg_add_cancel]
  exact hl _
end YM.Exterior
