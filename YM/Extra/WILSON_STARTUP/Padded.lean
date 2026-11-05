import YM.Bid.Craft
import YM.Next.EXTRACTION.Tails
import YM.Work.B09.Core

/-!
# Nat labels with explicit spare addresses

Use even at finite period with zero padding; wants full relabelling including
all dormant entries. No cardinality costs or uniformity conclusions implicit.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter RG
open scoped Classical
namespace Padded
variable (α : Type*) [Countable α] [Nonempty α]

def codec : ℕ ≃ α × ℕ :=
  letI := Classical.choice (nonempty_denumerable (α × ℕ))
  (Denumerable.eqv _).symm

def fixed (i : ℕ) := (codec α i).2=0

def name (i : ℕ) := (codec α i).1

variable {α}

def index (a : α) : ℕ := (codec α).symm (a,0)

def sends (s : Equiv.Perm α) : Equiv.Perm ℕ := ((codec α).trans (Equiv.prodCongr s (Equiv.refl ℕ))).trans (codec α).symm

@[simp] theorem fixed_sends (s : Equiv.Perm α) (i : ℕ) : fixed α (sends s i) ↔ fixed α i := by simp [sends,fixed]
@[simp] theorem name_sends (s : Equiv.Perm α) (i : ℕ) : name α (sends s i) = s (name α i) := by simp [sends,name]
@[simp] theorem fixed_index (a : α) : fixed α (index a) := by simp [fixed,index]
@[simp] theorem name_index (a : α) : name α (index a) = a := by simp [name,index]
theorem index_name {i : ℕ} (h : fixed α i) : index (name α i) = i := by
  unfold index name
  have := h
  unfold fixed at h
  rw [← h]; exact Equiv.symm_apply_apply _ _
theorem index_injective : Injective (index (α:=α)) := fun i j h => by simpa using congr_arg (name α) h

variable {X : Type*} [AddCommMonoid X] [TopologicalSpace X] {f : ℕ → X} {g : α → X}

theorem has [Fintype α] (h : ∀ i, f i = if fixed α i then g (name α i) else 0) : HasSum f (∑ x, g x) := by
  refine (index_injective.hasSum_iff (g:=index (α:=α)) (fun x hx => ?_)).mp ?_
  · rw [h,if_neg]; exact fun hh => hx ⟨_,index_name hh⟩
  simpa [comp_def,h] using! hasSum_fintype g

theorem totals [T2Space X] [Fintype α] (h : ∀ i, f i = if fixed α i then g (name α i) else 0) : ∑' i, f i = ∑ x, g x :=
  (has h).tsum_eq

theorem budget [Fintype α] {f : ℕ → ℝ} {g : α → ℝ} {c : ℝ} (h : ∀ i, f i = if fixed α i then g (name α i) else 0)
    (hg : ∀ i, 0 ≤ g i) (ht : ∑ i, g i ≤ c) : SumBudget f c :=
  ⟨fun i => by rw [h]; split <;> first | exact hg _ | exact le_rfl, (has h).summable,(totals h).trans_le ht⟩
end Padded
end YM.WilsonStartup
