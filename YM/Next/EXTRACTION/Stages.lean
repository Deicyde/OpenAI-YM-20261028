import YM.Next.EXTRACTION.Base

/-!
# If further estimates are obtained only stage by stage

It can happen that adding the input concerning a new fixed weight d requires
yet another refinement of the pair while retaining the tables. Provide the
diagonal operation for countably many stages and show how to use this to
finish an arrival. We *still* need compatible estimates: the displayed use
requires being able to do each stage on a refinement of **any** order under
the given extraction. Not a way to combine independent incompatible choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Function Filter Extraction Dash Set

private theorem diagonal_seq (F : ℕ → Sequence) (h : ∀ i, ∃ g, F (i+1) = (F i).after g) :
    ∃ g : Sequence, ∀ i, Tail ((F 0).after g) (F i) := by
  have he i j (hj : i ≤ j) : ∃ g, F j = (F i).after g := by
    induction j,hj using Nat.le_induction with
    | base => exact ⟨Sequence.full,rfl⟩
    | succ j _ ih =>
      obtain ⟨g₁,h₁⟩ := ih
      obtain ⟨g₂,h₂⟩ := h j
      exact ⟨g₁.after g₂, by rw [h₂,h₁]; rfl⟩
  let t i := F i i
  have ht : StrictMono t := by
    apply strictMono_nat_of_lt_succ
    intro i
    obtain ⟨g,hg⟩ := h i
    have hw := g.monotone.id_le (i+1)
    dsimp [t]
    rw [hg]; change F i i < F i (g (i+1))
    exact (F i).monotone (lt_of_lt_of_le (Nat.lt_succ_self i) hw)
  choose p hp using fun i => he 0 i (Nat.zero_le i)
  let u i := p i i
  have hh i : t i = F 0 (u i) := Sequence.after_apply (F 0) (p i) i ▸ congr_arg (fun (s : Sequence) => s i) (hp i)
  let g : Sequence := ⟨u,fun i j hij => (F 0).monotone.lt_iff_lt.mp (by rw [←hh,←hh]; exact ht hij)⟩
  refine ⟨g,fun i => ?_⟩
  filter_upwards [eventually_ge_atTop i] with j hj
  obtain ⟨v,hv⟩ := he _ _ hj
  refine ⟨v j,?_⟩
  rw [Sequence.after_apply,show g j = u j from rfl,← hh]
  exact congr_arg (fun (s : Sequence) => s j) hv.symm

/-- Diagonalize refinements of *orders*. Both mesh and period sequences
refine up to tails, separately. (There need be no single order exactly
refining every F i: their ranges may have empty intersection.) -/
theorem diagonal (F : ℕ → Order) (h : ∀ i, ∃ g, F (i+1) = (F i).refine g) :
    ∃ g : Order, ∀ i, Tails ((F 0).refine g) (F i) := by
  choose g hg using h
  obtain ⟨u,hu⟩ := diagonal_seq (fun i => (F i).mesh) fun i => ⟨(g i).mesh,congr_arg Order.mesh (hg i)⟩
  obtain ⟨v,hv⟩ := diagonal_seq (fun i => (F i).per) fun i => ⟨(g i).per,congr_arg Order.per (hg i)⟩
  exact ⟨⟨u,v⟩,fun i => ⟨hu i,hv i⟩⟩




end YM.Next.Extract
