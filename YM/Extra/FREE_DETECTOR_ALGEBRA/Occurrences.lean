import YM.Maxwell.Wick

set_option warningAsError false

/-!
# Adjoining and deleting occurrences in Wick tests

Use powers (distinguishable occurrences of repeated factors) in the actual
hierarchy definition. Multiplicity important.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.Pair
open Function Filter Set Maxwell Wick Wick.Occ
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {n : ℕ}

def bump (W : Powers G n) (i : Fin n) (a : Slot G) := Function.update W i (W i + Finsupp.single a 1)
theorem bump_at (W : Powers G n) (i : Fin n) (a : Slot G) (j : Fin n) (l : Slot G) :
    bump W i a j l = W j l + if i=j ∧ a=l then 1 else 0 := by
  rcases eq_or_ne j i with he|he
  · simp [bump,he,Finsupp.single_apply]
  simp [bump,he,he.symm]

/-- Old occurrences embed. -/
def earlier (W : Powers G n) (i : Fin n) (a : Slot G) (v : Occ W) : Occ (bump W i a) :=
  atSlot v.label v.probe v.index (by rw [bump_at]; exact lt_of_lt_of_le v.legit (le_add_of_nonneg_right (by split <;> norm_num)))

/-- New occurrence. -/
def added (W : Powers G n) (i : Fin n) (a : Slot G) : Occ (bump W i a) :=
    atSlot i a (W i a) (by simp [bump_at])

structure Miss {W Y : Powers G n} (p : Occ W → Occ Y) (head : Occ Y) : Prop where
  good : Injective p
  name v : label (p v)=label v
  read v : Occ.probe (p v)=Occ.probe v
  omit_head v : p v≠head
  fill v : v≠head → ∃ w, p w=v

theorem hole (W : Powers G n) (i : Fin n) (a : Slot G) : Miss (earlier W i a) (added W i a) := by
  let f := earlier W i a
  let p := added W i a
  change Miss f p
  refine ⟨fun v w h => ?_,fun v => rfl,fun v => rfl,?_,?_⟩
  · apply Occ.ext
    · change label (f v)=label (f w); exact congr_arg label h
    · change Occ.probe (f v)=Occ.probe (f w); exact congr_arg Occ.probe h
    · change index (f v)=index (f w); exact congr_arg index h
  · intro v hv
    have hi : v.label=i := congr_arg label hv
    have ht : v.probe=a := congr_arg Occ.probe hv
    have hx : v.index=W i a := congr_arg Occ.index hv
    exact Nat.lt_irrefl (W i a) (by simpa [hi,ht,hx] using v.legit)
  intro v hv
  have he : v.index < W v.label v.probe := by
    by_contra! hh
    have ht := v.legit; rw [bump_at] at ht
    split_ifs at ht with H
    · have hz : v.index = W v.label v.probe := by omega
      have hx : v.index = W i a := by rw [hz,H.1.symm,H.2.symm]
      exact hv (Occ.ext H.1.symm H.2.symm hx)
    · omega
  exact ⟨atSlot v.label v.probe v.index he,rfl⟩

def smaller (W : Powers G n) (i : Fin n) (a : Slot G) := Function.update W i (W i - Finsupp.single a 1)

lemma restores {W : Powers G n} {i : Fin n} {a : Slot G} (h : 0 < W i a) : bump (smaller W i a) i a = W := by
  funext v
  rcases eq_or_ne v i with h|h
  · subst v; simp only [bump,smaller,Function.update_self]
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h)
  simp [bump,smaller,h]

/-- Remove any given occurrence; use the bump equivalence and swap its hole
to this occurrence (possibly changes indices but not assigned probes). -/
lemma remove_hole {W : Powers G n} (p : Occ W) : ∃ f : Occ (smaller W p.label p.probe) → Occ W, Miss f p := by
  let Y := smaller W p.label p.probe
  have he : bump Y p.label p.probe=W := restores (by have := p.legit; omega)
  have e (X : Powers G n) (h : bump Y p.label p.probe=X) : ∃ (f : Occ Y→Occ X) (g : Occ X), Miss f g ∧ g.label=p.label ∧ g.probe=p.probe := by
    subst X; exact ⟨earlier Y p.label p.probe,added ..,hole ..,rfl,rfl⟩
  obtain ⟨f,a,hf,hg,ha⟩ := e W he
  let E := Equiv.swap a p
  have h1 (y : Occ W) : (E y).label=y.label ∧ (E y).probe=y.probe := by
    by_cases ht : y=a
    · rw [ht, show E a = p from Equiv.swap_apply_left _ _]
      exact ⟨hg.symm,ha.symm⟩
    by_cases hv : y=p
    · rw [hv, show E p = a from Equiv.swap_apply_right _ _]
      exact ⟨hg,ha⟩
    simp [E,Equiv.swap_apply_def, ht,hv]
  refine ⟨E ∘ f, hf.good |> E.injective.comp, fun v => (h1 _).1.trans (hf.name v),fun v => (h1 _).2.trans (hf.read v),fun v => ?_,fun v hv => ?_⟩
  · exact fun hh => hf.omit_head v (E.injective (hh.trans (Equiv.swap_apply_left _ _).symm))
  obtain ⟨w,hw⟩ := hf.fill (E.symm v) (fun h => hv (by simpa [E] using (E.symm_apply_eq.mp h)))
  exact ⟨w,E.eq_symm_apply.mp hw⟩

/-- A lift from which two occurrences have been removed, for the Wick
contraction formula. Does not assume or alter any kernel symmetries. -/
structure Edge {W Y : Powers G n} (f : Occ W→Occ Y) (p q : Occ Y) : Prop where
  good : Injective f
  name v : label (f v)=label v
  read v : Occ.probe (f v)=Occ.probe v
  not_left v : f v ≠ p
  not_right v : f v ≠ q
  apart : p.label ≠ q.label
  fill v : v≠p → v≠q → ∃ w, f w=v

theorem with_edge (W : Powers G n) (i : Fin n) (a : Slot G) (v : Occ W) (h : v.label≠i) :
    ∃ f : Occ (smaller W v.label v.probe) → Occ (bump W i a), Edge f (added W i a) (earlier W i a v) := by
  obtain ⟨p,hp⟩ := remove_hole v
  let e := earlier W i a
  have he : Miss e (added W i a) := hole W i a
  refine ⟨e ∘ p,he.good.comp hp.good,fun x => (he.name _).trans (hp.name _),fun x => (he.read _).trans (hp.read _),
    fun x => he.omit_head (p x),fun x => he.good.ne (hp.omit_head x), h.symm, ?_⟩
  intro y ha hb
  obtain ⟨b,rfl⟩ := he.fill y ha
  obtain ⟨c,rfl⟩ := hp.fill b (fun h => hb (congr_arg e h))
  exact ⟨c,rfl⟩
end YM.Extra.FD.Pair
