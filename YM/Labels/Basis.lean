import YM.Labels.Grading

/-! Choose real, filtered coefficient frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.Labels
open Submodule Function Set
open scoped BigOperators ComplexConjugate

variable {G : Gauge} {d : ℕ}

/-- Real and living in one bidegree. -/
def pureReal (G : Gauge) (d : ℕ) :=
    {v : Label G d | realBar v = v ∧ ∃ m : ℕ × ℕ, m.1 ≤ d ∧ v ∈ Grade m}

lemma pure_real_span : ⊤ ≤ span ℂ (pureReal G d) := by
  intro x _
  rw [← decompose x]
  refine sum_mem fun i hi ↦ sum_mem fun j _ ↦ ?_
  let y := gradePart (i,j) x
  have hh : y ∈ Grade (i,j) := gradePart_mem ..
  have hb : realBar y ∈ Grade (i,j) := by unfold y; rw [← gradePart_bar]; exact gradePart_mem ..
  have h' : (i,j).1 ≤ d := Nat.le_of_lt_succ <| Finset.mem_range.mp hi
  have hp : y + realBar y ∈ span ℂ (pureReal G d) := subset_span (by
    refine ⟨by simp [add_comm], (i,j), h', add_mem hh hb⟩)
  have hq : Complex.I • (y - realBar y) ∈ span ℂ (pureReal G d) := subset_span (by
    refine ⟨?_, (i,j), h', smul_mem _ _ (sub_mem hh hb)⟩
    rw [realBar.map_smulₛₗ, map_sub, twice]; simp [smul_sub]; abel)
  have e : (1/2 : ℂ) • ((y + realBar y) + (-Complex.I) • (Complex.I • (y - realBar y))) = y := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, show
      y + realBar y + (y - realBar y) = (2:ℂ) • y by rw [two_smul]; abel]
    rw [smul_smul, div_mul_cancel₀ _ (by norm_num), one_smul]
  change y ∈ _; exact e ▸ smul_mem _ _ (add_mem hp (smul_mem _ _ hq))

lemma unit_grade (d : ℕ) : unit G d ∈ Grade (0,0) :=
  MvPolynomial.isWeightedHomogeneous_one ℂ bidegree

@[simp] theorem unit_real (d : ℕ) : realBar (unit G d) = unit G d :=
  Subtype.ext (show conjPol _ = _ from map_one _)

theorem unit_not_zero : unit G d ≠ 0 := fun h =>
  one_ne_zero (congr_arg (fun x : Label G d => x.val) h)

theorem pure_unique {u : Label G d} (h : u ≠ 0) (a b : ℕ × ℕ) (ha : u ∈ Grade a) (hb : u ∈ Grade b) : a=b := by
  by_contra hx
  exact h ((gradePart_self u a ha).symm.trans (gradePart_zero u a b hx hb))

lemma pure_unit : unit G d ∈ pureReal G d := ⟨unit_real _,(0,0), Nat.zero_le _, unit_grade d⟩

structure Frame (G : Gauge) (d : ℕ) where
  extra : ℕ
  basis : Module.Basis (Fin (extra+1)) ℂ (Label G d)
  starts_unit : basis 0 = unit G d
  grades : Fin (extra+1) → ℕ × ℕ
  realForm (i : Fin (extra+1)) : realBar (basis i) = basis i
  bound (i : Fin (extra+1)) : (grades i).1 ≤ d
  pure (i : Fin (extra+1)) : basis i ∈ Grade (grades i)

lemma extend_subset {P : Set (Label G d)} (H : LinearIndepOn ℂ id P) (hP : P ⊆ pureReal G d) (he : unit G d ∈ P) :
    ∃ b : Frame G d, P ⊆ Set.range b.basis := by
  classical
  obtain ⟨s, hs, hPs, Hs, Hli⟩ := exists_linearIndepOn_id_extension H hP
  have Hsp := (pure_real_span (G := G) (d := d)).trans (span_le.mpr Hs)
  let b1 : Module.Basis s ℂ (Label G d) := Module.Basis.mk (show LinearIndependent ℂ (Subtype.val : s → _) from
    Hli.linearIndependent_restrict) (by simpa using Hsp)
  haveI : Finite s := Module.Finite.finite_basis b1
  letI := Fintype.ofFinite s
  let si : s := ⟨unit G d,hPs he⟩
  have hm : Nonempty s := ⟨si⟩
  let n := Fintype.card s - 1
  have hk : Fintype.card s = n+1 := by dsimp [n]; have := Fintype.card_pos_iff.mpr hm; omega
  let f : s ≃ Fin (n+1) := (Fintype.equivFin s).trans (finCongr hk)
  let j := f.trans (Equiv.swap (f si) 0)
  let B := b1.reindex j
  have hu (x : s) : b1 x = x.val := by simp [b1]
  have ha (x : s) : B (j x) = x.val := by simp [B, hu]
  have hv (i) : B i ∈ pureReal G d := by obtain ⟨x,rfl⟩ := j.surjective i; rw [ha]; exact hs x.property
  choose p hb hh using fun k : Fin (n+1) => (hv k).2
  have hed : j si = 0 := by simp [j]
  refine ⟨⟨n,B,hed ▸ ha si,p,fun i ↦ (hv i).1,hb,hh⟩,fun x hx ↦ ?_⟩
  exact ⟨j ⟨x,hPs hx⟩, ha _⟩

theorem frame_exists (G : Gauge) (d) : Nonempty (Frame G d) := by
  obtain ⟨X,-⟩ := extend_subset (P := ({unit G d}))
    ((linearIndepOn_singleton_iff ..).mpr unit_not_zero) (Set.singleton_subset_iff.mpr pure_unit) (by simp)
  exact ⟨X⟩

lemma extend_frame (X : Frame G d) : ∃ Y : Frame G (d+1),
    range ((raiseLabel G d.le_succ) ∘ X.basis) ⊆ range Y.basis := by
  let v : Fin (X.extra+1) → Label G (d+1) := (raiseLabel G d.le_succ) ∘ X.basis
  apply extend_subset (P := range v)
  · have e : LinearIndependent ℂ v := LinearIndependent.map' X.basis.linearIndependent _
      (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective _))
    exact e.linearIndepOn_id
  · rintro x ⟨m, hm⟩
    subst x
    refine ⟨Subtype.ext ?_, X.grades m, (X.bound m).trans d.le_succ, ?_⟩
    · exact congr_arg (fun x : Label G d => x.val) (X.realForm m)
    exact X.pure m
  exact ⟨0,by simp [v, X.starts_unit]; rfl⟩

structure Frames (G : Gauge) where
  level (d : ℕ) : Frame G d
  coherent d : range ((raiseLabel G d.le_succ) ∘ (level d).basis) ⊆ range (level (d+1)).basis

/-- Choice of coherent system; users can supply any one, the same at all cutoffs. -/
def frames (G : Gauge) : Frames G :=
  let u := Nat.rec (motive := fun d => Frame G d) (Classical.choice (frame_exists G 0))
    (fun _ m => (extend_frame m).choose)
  { level := u
    coherent := fun d => (extend_frame (u d)).choose_spec }
end YM.Labels
