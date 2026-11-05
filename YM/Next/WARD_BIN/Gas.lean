import YM.Ac.Table
import YM.RG.ActivityBounds

/-!
# Compressing the exact gas by geometric shape (for  merging)

Compression for proofs of signed **coefficients**, also with inhomogeneous
square-zero weights. Doesn't change the actual history/extraTest. Several
labels with same shape are permitted, but cannot be selected simultaneously
(nonempty primary inventory).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Gas
open Function Finset Filter Lattice Wilson RG
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}

/-- The supports in evaluations; not the full `inspected` read footprint. -/
abbrev Shape (n : Side) := {x : Support n × Support n // x.2.Nonempty ∧ x.2 ⊆ x.1 }

abbrev wall (p : Shape n) := p.val.1
abbrev inv (p : Shape n) := p.val.2
abbrev shape (A : Activities G n) (i : ℕ) : Shape n :=
  ⟨((A.forced i).support,(A.forced i).inventory),(A.forced i).inventory_ne,(A.forced i).inventory_sup⟩
lemma grows (p : Shape n) : inv p ⊆ wall p := p.property.2
lemma present (p : Shape n) : (inv p).Nonempty := p.property.1
lemma mentions (p : Shape n) : (wall p).Nonempty := (present p).mono (grows p)

variable {I R : Type*}

structure Holds (x : I → Shape n) (M : Support n) (b : Finset I) : Prop where
  disj : (b : Set I).PairwiseDisjoint (wall ∘ x)
  flags : b.biUnion (inv ∘ x) = M

namespace Holds
variable {x : I → Shape n} {M : Support n} {b : Finset I} (h : Holds x M b)
include h
lemma gain : Set.InjOn x ↑b := by
  intro i hi j hj he
  by_contra hn
  have hh : Disjoint (wall (x i)) (wall (x j)) := h.disj hi hj hn
  change x i=x j at he
  rw [he, disjoint_self] at hh; exact (mentions _).ne_empty hh

lemma image : Holds id M (b.image x) := by
  constructor
  · intro i hi j hj hn
    obtain ⟨i,ha,rfl⟩ := mem_image.mp hi; obtain ⟨j,hb,rfl⟩ := mem_image.mp hj
    exact h.disj ha hb (fun H => hn (congr_arg x H))
  rw [← h.flags]; ext i; simp

lemma owns {i} (hi : i∈b) : wall (x i) ∩ M=inv (x i) := by
  ext k; rw [← h.flags]
  constructor
  · intro H
    obtain ⟨he,j,hj,h⟩ := (show _ ∧ ∃ j∈b,k∈inv (x j) from ⟨(mem_inter.mp H).1,mem_biUnion.mp (mem_inter.mp H).2⟩)
    by_cases hm : i=j
    · rwa [hm]
    rename_i h'
    exact False.elim (disjoint_left.mp (h'.disj hi hj hm) he (grows (x j) h))
  intro hx; exact mem_inter.mpr ⟨grows (x i) hx,mem_biUnion.mpr ⟨i,hi,hx⟩⟩
end Holds

section Compression
variable (x : I → Shape n) (M : Support n) [CommSemiring R] (f : I→R)

def occ (b : Finset I) := if Holds x M b then ∏ i∈b,f i else 0
def fest (M : Support n) (g : Shape n→R) := ∑ D : Finset (Shape n), occ id M g D

private lemma chooser (D : Finset I) (C : Finset (Shape n)) (hh : Holds id M C) :
    ∑ b ∈ ((D.powerset.filter (Holds x M)).filter (fun b => b.image x=C)), (∏ i∈b,f i)=
    ∏ q∈C, (∑ i∈D with x i=q, f i) := by
  let F (i : ↥C) := D.filter fun j => x j=i.val
  let H := (i : ↥C) → ↥(F i)
  let y (h : H) (i : ↥C) : I := (h i).val
  have hy (h : H) (i) : y h i ∈ D ∧ x (y h i)=i.val := by simpa only [F,mem_filter] using (h i).property
  have hj (h : H) : Injective (y h) := by
    intro i j he; apply Subtype.ext; exact (hy _ i).2.symm.trans ((congr_arg x he).trans (hy h j).2)
  let e (h : H) := univ.image (y h)
  have he (h : H) : Holds x M (e h) := by
    constructor
    · intro i hi j hz hn
      obtain ⟨i,_,rfl⟩ := mem_image.mp hi; obtain ⟨j,-,rfl⟩ := mem_image.mp hz
      change Disjoint (wall (x (y h i))) (wall (x (y h j))); rw [(hy h i).2,(hy h j).2]
      exact hh.disj i.property j.property (fun H => hn (congr_arg _ (Subtype.ext H)))
    rw [← hh.flags]; ext k; constructor
    · intro hk; obtain ⟨i,hi,H⟩ := mem_biUnion.mp hk
      obtain ⟨i,_,rfl⟩ := mem_image.mp hi; exact mem_biUnion.mpr ⟨_,i.property,(hy h i).2 ▸ (show k∈inv (x (y h i)) from H)⟩
    intro hk; obtain ⟨i,hi,hk⟩ := mem_biUnion.mp hk
    exact mem_biUnion.mpr ⟨y h ⟨i,hi⟩,mem_image_of_mem _ (mem_univ _), by
      change k∈inv (x (y h ⟨i,hi⟩)); rw [(hy h _).2]; exact hk⟩
  have hi (h : H) : (e h).image x=C := by
    ext q; constructor
    · intro hx; obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; obtain ⟨j,-,rfl⟩ := mem_image.mp hi
      rw [(hy h j).2]; exact j.property
    intro hq; exact mem_image.mpr ⟨_, mem_image_of_mem (y h) (mem_univ ⟨q,hq⟩), (hy h ⟨q,hq⟩).2⟩
  let W := ((D.powerset.filter (Holds x M)).filter (fun b => b.image x=C))
  rw [prod_subtype _ (show ∀ i : Shape n,i∈C ↔ i∈C from fun _ => Iff.rfl)]
  have hs (q : ↥C) : ∑ i∈F q, f i=∑ i : ↥(F q),f i.val := sum_subtype _ (fun _ => Iff.rfl) _
  change ∑ b∈W, _ = ∏ i : ↥C, ∑ j∈F i,f j
  simp_rw [hs]
  rw [Fintype.prod_sum]
  symm
  refine sum_bij (fun a _ => e a) (fun h _ => ?_) (fun a _ b _ he => ?_) (fun b hb => ?_) (fun a _ => ?_)
  · refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr ?_, he h⟩,hi h⟩
    rintro k hk; obtain ⟨i,-,rfl⟩ := mem_image.mp hk; exact (hy _ _).1
  · funext i; apply Subtype.ext
    have hz : y a i ∈ e b := he ▸ mem_image_of_mem _ (mem_univ i)
    obtain ⟨j,_,hj⟩ := (mem_image.mp hz : ∃ j∈univ,y b j=y a i)
    have hk : j=i := Subtype.ext ((hy b j).2.symm.trans ((congr_arg x hj).trans (hy a i).2))
    subst j; exact hj.symm
  · have HV := mem_filter.mp hb
    have hc := (mem_filter.mp HV.1)
    have hz : ∀ i : ↥C, ∃ j∈b, x j=i.val := fun i => mem_image.mp (HV.2.symm ▸ i.property)
    choose j hL hP using hz
    let y' (i : ↥C) : ↥(F i) := ⟨j i,mem_filter.mpr ⟨mem_powerset.mp hc.1 (hL i),hP i⟩⟩
    refine ⟨y',mem_univ _,?_⟩
    apply Subset.antisymm
    · intro k hk; obtain ⟨i,_,rfl⟩ := mem_image.mp hk; exact hL _
    intro k hk; let i : ↥C := ⟨x k,HV.2 ▸ (mem_image_of_mem x hk)⟩
    exact mem_image.mpr ⟨i,mem_univ _,hc.2.gain (hL i) hk (hP i)⟩
  change _=∏ i∈ univ.image (y a), f i; rw [prod_image (hj a).injOn]

theorem fold (D : Finset I) : (∑ b∈D.powerset, occ x M f b)=fest M (fun q => ∑ i∈D, if x i=q then f i else 0) := by
  unfold occ fest
  rw [← sum_filter (Holds x M), ← sum_fiberwise _ (fun b => b.image x)]
  apply sum_congr rfl; intro C _; unfold occ
  split_ifs with h
  · simp_rw [← sum_filter]; exact chooser x M f D C h
  exact sum_eq_zero fun b hb => False.elim (h ((mem_filter.mp hb).2 ▸ (mem_filter.mp (mem_filter.mp hb).1).2.image))

variable [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R] [T2Space R]

theorem series (hc : Summable (occ x M f)) (hs : ∀ q, Summable fun i => if x i=q then f i else 0) :
    (∑' b, occ x M f b) = fest M (fun q => ∑' i,if x i=q then f i else 0) := by
  classical
  let E (D : Finset I) := ∑ b∈D.powerset, occ x M f b
  have ht : Tendsto E atTop (𝓝 (∑' b, occ x M f b)) := hc.hasSum.comp tendsto_finset_powerset_atTop_atTop
  apply tendsto_nhds_unique ht
  dsimp only [E]
  simp_rw [fold]
  unfold fest
  refine tendsto_finsetSum _ fun C _ => ?_
  unfold occ
  by_cases h : Holds id M C
  · simp_rw [if_pos h]; exact tendsto_finsetProd _ fun q _ => (hs q).hasSum
  simp only [if_neg h]; exact tendsto_const_nhds
end Compression
section Actual
variable {p : BudgetPoint} {δ w : ℝ} (A : Activities G n)

lemma admissible_iff (U : Config G n) (b : Finset ℕ) :
    A.admissible p U b ↔ Holds (shape A) (flags p.threshold U) b :=
  ⟨fun H => ⟨H.1,H.2⟩,fun H => ⟨H.disj,H.flags⟩⟩

lemma vacc (U : Config G n) (b : Finset ℕ) :
    A.gasOccurrence p b U=occ (shape A) (flags p.threshold U) (fun i => A.K i U) b := by
  unfold Activities.gasOccurrence occ
  simp_rw [admissible_iff A U b]

lemma summable_ite {V Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y] {f : V→Y}
    (h : Summable f) (P : V → Prop) [DecidablePred P] : Summable (fun i => if P i then f i else 0) := by
  rw [show (fun i => if P i then f i else 0) = {i|P i}.indicator f from funext fun i => by simp [Set.indicator_apply]]
  exact h.indicator _

/-- Operator on coefficients only, confined to shell -- stashes actual flag
predicates in each input. -/
def bucket {Y : Type*} [TopologicalSpace Y] [AddCommMonoid Y] (f : ℕ → Y) (q : Shape n) :=
  ∑' i, if shape A i=q then f i else 0

def vacuum (U : Config G n) := bucket A (fun i => A.K i U)

lemma weights (h : A.KBound p w) : Dominated A.K := by
  obtain ⟨b,hb,h⟩ := Activities.K_total h
  exact ⟨b,hb,fun i => (h i).2⟩

lemma value (h : A.Valid p δ w) (U : Config G n) :
    A.gas p U = fest (flags p.threshold U) (vacuum A U) := by
  unfold Activities.gas
  simp_rw [vacc A]
  have hs := (weights A h.boundK).summable U
  refine series _ _ _ ?_ (fun i => summable_ite hs _)
  simpa only [vacc] using (Activities.gasSeries h).summable U
end Actual
end YM.WardBin.Gas
