import YM.Next.FOUNDATIONS.SU2
import YM.Push.LOCAL_SPLITTING.Merge

/-!
# Exact singleton recovery after indicator moves

Bijection on the nonzero pointed products in the existing forced alphabet.
No duplicates, no independent-gas assumption, no absolute value inside the
represented insertion. Eligibility and exact coverage even for evaluated
functions (not AE). Auxiliary series guarded by HasSum/Dominated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side} {ι : Type*}

abbrev Pointed := Σ b : Finset ℕ, ↥b

def pointValue (B : BudgetPoint) (A : Activities G n) (f : ℕ → Config G n → ℂ) (U : Config G n) (x : Pointed) :=
  if A.admissible B U x.1 then f x.2.val U * ∏ j∈ x.1.erase x.2.val, (A.K j U : ℂ) else 0

def gasMark (B : BudgetPoint) (A : Activities G n) (U : Config G n) (b : Finset ℕ) : (ℕ → Config G n → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i∈b, (if A.admissible B U b then ∏ j∈b.erase i, (A.K j U : ℂ) else 0) •
    ((LinearMap.proj (R:=ℂ) (φ:=fun _: Config G n => ℂ) U) ∘ₗ (LinearMap.proj (R:=ℂ) (φ:=fun _ : ℕ => Config G n → ℂ) i))

theorem gasMark_eq (B : BudgetPoint) (A : Activities G n) (U : Config G n) (b : Finset ℕ) (f : ℕ → Config G n → ℂ) :
    gasMark B A U b f = if A.admissible B U b then ∑ i∈b, f i U * ∏ j∈b.erase i, (A.K j U : ℂ) else 0 := by
  by_cases h : A.admissible B U b <;> simp [gasMark,h,mul_comm]

theorem gasMark_point (B : BudgetPoint) (A : Activities G n) (U : Config G n) (b : Finset ℕ) (f : ℕ → Config G n → ℂ) :
    (∑ i : ↥b, pointValue B A f U ⟨b,i⟩) = gasMark B A U b f := by
  by_cases h : A.admissible B U b <;> simp only [pointValue,gasMark_eq,h,↓reduceIte]
  exact b.sum_coe_sort (fun i => f i U * ∏ j∈b.erase i, (A.K j U : ℂ))
  simp

theorem dominated_gasMark {B : BudgetPoint} {A : Activities G n} {f : ℕ → Config G n → ℂ} {a w : ℝ} (hf : ForceCost B A f a)
    (hw : A.KBound B w) : Dominated (fun b (U : Config G n) => gasMark B A U b f) := by
  obtain ⟨k,hk,h⟩ := hf; obtain ⟨z,hz,hZ⟩ := Activities.K_total hw
  let g (i : ℕ) := k i+z i
  have he : Summable g := ((sumBudget_uncharge (fun i => (h i).1) hk).2.1).add hz
  have hp i : 0 ≤ g i := add_nonneg (h i).1 (hZ i).1
  refine ⟨_, summable_finsetProd_of_summable_nonneg (f:=fun i => 2*g i) (fun i => mul_nonneg (by norm_num) (hp i)) (he.mul_left 2), ?_⟩
  intro b U; dsimp only; rw [gasMark_eq]; split
  · apply (norm_sum_le ..).trans
    have H (i) (hi : i∈b) : ‖f i U * ∏ j∈b.erase i, (A.K j U : ℂ)‖ ≤ ∏ j∈b, g j := by
      rw [← Finset.mul_prod_erase b g hi,norm_mul,norm_prod]; refine mul_le_mul (((h i).2 U).trans (le_add_of_nonneg_right (hZ _).1)) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hp i)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (Complex.norm_real _).trans_le (((hZ i).2 U).trans (le_add_of_nonneg_left (h i).1))
    apply (Finset.sum_le_sum H).trans; rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n:=b.card)).le) (Finset.prod_nonneg fun i _ => hp i)
  rw [norm_zero]; exact Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hp i)

namespace Slots
variable {A : Activities G n} {X : ι → Support n} (S : Slots A X)

def hits (T : Support n) (b : Finset ℕ) (A : Activities G n) := b.filter (fun i => ¬ Disjoint T (patch A i))

def Matches (x : Pointed) (y : ι × Finset ℕ) := ∃ s : Letters A X, s.1 = y.1 ∧ S.label s = x.2.val ∧
  y.2 = s.bundle ∪ x.1.erase x.2.val ∧ s.bundle = hits (X y.1) y.2 A ∧ Disjoint s.bundle (x.1.erase x.2.val)

theorem Matches.uniq {x : Pointed} {y y' : ι × Finset ℕ} (h : S.Matches x y) (he : S.Matches x y') : y = y' := by
  obtain ⟨s,h,hv,ha,_⟩ := h; obtain ⟨s',h',hv',ha',_⟩ := he
  have hq : s = s' := S.label.injective (hv.trans hv'.symm)
  subst s'; exact Prod.ext (h.symm.trans h') (ha.trans ha'.symm)

theorem Matches.uniq' {x x' : Pointed} {y : ι × Finset ℕ} (h : S.Matches x y) (he : S.Matches x' y) : x = x' := by
  obtain ⟨s,h,hv,ha,hb,hd⟩ := h; obtain ⟨s',h',hv',ha',hb',hd'⟩ := he
  have hq : s = s' := Sigma.ext (h.trans h'.symm) (by cases s; cases s'; cases h.trans h'.symm; exact heq_of_eq (Subtype.ext (hb.trans hb'.symm)))
  subst s'
  have hrest := (Finset.union_sdiff_cancel_left hd).symm.trans ((congr_arg (· \ s.bundle) (ha.symm.trans ha')).trans (Finset.union_sdiff_cancel_left hd'))
  have hx : x.1 = x'.1 := (Finset.insert_erase x.2.property).symm.trans ((congr_arg₂ _ (hv.symm.trans hv') hrest).trans (Finset.insert_erase x'.2.property))
  exact Sigma.ext hx (by cases x; cases x'; cases hx; exact heq_of_eq (Subtype.ext (hv.symm.trans hv')))

section Eq
variable (B : BudgetPoint) (U : Config G n) (f : ι → Config G n → ℂ)

theorem approved {x : Pointed} {s : Letters A X} (he : A.admissible B U x.1) (hx : x.2.val = S.label s) : (A.forced (S.label s)).eligible B.threshold U := by
    refine ⟨?_, S.allows _ _⟩
    rw [← he.2, ← hx]
    ext z; rw [Finset.mem_inter]; constructor
    · rintro ⟨hz,hz'⟩; obtain ⟨j,hj,hu⟩ := Finset.mem_biUnion.mp hz'
      by_cases h : j = x.2.val
      · simpa only [h] using hu
      exact absurd ((A.forced j).inventory_sup hu) (Finset.disjoint_left.mp (he.1 x.2.property hj (Ne.symm h)) hz)
    exact fun hz => ⟨(A.forced _).inventory_sup hz,Finset.mem_biUnion.mpr ⟨_,x.2.property,hz⟩⟩
private theorem match_value {x : Pointed} {s : Letters A X} (he : A.admissible B U x.1) (hx : x.2.val = S.label s) {q : Finset ℕ}
    (ha : A.admissible B U q) (hq : q = s.bundle ∪ x.1.erase x.2.val) (hd : Disjoint s.bundle (x.1.erase x.2.val)) :
    pointValue B A (S.pack B.threshold f) U x = f s.1 U * (A.gasOccurrence B q U : ℂ) := by
  have hg : (A.forced (S.label s)).eligible B.threshold U := by
    exact S.approved B U he hx
  rw [pointValue, if_pos he, hx, pack_label, payload, if_pos hg, Activities.gasOccurrence, if_pos ha,Complex.ofReal_prod,hq,Finset.prod_union hd,hx,mul_assoc]

theorem unpack {x : Pointed} {s : Letters A X} (he : A.admissible B U x.1) (hs : S.label s = x.2.val) :
    let y := (s.1,s.bundle∪x.1.erase x.2.val)
    A.admissible B U y.2 ∧ S.Matches x y ∧ Disjoint s.bundle (x.1.erase x.2.val) := by
  let r := x.1.erase x.2.val
  have hD j (hj : j∈r) : Disjoint s.total (patch A j) := (S.support s).symm ▸ he.1 (hs ▸ x.2.property) (Finset.mem_of_mem_erase hj) (hs ▸ (Finset.ne_of_mem_erase hj).symm)
  have hd : Disjoint s.bundle r := Finset.disjoint_left.mpr fun j hj hr => s.2.property.hits _ hj (Finset.disjoint_union_left.mp (hD _ hr)).1
  have ha : A.admissible B U (s.bundle ∪ r) := by
    refine ⟨?_,?_⟩
    · change Separate A _; rw [Separate,Finset.coe_union]; exact s.2.property.separate.union ((show Separate A x.1 from he.1).subset (Finset.coe_subset.mpr (Finset.erase_subset _ _))) fun i hi j hj _ => Finset.disjoint_of_subset_left (s.contains hi) (hD j hj)
    rw [← he.2]; conv_rhs => rw [← Finset.insert_erase x.2.property]
    rw [Finset.biUnion_insert, Finset.union_biUnion]; exact congr_arg (· ∪ _) ((S.inventory s).symm.trans (congr_arg (flagsFor A) hs))
  refine ⟨ha,⟨s,rfl,hs,rfl,?_,hd⟩,hd⟩
  unfold hits; simp only [Finset.filter_union]
  have hr {i} (hi : i∈r) := not_not.mpr (Finset.disjoint_union_left.mp (hD i hi)).1
  rw [Finset.filter_eq_empty_iff.mpr @hr, Finset.union_empty]
  exact (Finset.filter_true_of_mem s.2.property.hits).symm

private theorem from_point {x : Pointed} (h : pointValue B A (S.pack B.threshold f) U x ≠ 0) :
    ∃ y : ι × Finset ℕ, S.Matches x y ∧ pointValue B A (S.pack B.threshold f) U x = f y.1 U * (A.gasOccurrence B y.2 U : ℂ) := by
  have he : A.admissible B U x.1 := by contrapose! h; simp [pointValue,h]
  obtain ⟨s,hs⟩ : ∃ s, S.label s = x.2.val := by by_contra hn; simp [pointValue, S.pack_none _ _ _ hn] at h
  obtain ⟨ha,hq,hd⟩ := S.unpack B U he hs
  exact ⟨_,hq, S.match_value B U f he hs.symm ha rfl hd⟩

theorem pack_admissible {q : Finset ℕ} (ha : A.admissible B U q) (i : ι) (hN : (hits (X i) q A).Nonempty) :
    ∃ x : Pointed, A.admissible B U x.1 ∧ S.Matches x (i,q) := by
  let u := hits (X i) q A
  have hsub : u ⊆ q := Finset.filter_subset _ _
  have hP : Packs A (X i) u := by
    refine ⟨hN,(show Separate A q from ha.1).subset (Finset.coe_subset.mpr hsub),fun j hj => (Finset.mem_filter.mp hj).2⟩
  let s : Letters A X := ⟨i,⟨u,hP⟩⟩
  let r := q \ u
  have hun : u ∪ r = q := Finset.union_sdiff_of_subset hsub
  have he j (hj : j∈r) : Disjoint (patch A (S.label s)) (patch A j) := by
    obtain ⟨hq,hu⟩ := Finset.mem_sdiff.mp hj
    rw [S.support,Letters.total,Finset.disjoint_union_left,Finset.disjoint_biUnion_left]
    exact ⟨not_not.mp fun he => hu (Finset.mem_filter.mpr ⟨hq,he⟩),fun k hk => ha.1 (hsub hk) hq (fun hh => hu (hh ▸ hk))⟩
  have hnew : S.label s ∉ r := fun h => by
    obtain ⟨x,hx⟩ := (A.forced (S.label s)).inventory_ne.mono (A.forced _).inventory_sup
    exact Finset.disjoint_left.mp (he _ h) hx hx
  have had : A.admissible B U (insert (S.label s) r) := by
    constructor
    · intro j hj k hk hjk
      obtain h|h := Finset.mem_insert.mp hj <;> obtain h'|h' := Finset.mem_insert.mp hk
      · exact absurd (h.trans h'.symm) hjk
      · exact h ▸ he _ h'
      · exact h' ▸ (he _ h).symm
      exact ha.1 (Finset.mem_sdiff.mp h).1 (Finset.mem_sdiff.mp h').1 hjk
    rw [← ha.2,← hun,Finset.union_biUnion,Finset.biUnion_insert]; exact congr_arg (· ∪ _) (S.inventory s)
  let x : Pointed := ⟨insert (S.label s) r, ⟨_,Finset.mem_insert_self (S.label s) r⟩⟩
  have hx : x.1.erase x.2.val = r := Finset.erase_insert hnew
  have hd : Disjoint s.bundle (x.1.erase x.2.val) := hx.symm ▸ Finset.disjoint_sdiff
  have hq : q = s.bundle ∪ x.1.erase x.2.val := hx.symm ▸ hun.symm
  exact ⟨x,had,⟨s,rfl,rfl,hq,rfl,hd⟩⟩

private theorem to_point (hf : ∀ i, Attaches B.threshold (X i) (f i)) (y : ι × Finset ℕ) (hy : f y.1 U * (A.gasOccurrence B y.2 U : ℂ) ≠ 0) :
    ∃ x : Pointed, S.Matches x y ∧ pointValue B A (S.pack B.threshold f) U x = f y.1 U * (A.gasOccurrence B y.2 U : ℂ) := by
  obtain ⟨i,q⟩ := y
  have ha : A.admissible B U q := by by_contra hn; simp [Activities.gasOccurrence,hn] at hy
  have hN : (hits (X i) q A).Nonempty := by
    have h : ¬ Healthy B.threshold (X i) U := fun he => hy (by simp [(hf i).healthy_zero _ he])
    obtain ⟨x,hx,hx'⟩ := Finset.not_disjoint_iff.mp h
    rw [← ha.2] at hx'; obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp hx'
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, Finset.not_disjoint_iff.mpr ⟨_,hx,(A.forced j).inventory_sup he⟩⟩⟩
  obtain ⟨x,he,hM⟩ := S.pack_admissible B U ha i hN
  obtain ⟨s,h1,h2,h3,-,hd⟩ := id hM
  exact ⟨x, hM, (S.match_value B U f he h2.symm ha h3 hd).trans (by rw [h1])⟩

theorem point_hasSum_iff (hf : ∀ i, Attaches B.threshold (X i) (f i)) (c : ℂ) :
    HasSum (pointValue B A (S.pack B.threshold f) U) c ↔ HasSum (fun y : ι × Finset ℕ => f y.1 U * (A.gasOccurrence B y.2 U : ℂ)) c := by
  let g := pointValue B A (S.pack B.threshold f) U
  let h := fun y : ι × Finset ℕ => f y.1 U * (A.gasOccurrence B y.2 U : ℂ)
  choose y hy hy' using fun x : Function.support g => S.from_point B U f (x:=x.val) x.property
  let M (x : Function.support g) : Function.support h := ⟨y x,fun he => x.property ((hy' x).trans he)⟩
  have hi : Injective M := by
    intro x x' H; have H' : y x = y x' := congr_arg Subtype.val H
    exact Subtype.ext ((hy x).uniq' S (H' ▸ hy x'))
  have hs : Surjective M := by
    rintro ⟨z,hz⟩; obtain ⟨x,hx,he⟩ := S.to_point B U f hf z hz
    let t : Function.support g := ⟨x, fun ha => hz (he.symm.trans ha)⟩
    exact ⟨t, Subtype.ext ((hy t).uniq S hx)⟩
  exact (Equiv.ofBijective M ⟨hi, hs⟩).hasSum_iff_of_support (fun x => (hy' x).symm)

private theorem mul_hasSum {κ : Type*} {u : ι → ℂ} {v : κ → ℂ} (h : Summable fun i => ‖u i‖)
    (hv : Summable fun j => ‖v j‖) {z : ℂ} (he : HasSum v z) : HasSum (fun x : ι × κ => u x.1 * v x.2) ((∑' i, u i)*z) :=
  h.of_norm.hasSum.mul he (summable_mul_of_summable_norm h hv)

/-- Multiply the sum of attaching terms by the vacuum gas, retaining all
predicates. No forking or altering `A`. Complex signs permitted. -/
theorem recover (hf : ∀ i, Attaches B.threshold (X i) (f i)) {δ w : ℝ} (ha : A.Valid B δ w) (he : Summable fun i => ‖f i U‖) :
    HasSum (fun b => gasMark B A U b (S.pack B.threshold f)) ((∑' i, f i U)*(A.gas B U : ℂ)) := by
  have hz : Summable fun i => ‖(A.gasOccurrence B i U : ℂ)‖ := by simp_rw [Complex.norm_real]; exact (Activities.gasSeries ha).absolute U
  have ht : HasSum (fun i => (A.gasOccurrence B i U : ℂ)) (A.gas B U : ℂ) := Complex.hasSum_ofReal.mpr ((Activities.gasSeries ha).summable U).hasSum
  have hpoint : HasSum (pointValue B A (S.pack B.threshold f) U) _ := (S.point_hasSum_iff B U f hf _).2 (mul_hasSum he hz ht)
  have hs (b : Finset ℕ) : HasSum (fun i : ↥b => pointValue B A (S.pack B.threshold f) U ⟨b,i⟩) (gasMark B A U b (S.pack B.threshold f)) := by
    rw [← gasMark_point]; exact hasSum_fintype _
  exact hpoint.sigma hs
end Eq
end Slots
end YM.Push.Local
