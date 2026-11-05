import YM.Bid.Loan
import YM.Next.WARD_BIN.Deposit
import YM.Next.WARD_BIN.Eqs
import YM.Next.WARD_BIN.Wheels

/-!
# Carrying same singleton label every ancestor

Gas permutation and actual density push with embedded shifts, including on
planes/seams. Uses pointwise positivity. Add panel compression transport but
does *not* identify different Histories by their supports/shapes/norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Wheels
open Function MeasureTheory Lattice Wilson RG Gas Topology
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {k m p N : ℕ} {S : Levels G} {H : History G} (s : Signed)

lemma gravity (h : H.Selected) (hm : m ≤ N) (U : Config G (H.S.side m p)) : 0<(H.rep N p m).eval U := by
  induction hm using Nat.decreasingInduction with
  | self => rw [(h.starts N p).2]; exact Real.exp_pos _
  | of_succ i hi ih =>
    let Q := H.levels.clock.op i p
    let b := H.β N p (i+1)
    have he (u : Config G (H.S.side (i+1) p)) : ∃ t,0<Q.likelihood u t := by
      by_contra! hp
      have hh := Q.chosen (H.levels.blocks i p).branches u
      rw [Finset.sum_eq_zero (fun j _ => le_antisymm (hp j) (Q.likelihood_pos u j))] at hh; exact zero_ne_one hh
    have hz (u : Config G (H.S.side (i+1) p)) (t) : 0<Q.noise b (Q.prediction u t) U := Finset.prod_pos
      fun j _ => mul_pos (inv_pos.mpr (Q.penaltyZ_pos b)) (Real.exp_pos _)
    let v := (H.rep N p (i+1)).eval
    let g (u) := Q.density b u U • v u
    have hp (u : Config G (H.S.side (i+1) p)) : 0<g u := by
      obtain ⟨t,ht⟩ := he u
      exact mul_pos (Finset.sum_pos' (fun j _ => mul_nonneg (Q.likelihood_pos u j) (hz _ _).le) ⟨t,Finset.mem_univ t,mul_pos ht (hz u _)⟩) (ih u)
    have hh := (h.represents _ p _ hi).good
    rw [(h.steps N p i hi).1]; change 0<∫ u,g u ∂_
    apply (integral_pos_iff_support_of_nonneg (fun v => (hp v).le) (StepData.push_slice (H.levels.transition_mass ..)
      U _ (((H.rep N p _).envelope hh).integrable _))).2; rw [show support g=Set.univ from Set.eq_univ_of_forall fun x => (hp x).ne']; simp



lemma embedding_pull (b : Site n) : MeasurableEmbedding (pull s b (K:=G.El)) := by
  refine ((Wilson.continuous_pull s b).isClosedEmbedding (fun U V he => ?_)).measurableEmbedding
  funext i
  obtain ⟨j,rfl⟩ := (sending s b).surjective i
  have ht := congr_fun he j
  rw [pull_by, pull_by] at ht; split at ht
  · exact inv_injective ht
  exact ht
lemma turn_push {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : Config G (S.S.side (m+1) p)→ X) (β : ℝ) (V : Config G (S.S.side m p)) (b : Site (S.S.side m p)) :
    (S.clock.op m p).push β f (pull s b V) = (S.clock.op m p).push β (f ∘ pull s ((S.clock.op m p).ratio.embed b)) V := by
  unfold StepData.push
  rw [← (prior_pull s ((S.clock.op m p).ratio.embed b) (G:=G)).integral_comp (embedding_pull s ((S.clock.op m p).ratio.embed b) (G:=G))]
  simp_rw [(S.blocks m p).symmetric]; rfl


lemma rep_spins (h : H.Selected) (hm : m ≤ N) (U : Config G (H.S.side m p)) (b : Site (H.S.side m p)) : (H.rep N p m).eval (pull s b U) = (H.rep N p m).eval U := by
  induction hm using Nat.decreasingInduction with
  | self => rw [(h.starts N p).2]; unfold bare; rw [energy_pull]
  | of_succ i hi ih =>
    rw [(h.steps N p i hi).1,turn_push]
    rw [show (H.rep N p (i+1)).eval ∘ pull s ((H.levels.clock.op i p).ratio.embed b)=(H.rep N p (i+1)).eval from
      funext fun U => ih U _]

section Parts
open Finset
variable {A : Activities G n} {b : Site n} {s : Signed} (J : A.Moves s b) (U : Config G n)
def yacht (e : Equiv.Perm (Site n)) (q : Shape n) : Shape n :=
  ⟨((wall q).image e,(inv q).image e),(present q).image _, image_subset_image (grows _)⟩
def bay (e : Equiv.Perm (Site n)) : Equiv.Perm (Shape n) :=
  { toFun := yacht e, invFun := yacht e.symm, left_inv := by
      intro i; apply Subtype.ext; dsimp only [yacht,wall,inv]; simp [image_image], right_inv := by
      intro i; apply Subtype.ext; dsimp only [yacht,wall,inv]; simp [image_image] }
lemma sails (j : ℕ) : shape A (J.kp j)=bay (aerial s b) (shape A j) :=
  Subtype.ext (Prod.ext (J.forced_support j) (J.forced_inventory j))

include J in
lemma row (i : Shape n) : vacuum A U (bay (aerial s b) i) = vacuum A (pull s b U) i := by
  unfold vacuum bucket; rw [← Equiv.tsum_eq J.kp]; refine tsum_congr fun j => ?_; simp only [J.valuesK,sails,Equiv.apply_eq_iff_eq]
lemma shape_images {D : Type*} {u : Equiv.Perm (Site n)} {Z : Type*} {F : D ≃ Z} (f : D→Support n) (g : Z→Support n) (h : ∀ i, g (F i)=(f i).image u) (B : Finset D) :
    (B.map F.toEmbedding).biUnion g=(B.biUnion f).image u := by
  ext j
  simp only [mem_biUnion,mem_map,Equiv.coe_toEmbedding,mem_image]
  constructor
  · rintro ⟨_,⟨i,hi,rfl⟩,hh⟩; rw [h] at hh; obtain ⟨v,hv,rfl⟩ := mem_image.mp hh; exact ⟨_,⟨_,hi,hv⟩,rfl⟩
  rintro ⟨_,⟨i,hi,H⟩,rfl⟩
  exact ⟨_,⟨i,hi,rfl⟩,(h i).symm ▸ mem_image_of_mem _ H⟩
lemma pairwise_map {D : Type*} {Z : Type*} {F : D ≃ Z} {u : Equiv.Perm (Site n)} (f : D→Support n) (g : Z→Support n) (h : ∀ i,g (F i)=(f i).image u) (B : Finset D) :
    (↑(B.map F.toEmbedding):Set Z).PairwiseDisjoint g ↔ (B:Set D).PairwiseDisjoint f := by
  constructor
  · intro he i hi j hj H
    apply (disjoint_image u.injective).mp; rw [← h, ← h]
    exact he (mem_map_of_mem _ hi) (mem_map_of_mem _ hj) (F.injective.ne H)
  intro he i hi j hj H; obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi; obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hj
  change Disjoint (g (F a)) (g (F b)); rw [h,h,disjoint_image u.injective]; exact he ha hb (fun h => H (congr_arg _ h))
lemma admitted (p : BudgetPoint) (B : Finset ℕ) : A.admissible p U (B.map J.kp.toEmbedding) ↔ A.admissible p (pull s b U) B := by
  let f := fun i => (A.forced i).support
  let g := fun i => (A.forced i).inventory
  change ((↑(B.map J.kp.toEmbedding) : Set ℕ).PairwiseDisjoint f ∧ (B.map J.kp.toEmbedding).biUnion g=_) ↔ ((B:Set ℕ).PairwiseDisjoint f ∧ B.biUnion g=_)
  rw [pairwise_map f f (u:=aerial s b) J.forced_support,shape_images g g (u:=aerial s b) J.forced_inventory]
  conv_lhs => rw [← Work.H03.flags_send s b p.threshold]
  simp only [(show affine s b=⇑(aerial s b) from rfl), (image_injective (aerial s b).injective).eq_iff]
lemma occurs (p : BudgetPoint) (B : Finset ℕ) : A.gasOccurrence p (J.kp.finsetCongr B) U=A.gasOccurrence p B (pull s b U) := by
  unfold Activities.gasOccurrence; rw [Equiv.finsetCongr_apply,admitted J]
  split_ifs
  · rw [prod_map]; exact prod_congr rfl fun i _ => J.valuesK i U
  rfl
include J in
lemma gassing (p : BudgetPoint) : A.gas p (pull s b U) = A.gas p U := by
  unfold Activities.gas; nth_rw 2 [← Equiv.tsum_eq (Equiv.finsetCongr J.kp)]; exact tsum_congr fun i => (occurs J U p i).symm
lemma prices_steady (s : Signed) (h : H.Selected) {m} (hm : m ≤ N) (U : Config G (H.S.side m p)) (b : Site (H.S.side m p)) :
    let P := H.rep N p m
    Real.exp (P.exponent (pull s b U))=Real.exp (P.exponent U) := by
  intro P; obtain ⟨J⟩ := (h.represents N p m hm).good.labels.moves s b
  have he : P.activities.gas P.p U ≠ 0 := fun hn => (gravity h hm U).ne' (by change Real.exp _*P.activities.gas P.p U=_; rw [hn,mul_zero])
  apply mul_right_cancel₀ he
  conv_lhs => rw [← gassing J]
  exact rep_spins s h hm U b

lemma aisle_port {e : Equiv.Perm (Site n)} {X : Support n} {i : Shape n} (t : Finset (Shape n)) :
    t.map (bay e).toEmbedding ∈ aisle (X.image e) (bay e i) ↔ t ∈ aisle X i := by
  let Z := bay e
  have ht (t : Shape n) : wall (Z t) = (wall t).image e := rfl
  have he (t : Shape n) : inv (Z t)=(inv t).image e := rfl
  have Ht : ∀ l : Shape n,(X.image e∩wall (Z l)).Nonempty ↔ (X∩wall l).Nonempty := by
    intro i; rw [ht, ← image_inter _ _ e.injective, image_nonempty]
  simp only [aisle,mem_filter,mem_univ,true_and, map_nonempty]
  rw [pairwise_map wall wall ht,shape_images wall wall ht,shape_images inv inv he]
  change (_∧_ ∧ _ ∧ _=wall (Z i) ∧ _=inv (Z i)) ↔ _
  rw [ht,he,← image_union, (image_injective e.injective).eq_iff,(image_injective e.injective).eq_iff]
  unfold Z at Ht
  simp only [Finset.forall_mem_map,Equiv.coe_toEmbedding,Ht]


-- The walk around all pads, with eligibility carried. None discarded.
include J in
lemma hop_rot (r : Bool) (Y : Support n) (p : BudgetPoint) (d : Config G n→ℂ) (i : Shape n) :
    turn r (hop A p Y d i (pull s b U))=hop A p (Y.image (affine s b)) (turn r ∘ d ∘ pull s b) (bay (aerial s b) i) U := by
  unfold hop Gas.tag
  let Z := aerial s b
  let e := bay Z
  have he : wall (bay (aerial s b) i) ∩ flags p.threshold U=inv (bay (aerial s b) i) ↔ wall i∩flags p.threshold (pull s b U)=inv i := by
    change ((wall i).image (affine s b) ∩ _ = (inv i).image ⇑Z) ↔ _
    rw [sampling]; exact (image_injective Z.injective).eq_iff
  simp only [he]; split_ifs
  · have hH : aisle (Y.image (affine s b)) (e i)=(aisle Y i).map (e.finsetCongr.toEmbedding) := by
      ext l; obtain ⟨l,rfl⟩ := e.finsetCongr.surjective l
      rw [mem_map_equiv,Equiv.symm_apply_apply]; exact aisle_port (e:=aerial s b) (X:=Y) (i:=i) l
    have hB (y : Finset (Shape n)) : (∏ j∈y,vacuum A (pull s b U) j)=∏ j ∈ e.finsetCongr y,vacuum A U j := by
      rw [Equiv.finsetCongr_apply,prod_map]; exact prod_congr rfl fun j _ => (row J U j).symm
    simp only [turn_mul, comp_apply]
    apply congr_arg (turn r _ * ·)
    simp_rw [← Complex.ofReal_prod, ← Complex.ofReal_sum]
    rw [turn_real,hH,sum_map]; congr 1; exact sum_congr rfl fun i _ => hB i
  rw [turn_zero]
end Parts
end YM.WardBin.Wheels
