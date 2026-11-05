import YM.Analysis.Polydisc
import YM.SectorNext.RECONNECTED_LOCALITY.Brochures
import YM.Work.E09


set_option warningAsError false

/-!
# Missing unforced clusters & failed masks/integrated halo attachments

Variant with one address per missing Rose (resp. correction) and
*identity-restoring* $e^x-1$ at that address, rather than terms from a
multiset expansion. Require every selected attachment to intersect the ORIGINAL
support of one selected d (when $x$ is a failed-mask potential, its failure
in a covered term already guarantees this; for the Rose address use exactly
this rule to detect clusters omitted in the pressure). Keep original disjointness,
coverage and *all* extra predicates within new connected components. Do not
turn overlaps of attachments with internal d into prior d incompatibilities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
open Function Filter RG Lattice Wilson Words MeasureTheory Finset
open scoped Classical

variable {G : Gauge} {c : Side} {ι β τ : Type*}

structure Riser (G : Gauge) (c : Side) (ι : Type*) where
  bank : ι → Support c
  solid i : (bank i).Nonempty
  call : ι → Config G c → ℝ

namespace Riser
variable (X : Riser G c ι) (D : Brand G c β) (P : BudgetPoint)

abbrev Letter (β ι : Type*) := β ⊕ ι
-- bank is attachment cost (complete support). B d already local on D.range incl final-read exceptions.
def scope (i : Letter β ι) := i.elim D.range X.bank
def flag (_X : Riser G c ι) (i : Letter β ι) := i.elim D.require (fun _ => (∅:Support c))

def phase (i : Letter β ι) (U : Config G c) : ℝ :=
    i.elim (fun i=>D.ink i U) (fun i=>Real.exp (X.call i U)-1)

def rawEligible (i : Letter β ι) (s : Finset (Letter β ι)) := i.elim
    (fun i => ∀ j∈s.toLeft,i≠j → Disjoint (D.range i) (D.range j))
    (fun i => ∃ j∈s.toLeft,¬Disjoint (X.bank i) (D.range j))

lemma live : Retained (X.scope D) (X.rawEligible D) := by
  have hx (i : Letter β ι) (s b : Finset (Letter β ι)) (h : ∀ l,¬Disjoint (X.scope D i) (X.scope D l) → (l∈s↔l∈b))
      (he : rawEligible X D i s) : rawEligible X D i b := by
    rcases i with i|i
    · intro j hj hn; by_contra hh
      have hx : Disjoint (D.range i) (D.range j) := he _ (Finset.mem_toLeft.mpr ((h (.inl j) hh).2 (Finset.mem_toLeft.mp hj))) hn
      exact hh hx
    obtain ⟨j,hj,hr⟩:= (show ∃ j∈s.toLeft, ¬Disjoint (X.bank i) (D.range j) from he)
    exact ⟨j, Finset.mem_toLeft.mpr ((h (.inl j) hr).1 (Finset.mem_toLeft.mp hj)),hr⟩
  intro i s b h; exact propext ⟨hx _ _ _ h, hx _ _ _ (fun l e => (h l e).symm)⟩

lemma covered (t : Letter β ι) : X.flag D t ⊆ X.scope D t := by
  cases t
  · exact (D.forced _).inventory_sup
  exact Finset.empty_subset _

lemma aboard (t : Letter β ι) : (X.scope D t).Nonempty := by cases t; exact D.active _; exact X.solid _

lemma key (s : Finset (Letter β ι)) : region (X.flag D) s=s.toLeft.biUnion D.require := by
  ext i
  simp only [region,Finset.mem_biUnion,Finset.mem_toLeft]
  constructor
  · rintro ⟨j,hj,H⟩; rcases j with j|j
    · exact ⟨j,hj,H⟩
    exact (Finset.notMem_empty i H).elim
  rintro ⟨j,hj,H⟩; exact ⟨.inl _,hj,H⟩

lemma orders (s : Finset (Letter β ι)) : permits (rawEligible X D) s ↔
    ((s.toLeft : Set β).PairwiseDisjoint D.range ∧ ∀ i∈s.toRight,∃ j∈s.toLeft, ¬Disjoint (X.bank i) (D.range j)) := by
  refine ⟨fun h => ⟨fun i hi j hj => (show ∀ k∈_,_ from h (.inl i) (mem_toLeft.mp hi)) j hj,fun i hi => h (.inr i) (mem_toRight.mp hi)⟩,?_⟩
  rintro ⟨h1,h2⟩ (i|i) hi
  · exact fun j hj => h1 (mem_toLeft.mpr hi) hj
  exact h2 i (mem_toRight.mpr hi)

abbrev Wagon := {s : Finset (Letter β ι) // Ac.Spark (X.scope D) s ∧ permits (rawEligible X D) s}

instance [Countable ι] [Countable β] : Countable (X.Wagon D) := by unfold Wagon; infer_instance

/-- Each merged address necessarily carries at least one OLD d occurrence. -/
theorem forced (s : X.Wagon D) : s.val.toLeft.Nonempty := by
  obtain ⟨i,hi⟩:=s.property.1.1; rcases i with i|i
  · exact ⟨i,mem_toLeft.mpr hi⟩
  obtain ⟨j,hj,_⟩:=((X.orders D _).1 s.property.2).2 i (mem_toRight.mpr hi)
  exact ⟨j,hj⟩

def route (s : X.Wagon D) : ForcedAddress G c where
  support:=region (X.scope D) s.val
  inventory:=region (X.flag D) s.val
  inventory_ne:=by
    rw [key]; obtain ⟨i,hi⟩:=X.forced D s; obtain ⟨x,hx⟩:=(D.forced i).inventory_ne
    exact ⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩
  inventory_sup:=region_inventory (covered X D) _
  extraTest x := ∀ i ∈ s.val.toLeft,(D.forced i).eligible P.threshold x

/-- New forced label. Test on old V predicates and the new *final centers*; overlaps
formed using bank union and D.range, so UsedFinal is passed on those, without retroactive
enlargement. When integrating THESE U flags later must use e.g. `inspected` before merging again. -/
def fused : Brand G c (X.Wagon D) := {
  forced:=X.route D P
  ink:=fun s V => if (X.route D P s).eligible P.threshold V then ∏ i∈s.val,X.phase D i V else 0 }

lemma chamber (V : Config G c) (s : X.Wagon D) (h : D.Names P) :
    clause (X.rawEligible D) (X.scope D) (X.flag D) (flags P.threshold V)
      (fun p => ∏ i∈p,X.phase D i V) s.val = (X.fused D P).ink s V := by
  unfold clause Brand.ink fused ForcedAddress.eligible route
  simp only [s.property.2,true_and]
  split_ifs with he hq
  · rfl
  · by_contra hn
    have hv (i : β) (hi : i∈s.val.toLeft) := prod_ne_zero_iff.mp hn (.inl i) (mem_toLeft.mp hi)
    exact hq ⟨he,fun i hi => h.permits i V (hv i hi)⟩
  rename_i H; exact absurd H.1 he
  rfl

def extra (Y : Support c) (i : ι) (U : Config G c) := if Disjoint (X.bank i) Y then 0 else X.call i U

def toll (V : Config G c) (b : Finset β) := D.record P V b *
    Real.exp (∑' i,X.extra (b.biUnion D.range) i V)

set_option maxHeartbeats 400000 in
/-- Main bridge already evaluating the REAL restored gas, conditional on retained d and
payments for those and the arriving exponent letters (before even pricing fused).
The masks and old flag predicates are genuine evaluations.
-/
theorem luggage (h : D.Names P) {a ε : ℝ} (H : D.Charged P a ε) (ha : 0≤a)
    (he : Dominated X.call) (V : Config G c) :
    HasSum ((X.fused D P).record P V) (∑' b,toll X D P V b) := by
  let p:=fun i => X.phase D i V
  let f:= fun s => if permits (X.rawEligible D) s ∧ region (X.flag D) s=flags P.threshold V then
    ∏ i∈s,p i else 0
  let c' := clause (X.rawEligible D) (X.scope D) (X.flag D) (flags P.threshold V) (fun s => ∏ i∈s,p i)
  let g := openOccurrence (X.scope D) (X.flag D) (flags P.threshold V) c'
  let A:=X.fused D P
  have hw (r : ℝ) : HasSum f r ↔ HasSum g r := by
    refine layout_sum (live X D) (covered X D) (flags P.threshold V) _ _ ?_ _
    intro s _ _
    nth_rw 1 [← Ac.reconstruct (scope X D) s]
    exact prod_biUnion (Ac.different ..)
  have hg : HasSum g (∑' b,toll X D P V b) := by
    apply (hw _).mp
    let e := (Finset.sumEquiv : Finset (Letter β ι) ≃o Finset β × Finset ι).toEquiv
    -- rolling out per selected d family, signed attachment activated iff incidence.
    let Y b := (Finset.biUnion b D.range)
    let w b i := Real.exp (X.extra (Y b) i V)-1
    have hf (b : Finset β) (u : Finset ι) : (f ∘ e.symm) (b,u)=D.record P V b * ∏ i∈u,w b i := by
      change f (b.disjSum u)=_
      unfold f
      rw [orders,key,toLeft_disjSum,toRight_disjSum]
      rw [prod_disjSum]
      unfold Brand.record Brand.covered
      let T := fun i : ι => ¬Disjoint (X.bank i) (Y b)
      have ht i : T i ↔ ∃ j∈b,¬Disjoint (X.bank i) (D.range j) := by
        unfold T Y; simp [Finset.disjoint_left]
        grind
      simp_rw [← ht]
      by_cases hA : (b : Set β).PairwiseDisjoint D.range ∧ b.biUnion D.require=flags P.threshold V
      · rw [if_pos hA]
        by_cases hv : ∀ i∈u,T i
        · rw [if_pos ⟨⟨hA.1,hv⟩,hA.2⟩,prod_congr rfl (g:=w b) (f:=fun j : ι => p (.inr j))
            (fun j hj => by unfold p phase w extra; rw [if_neg (hv _ hj)]; rfl)]
          rfl
        obtain ⟨i,hi,hni⟩ : ∃ i∈u,¬T i := by push Not at hv; exact hv
        rw [if_neg (fun hm => hv hm.1.2), prod_eq_zero hi (show w b i=0 from by
          unfold w extra; rw [if_pos (of_not_not ‹¬ T i›)]; simp)]; ring
      rw [if_neg hA, if_neg (fun ht => hA ⟨ht.1.1,ht.2⟩)]; ring
    -- common summable w majorant over all b
    let z i:= Real.exp (X.call i V)-1
    have hz : Summable z := by
      have hp:=he.absolute V
      refine (hp.mul_left 2).of_norm_bounded_eventually ?_
      filter_upwards [hp.tendsto_cofinite_zero.eventually_le_const zero_lt_one] with i hi
      exact Real.abs_exp_sub_one_le hi
    have hs : Summable (f ∘ e.symm) := by
      apply Summable.of_norm_bounded (g:=fun x : Finset β × Finset ι => ‖D.record P V x.1‖*∏ i∈x.2,‖z i‖)
        (summable_mul_of_summable_norm (f:=fun x => ‖D.record P V x‖) (g:=fun x => ∏ i∈x,‖z i‖)
          ((Brand.liable D H ha).absolute V).norm (summable_finsetProd_of_summable_norm (f:=fun i => ‖z i‖) hz.norm.norm).norm)
      rintro ⟨b,u⟩; change ‖(f ∘ e.symm) (b,u)‖ ≤ _
      rw [hf,norm_mul,norm_prod]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i _
      unfold w z extra; split; simp; exact le_rfl
    have hw b : Summable (fun i => X.extra (Y b) i V) := by
      refine (he.absolute V).of_norm_bounded fun i => ?_; unfold extra; split; simp; exact le_rfl
    have hW b : Summable (w b) := by
      refine hz.norm.of_norm_bounded fun i => ?_; unfold w z extra; split; simp; exact le_rfl
    refine e.symm.hasSum_iff.mp (hs.hasSum_iff.mpr ?_)
    rw [hs.tsum_prod]; apply tsum_congr; intro b
    simp_rw [hf,tsum_mul_left,← tprod_one_add (summable_finsetProd_of_summable_norm (hW b).norm)]
    unfold toll w; simp only [add_sub_cancel]; rw [← (hw b).hasSum.rexp.tprod_eq]; rfl
  -- Now relabel g (which had tests inside) to the Wagon gas. Pieces etc preserve coverage; remove invalid p only.
  let b := fun p : Finset (X.Wagon D) => p.image (Subtype.val (p:=fun _ => _))
  have hu i : g (b i)=A.record P V i := by
    unfold g b openOccurrence Brand.record
    have heq : Pieces (X.scope D) (b i) ∧ (b i).biUnion (region (X.flag D))=flags P.threshold V ↔ A.covered P V i := by
      have eq : (image (Subtype.val : X.Wagon D → _) i).biUnion (region (X.flag D)) = i.biUnion A.require := by
        rw [image_biUnion]; rfl
      dsimp only [b]
      rw [eq,Brand.covered]
      refine and_congr_left fun _ => ?_
      constructor
      · intro H q hq s hs hn
        exact H.1 (Finset.mem_image_of_mem _ hq) (Finset.mem_image_of_mem _ hs) (mt Subtype.ext hn)
      refine fun hr => ⟨fun q hq s hs hn => ?_,fun p hp => ?_⟩
      · obtain ⟨q,h0,rfl⟩:=Finset.mem_image.mp hq; obtain ⟨s,h1,rfl⟩:=Finset.mem_image.mp hs
        exact hr h0 h1 (fun he => hn (congr_arg Subtype.val he))
      obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hp; exact p.property.1
    split
    · rename_i hv; rw [if_pos (heq.mp hv),prod_image Subtype.val_injective.injOn]
      exact prod_congr rfl fun i _ => X.chamber D P V i h
    rename_i hv; rw [if_neg (mt heq.mpr hv)]
  have ho : Injective b:= Finset.image_injective Subtype.val_injective
  have ht : Summable (A.record P V) := (hg.summable.comp_injective ho).congr (fun i => hu i)
  refine ht.hasSum_iff.mpr <| (tsum_eq_tsum_of_ne_zero_bij (g:=A.record P V) (fun i => b i.val) (ho.comp Subtype.val_injective)
    (show support g⊆_ from ?_) (fun i => hu i.val)).symm.trans hg.tsum_eq
  intro i H
  have he : ∀ j∈i, Ac.Spark (scope X D) j ∧ permits (X.rawEligible D) j := by
    change g i≠0 at H
    unfold g openOccurrence at H; split at H
    · rename_i hS; intro j hj
      have hh := prod_ne_zero_iff.mp H j hj
      unfold c' clause at hh; split at hh
      · rename_i ht; exact ⟨hS.1.2 j hj,ht.1⟩
      exact (hh rfl).elim
    exact (H rfl).elim
  let v : Finset (X.Wagon D):=i.subtype _
  have hv : b v=i := by
    ext x
    unfold b; rw [Finset.mem_image]
    constructor
    · rintro ⟨q,hq,rfl⟩; exact (Finset.mem_subtype).mp hq
    intro hx; exact ⟨⟨x,he x hx⟩,by simp [v,hx],rfl⟩
  refine ⟨⟨v,?_⟩,hv⟩
  rw [mem_support,←hu,hv]; exact H

end Riser
end YM.SectorNext.Reconnect
