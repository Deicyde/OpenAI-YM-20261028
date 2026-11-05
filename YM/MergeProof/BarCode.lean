import YM.Extra.SOURCE_HISTORIES.Pencil
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{A:Activities G n}{ι K E:Type*}
abbrev Box (n:Side):= Support n × Support n
def barcode (A:Activities G n)(i:ℕ): Box n := ((A.forced i).support,(A.forced i).inventory)
-- compress wrt Supports/int.
def cram (k:ι→K)(f:ι→E)[AddCommGroup E][TopologicalSpace E][T2Space E](p:K):= ∑' i:{i:ι//k i=p},f i.val
lemma heavy (k:ι→K){f:ι→ℝ}(hf:Summable f):HasSum (cram k f) (∑' i,f i):= hf.hasSum.tsum_fiberwise k
lemma bulky (k:ι→K){f:ι→ℂ}(hf:Summable f):HasSum (cram k f) (∑' i,f i):= hf.hasSum.tsum_fiberwise k -- no abs?
lemma metric_cram (k:ι→K){f:ι→ℂ}{c:ι→ℝ}(hc:Summable c)(hb:∀ i,‖f i‖ ≤ c i)(p:K): ‖cram k f p‖ ≤ cram k c p:=by
  have hh:Summable (fun i:{i// k i=p}=> ‖f i.val‖):= (hc.of_nonneg_of_le (fun i=>norm_nonneg _) hb).comp_injective Subtype.val_injective
  exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum (fun i=>hb _) (hc.comp_injective Subtype.val_injective))
lemma expand_eq (k:ι→K)(x:K)(f:ι→E)[AddCommGroup E][TopologicalSpace E][T2Space E][DecidableEq K]: cram k f x=∑' i,if k i=x then f i else 0:= by
   unfold cram; rw [show (∑' i, if k i=x then f i else 0)=_ from (tsum_subtype_eq_of_support_subset (s:={i|k i=x}) (f:=fun i=>if k i=x then f i else 0) (by intro i hi; by_contra h; exact hi (if_neg h))).symm]; exact tsum_congr fun i=> (if_pos i.property).symm
lemma reach (a:Equiv.Perm ℕ) (A:Activities G n)(d:BudgetPoint)(ha:∀ i,barcode A (a i)=barcode A i)(U:Config G n)(b:Finset ℕ): A.admissible d U (b.map a.toEmbedding)↔ A.admissible d U b:= by
  unfold Activities.admissible
  have hu : (b.map a.toEmbedding).biUnion (fun i => (A.forced i).inventory) = b.biUnion fun i => (A.forced i).inventory := by rw [map_eq_image,image_biUnion]; ext; simp [(fun i=> show (A.forced (a i)).inventory= _ from Prod.mk.inj (ha i)|>.2)]
  rw [hu]; congr! 1; unfold Set.Pairwise; simp only [Finset.mem_coe,Finset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Equiv.toEmbedding_apply, ne_eq, Equiv.apply_eq_iff_eq, fun i=> show (A.forced (a i)).support=_ from Prod.mk.inj (ha i)|>.1]
variable {R: Rep G n}{j i:ℕ}
lemma tariff (he: barcode R.activities i= barcode R.activities j)(U:Config G n): dressed R i U=dressed R j U:= by
   by_cases ht:i=j; subst i;rfl
   let a:= Equiv.swap i j; have ha:a i=j:=Equiv.swap_apply_left ..; let f:=a.finsetCongr; unfold dressed; nth_rw 2 [← f.tsum_eq]
   have hv(k): barcode R.activities (a k)= barcode R.activities k:=by
      by_cases h:k=i; rw [h,ha,he]; by_cases h':k=j; rw [h',show a j=i from Equiv.swap_apply_right ..,he]; rw [show a k=k from Equiv.swap_apply_of_ne_of_ne h h']
   apply tsum_congr; intro b
   change coat R i b U=coat R j (f b) U
   unfold coat
   simp_rw [show f b=b.map a.toEmbedding from rfl, reach a _ _ hv, show j∈b.map a.toEmbedding ↔ i∈ b from by nth_rw 1 [← ha]; simp]; split_ifs with h
   have hp:j∉b:=by
      intro hz; let V:= (R.activities.forced i); have hs: Disjoint V.support V.support:= ((congr_arg (Disjoint V.support) (Prod.mk.inj he|>.1).symm)) ▸ (show Disjoint V.support (R.activities.forced j).support from h.2.1 h.1 hz ht); obtain ⟨x,hx⟩:= V.inventory_ne; exact disjoint_left.mp hs (V.inventory_sup hx) (V.inventory_sup hx)
   have hx : (b.map a.toEmbedding).erase j=b.erase i:=by
      rw [show j=a.toEmbedding i from ha.symm,← Finset.map_erase]; ext x; simp only [mem_map,mem_erase,Function.Embedding.coeFn_mk]
      constructor; rintro ⟨p,⟨hh,hb⟩,rfl⟩; rw [show a p=p from Equiv.swap_apply_of_ne_of_ne hh (ne_of_mem_of_not_mem hb hp)]; exact ⟨hh,hb⟩
      rintro ⟨hi,hb⟩; exact ⟨x,⟨hi,hb⟩,Equiv.swap_apply_of_ne_of_ne hi (ne_of_mem_of_not_mem hb hp)⟩
   rw [hx]
   rfl
lemma chamber {f g : ℕ→ℂ} (h:cram (barcode R.activities) f=cram (barcode R.activities) g)(U : Config G n)(hf: Summable fun i=> f i*dressed R i U)(hg : Summable fun i=> g i*dressed R i U):
    ∑' i,f i*dressed R i U=∑' i,g i *dressed R i U:=by
    let q:=barcode R.activities; rw [← (bulky q hf).tsum_eq, ← (bulky q hg).tsum_eq]; refine tsum_congr fun i=>?_
    by_cases hx:i∈ Set.range q
    · obtain ⟨k,rfl⟩:=hx
      have he (F:ℕ→ℂ): cram q (fun i=> F i*dressed R i U) (q k)= cram q F (q k)* dressed R k U:=by
        unfold cram; rw [← tsum_mul_right]; apply tsum_congr; intro i; dsimp only; rw [tariff i.property]
      rw [he,he,congr_fun h]
    haveI : IsEmpty {u:ℕ // q u=i}:= ⟨fun ⟨j,h⟩=> hx ⟨j,h⟩⟩; rw [cram,cram,tsum_empty,tsum_empty]
end YM.MergeProof
