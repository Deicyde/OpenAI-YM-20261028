import YM.MergeProof.Accent
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil 
variable {w:V→ℝ} {F:I→Y→Poly B} {s:I→Support n} {b:ℕ}{d C t:ℝ}
lemma Loci.fares {F:Y→Poly B}(h:Loci w F t)(hw:∀ i,0<w i): 0≤ t ∧ ∀ y,Poly.price w (F y)≤ t:=by
   obtain ⟨f,h,hf,he⟩:=h; exact ⟨le_trans (sum_nonneg (fun i _=>mul_nonneg (Poly.worth hw _).le (h i))) he,fun y=> (le_trans (Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hf _ _) (Poly.worth hw i).le) he)⟩
lemma Towed.repair (h:Towed w s F b d C)(hw:∀ i,0<w i) (U:Y): Summable (fun i=>Poly.price w (F i U)) ∧ Summable (fun i=>F i U):=by
   obtain ⟨a,ha,h,hB⟩:=h; exact ⟨ha.of_nonneg_of_le (fun i=> Poly.nonnegative hw _) (fun i=> (Loci.fares (hB i) hw).2 _), (Poly.budgeted hw ha (fun i=> (Loci.fares (hB i) hw).2 U)).1⟩
-- compress into finite or any layout. tsums proof

def tally (k:I→J)(F:I→Y→Poly B) : J→Y→Poly B := fun j U=>∑' i : {i // k i=j}, F i.val U
lemma border {p:I→Poly B} (k:I→J) (hp:Summable p) : HasSum (fun j:J=>∑' i:{i// k i=j},p i.val) (∑' i,p i):= hp.hasSum.tsum_fiberwise k
set_option maxHeartbeats 640000 in
lemma towing {r:J→ Support n} (k:I→J)(F:I→Y→Poly B) (h:Towed w (r ∘ k) F b d C) (hw:∀ i,0<w i) : Towed w r (tally k F) b d C:=by
   obtain ⟨a,ha,h,H⟩:=h
   choose f hf hF he using fun i=> H i
   have ht(i):0 ≤ wordsPrice w (f i):=sum_nonneg (fun l _=>mul_nonneg (Poly.worth hw _).le (hf i l))
   have hc(i:B.Mode): Summable fun j=> f j i:= by
     apply (summable_mul_left_iff (Poly.worth hw i).ne').mp; refine ha.of_nonneg_of_le (fun j=>mul_nonneg (Poly.worth hw i).le (hf j i)) (fun j=>?_) ; exact (single_le_sum (f:=fun i=> Poly.toll w i*f j i) (fun i _=> mul_nonneg (Poly.worth hw i).le (hf j i)) (mem_univ _)).trans (he j)
   let A(j:J):= cram k a j
   have hA := heavy k ha
   refine ⟨A,hA.summable,fun p=>?_,fun j=>?_⟩
   · let t(i:I):= if p∈ r (k i) then a i * Real.exp (d*coverNumber b (r (k i))) else 0
     let e:= Real.exp; have h0:= heavy k (f:=t) (h p).2.1
     change SumBudget (fun j=> if p∈r j then A j*Real.exp (d*coverNumber b (r j)) else 0) C
     rw [show (fun j=> if p∈r j then A j*Real.exp (d*coverNumber b (r j)) else 0)=cram k t from funext fun j=>?_]; exact ⟨fun i=> tsum_nonneg (fun j=> (h p).1 j.val),h0.summable,h0.tsum_eq.trans_le (h p).2.2⟩
     unfold cram; by_cases he:p∈ r j
     · rw [if_pos he]; unfold A cram; rw [← tsum_mul_right]; refine tsum_congr fun i=> ?_; unfold t; rw [i.property,if_pos he]
     rw [if_neg he]; symm; refine (tsum_congr ?_).trans tsum_zero; intro i; unfold t; rw [i.property,if_neg he]
   let w' (i:B.Mode):= cram k (fun j=>f j i) j
   refine ⟨w',fun p=>tsum_nonneg (fun i=> hf i.val p),fun U i=> ?_,?_⟩
   · have hz:=Poly.budgeted hw (ha.comp_injective (f:=fun i=> a i) (i:=Subtype.val (p:=fun x=> k x=j)) Subtype.val_injective) (fun i=>(Loci.fares (H i.val) hw).2 U)
     rw [tally,Poly.share hz.1]; have he : Summable fun i':{x// k x=j}=> f i'.val i:= (hc i).comp_injective Subtype.val_injective; have ht:= fun i':{x// k x=j}=> hF i'.val U i
     exact (norm_tsum_le_tsum_norm (he.of_nonneg_of_le (fun i=> norm_nonneg _) ht)).trans ((he.of_nonneg_of_le (fun i=> norm_nonneg _) ht).tsum_le_tsum ht he)
   have ht := (ha.of_nonneg_of_le ht he).comp_injective (i:=Subtype.val (p:=fun i=> k i=j)) Subtype.val_injective
   refine le_trans ?_ (ht.tsum_le_tsum (fun i=>he i.val) (ha.comp_injective Subtype.val_injective))
   unfold wordsPrice w' cram; simp_rw [← tsum_mul_left]; apply le_of_eq; rw [Summable.tsum_finsetSum]; intro i _; exact ((hc i).comp_injective Subtype.val_injective).mul_left _
end YM.MergeProof.Accent
