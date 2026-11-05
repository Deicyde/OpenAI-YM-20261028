import YM.MergeProof.Endow
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil
variable {w:V→ℝ} {F:I→Config G n→Poly B} {s:I→Support n} {b:ℕ}{d C t:ℝ}{o:V→Site n}
lemma transit [Countable I] (k:I→J) {r:J→ Support n}(h: ∀ i,Borne o (r (k i)) (F i) t)(he:∀ U,Summable (fun i=>F i U)) (j:J): Borne o (r j) (tally k F j) t:=by
   let v := {i // k i=j}; have hh (i:v): Borne o (r j) (F i.val) t:= by obtain ⟨i,e⟩:=i; subst j; exact h _
   have ht U: Summable fun i:v=>F i.val U:= (he U).comp_injective Subtype.val_injective
   refine ⟨fun U V hV hx=>tsum_congr (fun i=> (hh i).home U V hV hx),fun g U=>tsum_congr (fun i=> (hh i).turns g U), fun i=>?_,fun U c hx=>?_⟩
   · have he: (fun U=> (tally k F j U).part i)=fun U=>∑' l:v,(F l.val U).part i:=funext fun U=>Poly.share (ht _) i; rw [he]; exact Measurable.tsum (fun j=> (hh j).me i)
   unfold tally; rw [Poly.share (ht _)]; exact (tsum_congr (fun i=> (hh i).scope _ c hx)).trans tsum_zero
lemma transitE [Countable I] (k:I→J) {r:J→ Support n}(h: ∀ i,Burns o (r (k i)) (F i) t)(he:∀ U,Summable (fun i=>F i U)) (j:J): Burns o (r j) (tally k F j) t:=by
   let v := {i // k i=j}; have hh (i:v): Burns o (r j) (F i.val) t:= by obtain ⟨i,e⟩:=i; subst j; exact h _
   refine { transit k (fun i=>(h i).toBorne) he j with
            permits:= fun U hp=>?_
            sil:=fun i=>?_ }
   · by_contra hn; exact hp ((tsum_congr (fun i:v=> not_not.mp (mt ((hh i).permits U) hn))).trans tsum_zero)
   unfold tally; rw [Poly.share]; exact (tsum_congr (fun j=> (h _|>.sil i))).trans tsum_zero
   exact (he i).comp_injective Subtype.val_injective
lemma transitK [Countable I] (k:I→J){r:J→ Box n}(h: ∀ i,Flow o (r (k i)) (F i) t)(he:∀ U,Summable (fun i=>F i U)) (j:J): Flow o (r j) (tally k F j) t:=by
   let v := {i // k i=j}; have hh (i:v): Flow o (r j) (F i.val) t:= by obtain ⟨i,e⟩:=i; subst j; exact h _
   refine { transit k (r:=Prod.fst ∘ r) (fun i=>(h i).toBorne) he j with
            permits:=fun U hu=>?_ }
   by_contra hn; exact hu ((tsum_congr (fun i:v=> not_not.mp (mt ((hh i).permits U) hn))).trans tsum_zero)
lemma room (X:Support n) (o:V→Site n)(p:B.Mode) : ((p.val:Set V) ⊆ {i|o i∈X}) ↔ p.val.image o ⊆ X :=by
   constructor
   · intro h j hj; obtain ⟨k,hk,rfl⟩:= mem_image.mp hj; exact h hk
   intro h i hi;exact h (mem_image_of_mem o hi)
lemma Borne.place {X:Support n}{f:Config G n→Poly B}(h:Borne o X f t)(p:B.Mode)(U)(hp:(f U).part p≠0): p.val.image o ⊆ X:= (room ..).1 (of_not_not fun he=>hp (h.scope U p he))
end YM.MergeProof.Accent
