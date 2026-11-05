import YM.MergeProof.Figure
import YM.MergeProof.Pitch

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open Local Extra.Trajectories Source
variable {R:Rep G n}(A: Activities G n)(P:BudgetPoint)(U:Config G n)
local notation "bc"=> barcode A
local notation "X" => flags P.threshold U
variable {F:Box n→Poly B}
lemma rock_out (f:ℕ→Poly B) {w:V→ℝ} (hp:∀ i,0<w i)(hf:Summable (fun i=>Poly.price w (f i))):
   field (cram (barcode A) f) (flags P.threshold U)=∑' x:Finset ℕ, if A.admissible P U x then ∏ i∈x,f i else 0:=by
   rw [field_eq bc X _ (Poly.budgeted hp hf (fun _=>le_rfl)).1 (Packets.summable_value _ _ _ hp hf)]; exact tsum_congr (fun i=> shovel A f U P i)
lemma mass_crest (A:Activities G n){P:BudgetPoint}{e t:ℝ}(hp:A.Valid P e t) (U:Config G n): Summable fun i=> A.K i U := by
   obtain ⟨b,h,hp⟩:= Activities.K_total hp.boundK; exact h.of_norm_bounded (fun i=> (hp i).2 _)
variable (hs:Summable (fun i=> A.K i U)) (hc:∀ i,(F i).part B.quiet= profile A (fun j=> Complex.ofReal ∘ A.K j) i U)
include hs hc
lemma stage₀ : (field F (flags P.threshold U)).part B.quiet=A.gas P U := by
   let K(i:ℕ):Poly B:= Poly.send B.quiet (↑(A.K i U):ℂ); let f:= cram bc K; let w:= fun _:V=> (1:ℝ); have hw i:0<w i:=zero_lt_one
   have hk: Summable fun i=> Poly.price w (K i):=by simp only [K,Poly.solo,Complex.norm_real,Poly.quiet_toll,one_mul]; exact hs.norm
   have hS := Packets.summable_value bc (Pattern X) K hw hk; have hK := (Poly.budgeted hw hk (fun i=>le_rfl)).1
   have he(p): (F p).part B.quiet= (f p).part B.quiet:= by
      unfold f; rw [cram,Poly.share]; rw [hc p]; refine tsum_congr (fun j=>?_); change (↑(A.K j.val U):ℂ)=(Poly.send B.quiet _).part _; simp
      exact hK.comp_injective Subtype.val_injective
   rw [show (field F X).part B.quiet=(field (cram bc K) X).part B.quiet from ?_, field_eq bc X _ hK hS,Poly.share hS]
   · unfold Activities.gas; rw [Complex.ofReal_tsum]; refine tsum_congr (fun i=>?_); rw [shovel]; unfold Activities.gasOccurrence; split; next h=> rw [shockProd₀,Complex.ofReal_prod];exact prod_congr rfl fun _ _=> by simp [K]
     next=>simp -- edit
   unfold field; rw [Poly.part_sum,Poly.part_sum]; refine Finset.sum_congr rfl (fun i _=>?_); unfold grid; split; next=> rw [shockProd₀,shockProd₀];exact prod_congr rfl fun i _=>he i
   next=>rfl
-- Barn oracle reads single output directly against Wilson coefficient exact density. No positivity proof needed for that identity alone.
variable {hs': ℕ→ℂ} {v:V}(hz: Summable hs')(hr:∀ i,(F i).part (B.fire v)=cram (barcode A) hs' i)
include hz hr
def nickel (P:BudgetPoint)(A:Activities G n)(u:Finset ℕ)(U:Config G n)(f:ℕ→ℂ):ℂ:= if A.admissible P U u then ∑ i∈u,f i * ∏ j∈u.erase i,(A.K j U:ℂ) else 0
lemma stageR : (field F (flags P.threshold U)).part (B.fire v)=∑' i,nickel P A i U hs' :=by
   let K(i:ℕ):Poly B:= Poly.send B.quiet (↑(A.K i U):ℂ)+Poly.send (B.fire v) (hs' i); let f:=cram bc K
   let w:= fun _:V=> (1:ℝ); have hw i:0<w i:=zero_lt_one; have ht:=B.fire_hot v
   have hk:Summable fun i=> Poly.price w (K i):= Summable.of_nonneg_of_le (fun i=> Poly.nonnegative hw _) (fun i=>Poly.addition hw _ _) (Summable.add (by simp only [Poly.solo,Complex.norm_real,Poly.quiet_toll,one_mul];exact hs.norm) (by simp only [Poly.solo,Poly.solo_toll,w,one_mul];exact hz.norm))
   have hx i:(K i).part B.quiet= A.K i U:=by simp [K,ht.symm]
   have hy i:(K i).part (B.fire v)=hs' i:=by simp [K,ht]
   have hK := (Poly.budgeted hw hk (fun _=>le_rfl)).1; have hS:=Packets.summable_value bc (Pattern X) K hw hk
   have hq(i): (F i).part B.quiet=(f i).part B.quiet:=by unfold f; rw [cram, hc,Poly.share]; exact tsum_congr fun j=> (hx _).symm; exact hK.comp_injective Subtype.val_injective
   have hn(i):(F i).part (B.fire v)= (f i).part (B.fire v):=by unfold f; rw [cram,hr,Poly.share]; exact tsum_congr fun j=> (hy _).symm; exact hK.comp_injective Subtype.val_injective
   have hh(u:Finset (Box n)): (grid F X u).part (B.fire v)=(grid f X u).part (B.fire v):= by unfold grid; split; rw [shockProd,shockProd]; simp_rw [hq,hn]; rfl
   rw [show (field F X).part (B.fire v)=(field (cram bc K) X).part (B.fire v) from (by unfold field; rw [Poly.part_sum,Poly.part_sum]; exact sum_congr rfl fun i _=>hh i), field_eq bc X _ hK hS,Poly.share hS]
   refine tsum_congr fun i=>?_ ; rw [shovel]; unfold nickel; split; rw [shockProd]; simp_rw [hx,hy]; congr!
   rfl
end YM.MergeProof.Accent
