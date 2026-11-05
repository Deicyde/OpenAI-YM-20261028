import YM.MultipleContact.Multi.ProbeTicket

/-! One choice of bands suitable for both the whole packet and the fixed probe lists individually. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.MultipleContact.ScheduleRow
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {b:ℕ}{n d: Fin b → ℕ} -- no local notation
variable (D : ∀ i:Fin b,Detector S (d i))
lemma probe_space (x:Exterior C.book):∀ᶠ M:ℕ in atTop, Drama.far (C.S.a M) x.point.ofLp:= by
        suffices ∀ᶠ M:ℕ in atTop,∀ ij:{p:Fin (x.n+1)×Fin (x.n+1) // p.1≠p.2},4*C.S.a M<‖x.point ij.val.1 - x.point ij.val.2‖ from this.mono fun i hi a b hab=>hi ⟨(a,b),hab⟩
        refine eventually_all.mpr fun ⟨⟨a,b⟩,hab⟩=> ((C.S.shrinks.const_mul 4).eventually (gt_mem_nhds ?_))
        rw [mul_zero]; exact norm_pos_iff.mpr (sub_ne_zero_of_ne (x.clear.ne hab))
lemma layout (Q:Fin b → ℝ)(hQ:∀i,0<Q i)(κ:ℝ)(hk:0<κ) (hF:CellHyp C F):
     ∃ (M J:ℕ)(P:Fin b→ℝ),4*C.S.a M<κ ∧ M≤J ∧ b * (6*C.S.a J) < C.S.a M ∧ (∀ i:Fin b,0<P i ∧ ∀v:C.book.Ref (d i), ‖v‖<Q i → Drama.Wage F C (Drama.Unit C v) J (P i)) ∧
     ∃ B> (0:ℝ),∀ i:Fin b,∀ x:(D i).probes,((x.val.n+1:ℕ):ℝ) * (6*C.S.a J) < C.S.a M ∧ Drama.far (C.S.a M) x.val.point.ofLp ∧ (∀j:Fin x.val.n,Drama.Wage F C (Drama.Unit C ((x.val.letter j).2)) J B):= by
         let T := Sigma (fun i:Fin b=> (D i).probes)
         have hM : ∀ᶠ M in atTop,4*C.S.a M < κ ∧ ∀t:T,Drama.far (C.S.a M) t.snd.val.point.ofLp:= ((C.S.shrinks.const_mul 4).eventually (gt_mem_nhds ((show 4*0 < κ from (by simpa using hk))))).and (eventually_all.mpr fun t:T=>probe_space ..)
         obtain ⟨M,hk,hspace⟩:=hM.exists
         let P' := Sigma (fun s:T=>Fin (s.snd.val.n))
         let L(k:P'):=k.fst.snd.val.letter k.snd
         have hb(k:P') := hold_cost hF (L k).fst (‖(L k).snd‖+1) (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
         have hw:= (eventually_ge_atTop M|>.and ((C.S.shrinks.const_mul 6|>.const_mul (b:ℝ)).eventually (gt_mem_nhds (show (b:ℝ)*(6*0)<C.S.a M by simpa using C.S.a_pos M)))) |>.and ((eventually_all.mpr fun t:T=>(C.S.shrinks.const_mul 6|>.const_mul ((t.snd.val.n+1:ℕ):ℝ)).eventually (gt_mem_nhds (show ((t.snd.val.n+1:ℕ):ℝ)*(6*0) < C.S.a M by simpa using C.S.a_pos M))) |>.and ((eventually_all.mpr fun i:Fin b=>hold_cost hF (d i) (Q i) (hQ i)).and (eventually_all.mpr hb)))
         obtain ⟨J,⟨hJ,hfit⟩,ht,hcost,hcost'⟩:=hw.exists
         choose U hU hB using hcost'; obtain ⟨B,hbound⟩:= Finite.bddAbove_range U
         choose P hp hP using hcost
         refine ⟨M,J,P,hk,hJ,hfit,fun i=>⟨hp i,hP i⟩,max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun i x=> ⟨ht ⟨i,x⟩,hspace ⟨i,x⟩,fun j=>?_⟩⟩
         let y:P':=⟨⟨i,x⟩,j⟩
         apply (hB y (L y).2 (by linarith only)).mono; intro a ha; obtain ⟨hh,h,hz⟩:=ha; exact ⟨hh,h,hz.trans ((hbound (Set.mem_range_self y)).trans (le_max_right ..))⟩

variable [∀i,Inhabited (Fin (n i))]
end YM.MultipleContact.ScheduleRow
