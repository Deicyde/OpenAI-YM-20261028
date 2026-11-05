import YM.MultipleContact.Multi.Calendar

/-! Snapshot using the actual continuum positions and single-cluster dynamic reference units, with masks. Input rows can come from `portion`. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.MultipleContact.ScheduleRow
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open RG Bunching.Cord
open scoped Topology BigOperators Classical
variable {b:ℕ}{G:Gauge}{C:Family G}{F:Extraction.Order}
local notation "I"=> Fin b
variable {n d: Fin b→ℕ} [∀ i,Inhabited (Fin (n i))]{v :∀i:Fin b,Fin (n i)→ C.book.Token}
variable {J M:ℕ}{m j:Fin b→ℕ}{F' : Filter (ℕ×ℕ)}
lemma extract_tuple (u:∀i:Fin b,ℕ×ℕ → C.book.Ref (d i)) {B:ℝ} (hb: NeBot F') (h:F' ≤ F.fuse) (h':∀i,∀ᶠ t in F',‖u i t‖ ≤ B):∃ L:Filter (ℕ×ℕ), L ≤ F.fuse ∧ L.NeBot ∧ ∃w:∀ i,C.book.Ref (d i),∀ i,Tendsto (u i) L (𝓝 (w i)):= by
     suffices hh:∀ l:Finset (Fin b),∃ L:Filter (ℕ×ℕ), L ≤ F' ∧ L.NeBot ∧ ∃w:∀ i,C.book.Ref (d i),∀ i∈l,Tendsto (u i) L (𝓝 (w i)) by
          obtain ⟨L,hk,ha,w,hw⟩:=hh Finset.univ; exact ⟨L,hk.trans h,ha,w,fun i=>hw i (by simp)⟩
     intro l; induction l using Finset.induction with
     | empty=>exact ⟨F',le_rfl,hb,fun _=>0,fun _ hk=>False.elim (Finset.notMem_empty _ hk)⟩
     | insert i l hi ih=>
         obtain ⟨L,hk,hb,z,hz⟩:=ih
         obtain ⟨L',hL,H,w,h⟩:=finite_extract (𝓛:=L) (u i) B ((h' i).filter_mono hk)
         refine ⟨L',hL.trans hk,H,update z i w,fun s hs=>?_⟩
         rcases Finset.mem_insert.mp hs with hs|hs
         · subst s; simpa only [update_self] using h
         simpa only [update_of_ne (ne_of_mem_of_not_mem hs hi)] using (hz s hs|>.mono_left hL)

variable {x: Fin b→ ℝ}{xe: Π i:Fin b, Fin (n i)→ E4}
variable {fl: Filter (ℕ×ℕ)} (hf:fl.NeBot){B A ε:Fin b→ℝ}
open Drama
variable {δ:ℝ} {h : Fin b → ℕ} {lamp: Side}
variable (hv:∀i:Fin b,Portion C F (d i) (v i) J (m i) (j i) lamp δ (A i)) {g:Fin b→ Drama.Mode}
variable (hBand: ∀i,g i≠ .fused → Cord.Band (n i) lamp (x i) (xe i))(hTail:∀i,tail C (x i) (m i))(hx:∀i,0<x i){y:Π i:Fin b, Fin (n i) → Cover}{u:∀i:Fin b,ℕ×ℕ → C.book.Ref (d i)} {w:∀i:Fin b,C.book.Ref (d i)} {z:Fin b→ E4}
include hf hv hBand hTail hx
omit hf hv hBand hTail hx in
lemma a_mono (S:Schedule){M J:ℕ}(h:M ≤ J):S.a J ≤ S.a M:=(le_mul_of_one_le_right (S.a_pos _|>.le) (show (1:ℝ) ≤ (S.toDepth h 0).count.val from Nat.one_le_cast.mpr (S.toDepth h 0).count.pos)).trans_eq (S.embeds_scale ..) -- wrong include!!!
lemma combined {P:Fin b → ℝ}{S:Table C.book} (hR:∀i,g i=.signed→ xe i=C.S.gridPoint (j i) ∘ (y i)) (hP:∀i,g i=.signed → ∀b:Axis,Injective (fun k:Fin (n i)=>xe i k b))
    (hW:∀ i,g i=.signed → Drama.Wage F C (Loss C (j:=j i) (y i) (v i) (charge (v i) (d i) (m i)) (u i)) J (A i))
    (hF:∀ i,g i=.fused→xe i=0 ∧ Drama.Wage F C (Fused C (u i)) J (P i))
    (hJ:M ≤ J) (hfit: b*(6*C.S.a J) < C.S.a M)(hfar:Drama.far (C.S.a M) z)(HC:S.Hierarchy) (hm:F.PointLimits C S)(hT:fl ≤ F.fuse)(hTend:∀i,Tendsto (u i) fl (𝓝 (w i)))(hc:C.Makes):
    let price i:=if g i=.raw then (x i)^(-(mass (v i):ℝ)-δ) else if g i=.signed then A i else P i
    ‖evaluation S (∏i,expression (S:=S) (g i) (charge (v i) (d i) (m i)) (S.classTokens ∘ v i) (S.project _ (w i)) (z i) (xe i))‖ ≤ ∏i,price i:=by
       intro price
       let L1 i:= m i+1;let L2 i:= m i+1+Lag (n i)
       choose K hvK using fun i=> (hv i).raw _ (hx i) (hTail i)
       have h: Tickets C F (fun i=>charge (v i) (d i) (m i)) v (fun t i=>u i t) g J L1 L2 j y K price := by
         refine ⟨fun i hi=>?_,fun i hi=>?_,fun i hi=>?_⟩
         · simpa [price,hi] using hW i hi
         · simpa [price,hi] using (hF i hi).2
         exact ⟨(hvK i).1,Nat.le_add_right ..,(hvK i).2.1,slots (n i) (m i), (hvK i).2.2.1,(hvK i).2.2.2.trans (le_of_eq (by simp [price,hi]))⟩
       apply Drama.passage (s:=z) h HC hm hT hTend hc hJ hfit hfar hR hP
       · refine fun i hi=> ⟨(hv i).small _ (hx i) (hTail i) _ (hBand i (by simp [hi])),fun k l h=>?_⟩
         exact (point_gap (m i) (x i) (hTail i)).trans ((hBand i (by simp [hi])).2.1 k l h)
       refine ⟨fun i hi k l h=>by
            by_contra hc; have he:= (hBand i hi).2.1 k l hc; simp only [h,sub_self,norm_zero] at he; exact he.not_ge (div_nonneg (hx i).le (by norm_num)), fun i k=>?_⟩
       by_cases h:g i=.fused
       · rw [(hF i h).1]; simpa using (C.S.a_pos M).le
       have ht:=(hv i).small _ (hx i) (hTail i) _ (hBand i h) k; apply (a_mono C.S hJ).trans' (by nlinarith only [ht,norm_nonneg (xe i k)])
end YM.MultipleContact.ScheduleRow
