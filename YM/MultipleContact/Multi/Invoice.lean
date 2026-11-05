import YM.MultipleContact.Multi.Hold

/-! Decoding one signed branch at a time, under polynomial-template limits on their common cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.MultipleContact.ScheduleRow
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {b:ℕ}{n d: Fin b → ℕ}
variable [∀i,Inhabited (Fin (n i))]{v:∀i:Fin b,Fin (n i) → C.book.Token}
variable (D : ∀ i:Fin b,Detector S (d i))
variable (hA:Acme.Aroma C)(hT:Treasury C){ε:ℝ}
variable (hF:CellHyp C F)(H:S.Hierarchy)(hm:F.PointLimits C S)(hc:C.Makes)
variable (lamp:Lattice.Side)
variable {M J : ℕ}{m j:Fin b→ℕ}{g:Fin b→Mode}{A:Fin b→ℝ}{B:ℝ}{ρ:Fin b→ℝ}
variable {xe:∀i:Fin b,Fin (n i)→ E4}
variable (hsa:∀i:Fin b,g i ≠ .fused → ‖(0:ℂ)‖≤1)
variable (hPortion:∀i:Fin b,Portion C F (d i) (v i) J (m i) (j i) lamp ε (A i))
variable (hTail:∀i:Fin b,tail C (ρ i) (m i)) (h0:∀i,0 < ρ i)
variable (hBand:∀i:Fin b,g i ≠ .fused → Band (n i) lamp (ρ i) (xe i)) (hPlaced:∀i:Fin b,g i=.signed→∀ k:Fin (n i)×Axis,Placed _ (C.S.a (j i)) (xe i) k)
-- layout constants (only detector-alone budget here)
variable (hJ:M ≤ J) (hfit:∀ k:Fin b,∀ e:(D k).probes,((e.val.n+1:ℕ):ℝ)*(6*C.S.a J)< C.S.a M)
variable (hfar:∀ k:Fin b,∀ e:(D k).probes,Drama.far (C.S.a M) e.val.point.ofLp)
variable (hBudget:∀ k:Fin b,∀ e:(D k).probes,∀ i:Fin e.val.n,Wage F C (Drama.Unit C ((e.val.letter i).2)) J B)
variable {x:Π i:Fin b,Fin (n i) → Cover}{u:Π i:Fin b,ℕ×ℕ → C.book.Ref (d i)}
variable {fl:Filter (ℕ×ℕ)}[hN:fl.NeBot]
-- (insert missing variables from Hold below if needed)
variable {P:Fin b→ℝ}{K:ℝ}{z:Fin b → E4}(hf:(b:ℝ)*(6*C.S.a J) < C.S.a M)(hz:Drama.far (C.S.a M) z)
variable (α:∀ i:Fin b,S.Field (d i))(hα:∀ i:Fin b,g i=.fused→‖α i‖≤1)
variable (hP':∀ i:Fin b,0 < P i)(hFusion:∀ i:Fin b,∀ v:S.Field (d i),‖v‖ ≤ 1→ Wage F C (Drama.Unit C (S.representative _ v)) J (P i))(hRate:∀i,0<A i)
variable (hK':0 < K)(hK:∀ k:Fin b,∀V:Fin (n k) → S.Tag,∀Y: Fin (n k) → E4,∀ y:S.Field (d k),∀ c:ℝ,∀ e> (0:ℝ), (∀t:(D k).probes, ‖(c:ℂ) • raw S V (points Y) t.val-response S (d k) t.val y‖ ≤ e*(B^t.val.n))→ ‖c • (D k).apply V (points Y) - y‖ ≤ K*e)
def scaleMap (g : Fin b→Mode) (err raw full: Fin b→ℝ)(i:Fin b):ℝ:= match g i with | .signed=>err i | .raw=>raw i| .fused=>full i
def cash (P : Fin b→ℝ)(K:ℝ):= (Fintype.card (Fin b→ Fin 2):ℝ)*(∏ i:Fin b,max 1 (K*P i))
local notation "q'"=>fun i:Fin b=> (S.classTokens ∘ v i)
local notation "w'"=>fun i:Fin b=> charge (v i) (d i) (m i)
include h0 hPortion hRate hTail hBand hPlaced hm hc H hJ hfit hfar hBudget hf hz hα hP' hFusion hK' hK
set_option maxRecDepth 100000
lemma price_mixed : ‖evaluation S (∏ i:Fin b,let V:=S.classTokens ∘ v i; let w:=charge (v i) (d i) (m i); match g i with
     | .raw=> Scene.packet S V (xe i) (z i)
     | .fused=> insertion S (z i) (α i)
     | .signed=> (w:ℂ) • Scene.packet S V (xe i) (z i) - insertion S (z i) ((w:ℝ) • (D i).apply V (points (xe i))))‖ ≤ cash P K * ∏ i:Fin b,scaleMap g A (fun i=>(ρ i)^(-(mass (v i):ℝ)-ε)) P i:=by
     have hu0 (i:Fin b):∃ (x:Fin (n i)→ Cover)(u:ℕ×ℕ → C.book.Ref (d i))(Q:ℝ),((g i=.signed)→ (xe i=C.S.gridPoint (j i) ∘x ∧ (∀ a:Axis,Injective (fun k:Fin (n i)=>xe i k a)) ∧ Wage F C (Loss C (j:=j i) x (v i) (w' i) u) J (A i))) ∧ (∀ᶠ t in F.fuse,‖u t‖ ≤ Q):=by
           by_cases h:g i=.signed
           · obtain ⟨x,u,Q,hr,hy,he,hW⟩:= (hPortion i).abort _ (h0 i) (hTail i) _ (hBand _ (h.symm ▸ (by decide))) (hPlaced i h)
             exact ⟨x,u,Q,fun _=>⟨hr,hy,hW⟩,he⟩
           exact ⟨0,0,0,fun h'=>False.elim (h h'),Eventually.of_forall (fun i=>by simp)⟩
     choose x u Q hu hA' using hu0
     obtain ⟨Q',hQ'⟩:= Finite.bddAbove_range Q
     obtain ⟨L,hL,ht,w,hw⟩:= extract_tuple u (F:=F) (show NeBot F.fuse from (by infer_instance)) (le_refl _) (fun i=> (hA' i).mono (fun j hh=> hh.trans (hQ' (Set.mem_range_self i))))
     let φ(i:Fin b):S.Field (d i):= if g i=.fused then α i else S.project _ (w i)
     let ψ(i:Fin b):S.Field (d i):= if g i=.signed then (w' i) • (D i).apply (q' i) (points (xe i)) else φ i
     let V(i):=S.classTokens ∘ v i; let W(i):=w' i
     let packs i:=Scene.packet S (V i) (xe i) (z i); let useA (r:Fin b→Mode)(t:∀i,S.Field (d i)):= evaluation S (∏i,Drama.body S (r i) (W i) (packs i) (t i) (z i))
     let D':= scaleMap g A (fun i=>(ρ i)^(-(mass (v i):ℝ)-ε)) P
     have hC(i):0< D' i:= by change 0<scaleMap g A _ P i; unfold scaleMap; split <;> first | exact hRate _| exact hP' _|exact Real.rpow_pos_of_pos (h0 _) _
     have hZ(i:Fin b)(h:g i=.signed): ‖ψ i-φ i‖ ≤ K*D' i:=by
           change ‖ψ i-φ i‖ ≤ K*scaleMap g A _ _ i; unfold ψ φ; rw [if_pos h,if_neg (show g i ≠ .fused from (h.symm ▸ (by decide))), scaleMap,h]
           refine hK i _ _ _ _ _ (hRate i) ?_
           obtain ⟨hr,hx,hU⟩:=hu i h
           exact closed_raw (fl:=L) (x:=x) (u:=u) (y:=w i) D H hm hc lamp hPortion hTail h0 hBand hJ hfit hfar hBudget i h hL hr hx hU (hw i)
     have hwF := (Drama.adjust S H.laws.toSymmetric K D' g z packs W ψ φ (fun i hi=>by simp [ψ,hi]) hK' hC hZ P (fun j=>(hP' j).le) fun r hr u' hU'=> ?_)
     · apply hwF.trans'; refine (le_of_eq (congr_arg _ (congr_arg (evaluation S) (Finset.prod_congr rfl fun i _=>?_))))
       cases hg:g i <;> simp [hg,body,ψ,φ,packs, V, W]
     let f(i:Fin b):= if r i=g i then φ i else u' i
     have hFR(i)(hi:r i=.fused): ‖f i‖ ≤ 1:= by
         by_cases h:r i=g i
         · unfold f φ; simp only [if_pos h,if_pos (h.symm.trans hi)]; exact hα i (h.symm.trans hi)
         simp only [f,if_neg h];exact hU' i h
     let X'(i:Fin b):=if r i=.fused then 0 else xe i
     let u''(k:Fin b)(t:ℕ×ℕ):=if r k=.fused then S.representative _ (f k) else u k t
     let w''(i:Fin b):=if r i=.fused then S.representative _ (f i) else w i
     have he(i):r i=.signed → g i=.signed:=fun h=> Or.elim (hr i) (fun h'=> h'.symm.trans h) (fun h'=>h'.1)
     have he'(i):r i≠.fused → r i=g i:=fun h=> (hr i).resolve_right fun h'=>h h'.2
     have hcost : ‖useA r f‖ ≤ ∏ i, (if r i=g i then D' i else P i):=by
         have hEq i(hrf:r i≠.fused):f i=φ i:=by simp only [f,if_pos (he' i hrf)]
         have hQ (i:Fin b)(hi:r i≠.fused):Band (n i) lamp (ρ i) (X' i):=(show X' i=xe i from if_neg hi).symm ▸ hBand i ((he' i hi) ▸ hi) -- ▸ ?
         have hh:= combined (g:=r) (M:=M) (z:=z) (u:=u'') (w:=w'') (P:=P) (y:=x) ht hPortion hQ hTail h0 (fun i hs=>?_) (fun i hs=>?_) (fun i hs=>?_) ?_ hJ hf hz H hm hL ?_ hc
         · change ‖evaluation S _‖ ≤ _
           convert hh using 1
           · apply congr_arg; apply congr_arg (evaluation S); apply Finset.prod_congr rfl
             intro i hi
             change body S _ _ _ _ _ = expression _ _ _ _ _ _
             unfold w'' X' packs body expression; split
             next hs=> rw [hEq _ (hs.symm ▸ (by decide))]; unfold φ; simp [he i hs,hs,V,W]
             next hs=> simp [hs,V]
             next hs=> simp [hs,S.rep ..]
           apply Finset.prod_congr rfl
           intro i hi
           by_cases h:r i=g i
           · cases hg:g i <;> simp [D',scaleMap,h,hg]
           have hb:r i=.fused ∧ g i=.signed:=((hr i).resolve_left h).symm; simp [h,hb,D',scaleMap]
         · unfold X'; simp only [if_neg (show r i ≠ .fused from (hs.symm ▸ (by decide)))]; exact (hu i (he i hs)).1
         · unfold X'; simp only [if_neg (show r i ≠ .fused from (hs.symm ▸ (by decide)))]; exact (hu i (he i hs)).2.1
         · unfold u''; simp only [if_neg (show r i ≠ .fused from (hs.symm ▸ (by decide)))]; exact (hu i (he i hs)).2.2
         · intro i hi; exact ⟨if_pos hi,(by unfold u''; simp only [if_pos hi]; exact hFusion i (f i) (hFR i hi))⟩
         intro i; by_cases h:r i=.fused
         · unfold u'' w''; simp only [if_pos h]; exact tendsto_const_nhds
         unfold u'' w''; simp only [if_neg h]; exact hw i
     exact hcost
end YM.MultipleContact.ScheduleRow
