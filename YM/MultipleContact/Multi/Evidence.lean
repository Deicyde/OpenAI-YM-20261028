import YM.MultipleContact.Multi.Invoice

/-! Physical normalization at the grid snapshots. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
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
variable [∀i:Fin b,Inhabited (Fin (n i))]
def scaledBranch (g:Mode) {n d:ℕ}(v:Fin n → S.Tag)(D:Detector S d)(w:ℝ)(z:E4)(xe:Fin n→E4)(u:S.Field d) : Grammar (Alpha S) :=
       match g with | .raw=> Scene.packet S v xe z | .fused=> insertion S z u | .signed=> (w:ℂ) • Scene.packet S v xe z - insertion S z (w • D.apply v (points xe))
private lemma scaled_read (H:S.Hierarchy)(g:Mode){k d:ℕ}(v:Fin k → S.Tag)(D:Detector S d)(w:ℝ)(z:E4)(xe:Fin k→E4)(u:S.Field d):
      Indist S (scaledBranch g v D w z xe u) (if cEq:g=.signed then (w:ℂ) • scaledBranch g v D 1 z xe u else scaledBranch g v D 1 z xe u):= by
        unfold scaledBranch; split
        · simp [Indist]
        · simp [Indist]
        intro f; simp only [dite_true] -- transport notation perhaps if dependent? use dite
        simp only [dite_true, smul_mul_assoc,sub_mul,map_sub,map_smul,one_smul,Complex.ofReal_one,insertion]
        rw [show w • D.apply v (points xe)=(w:ℂ) • D.apply v (points xe) from rfl]; rw [inline_smul S H.laws.toSymmetric]
        all_goals rw [smul_sub]
private lemma trueWeight (H:S.Hierarchy)(g:Fin b→Mode)(v:∀i:Fin b,Fin (n i) → S.Tag)(D:∀i:Fin b,Detector S (d i))(w r:Fin b→ℝ)(h:∀i:Fin b,r i>0)(z:Fin b→E4) (xe:∀i:Fin b,Fin (n i)→E4)(u:∀i,S.Field (d i))(hw:∀i:Fin b,0< w i)
    (t:ℝ)(ht:0<t)(hs:‖evaluation S (∏i:Fin b,scaledBranch (g i) (v i) (D i) (w i) (z i) (xe i) (u i))‖≤t*∏i:Fin b,r i):
       ‖evaluation S (∏ i:Fin b,scaledBranch (g i) (v i) (D i) 1 (z i) (xe i) (u i))‖ ≤ t*∏ i:Fin b,if g i=.signed then r i/w i else r i:=by
       let e(i:Fin b):=if g i=.signed then w i else 1
       have hl: (∏ i:Fin b,e i)> (0:ℝ):=Finset.prod_pos fun i _=> by unfold e;split;exact hw i;exact zero_lt_one
       let f(t:ℝ)(i:Fin b):=scaledBranch (g i) (v i) (D i) t (z i) (xe i) (u i)
       have he: Indist S (∏ i:Fin b,f (w i) i) ((↑((∏i:Fin b,e i):ℝ):ℂ) • ∏ i:Fin b, f 1 i) := by
          rw [show ((↑((∏i:Fin b,e i):ℝ):ℂ))=∏ i:Fin b,(e i:ℂ) from Complex.ofReal_prod .., ← Finset.prod_smul]
          exact prod_indist S (q:=Finset.univ) (fun i _=> by by_cases h:g i=.signed <;> simpa [h,e,f] using! scaled_read H (g i) (v i) (D i) (w i) (z i) (xe i) (u i)) -- replace
       have hs:=hs
       change ‖evaluation S (∏ i:Fin b,f (w i) i)‖ ≤ _ at hs
       rw [reading_eq S he,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl] at hs
       have he': (∏ i:Fin b,if g i=.signed then r i/w i else r i)=(∏ i:Fin b,r i)/(∏i:Fin b,e i):=by rw [← Finset.prod_div_distrib]; apply Finset.prod_congr rfl; intro i _; by_cases h: g i = .signed <;> simp [e,h]
       apply (le_div_iff₀ hl).mpr (show _ from hs.trans' (le_of_eq (mul_comm ..))) |>.trans; rw [he',mul_div_assoc]
variable {v:∀i:Fin b,Fin (n i) → C.book.Token}
variable (D : ∀ i:Fin b,Detector S (d i))
variable (hA:Acme.Aroma C)(hT:Treasury C){ε:ℝ}
variable (hF:CellHyp C F)(H:S.Hierarchy)(hm:F.PointLimits C S)(hc:C.Makes)
variable (lamp:Lattice.Side)
include hA
lemma signed_power (i:Fin b)(β:ℝ)(hβ:β<1/32) (E:ℕ→ℝ) (h:Note C.S E (-1/32)):
     ∀ᶠ m in atTop,∀ρ:ℝ,tail C ρ m→ E m / charge (v i) (d i) m ≤ ρ^(-(mass (v i):ℝ)+(d i)+β):=by
       let g t:= fuga C.path.levels (t+1); let z t:= topZone C.path.levels (C.S.block t) (t+1)
       let q:ℝ := -(mass (v i):ℝ) + (d i:ℝ)
       have he:= h.splits (hA.notes.powr (-q)); have hg:=hA.notes.powr (q+β); have hz:=(Local.topNote hA.notes).powr (q+β)
       have hu:(-1/32:ℝ) - (-q)*-1 <(q+β)*-1:= by linarith only [hβ]
       filter_upwards [he.outweigh hz hu,he.outweigh hg hu] with m hm h'm ρ ⟨hx,hx'⟩
       change _ ≤ ρ^(q+β); rw [charge,show (mass (v i):ℝ) - ↑(d i)= -q by unfold q; ring] -- check
       have hρ:(0:ℝ)<ρ:= (hA.notes.pos _).trans_le hx
       by_cases hq:0≤ q+β
       · exact h'm.trans (Real.rpow_le_rpow (hA.notes.pos _|>.le) hx hq)
       exact hm.trans (Real.rpow_le_rpow_of_nonpos hρ hx' ((not_le.mp hq).le))
omit hA in
lemma make_room {P : Fin b → ℝ}{J:ℕ} (hRoom:∀i:Fin b,∀q:C.book.Ref (d i),‖q‖ < ‖LinearMap.toContinuousLinearMap (S.representative (d i))‖+1 → Drama.Wage F C (Drama.Unit C q) J (P i)):
      ∀ i:Fin b,∀ u:S.Field (d i),‖u‖≤1 → Drama.Wage F C (Drama.Unit C (S.representative _ u)) J (P i):= by
          intro i u hu; apply hRoom
          exact ((LinearMap.toContinuousLinearMap (S.representative (d i))).le_opNorm u).trans_lt ((mul_le_of_le_one_right (norm_nonneg _) hu).trans_lt (lt_add_of_pos_right _ zero_lt_one))
include hT hF H hm hc
set_option maxRecDepth 100000
lemma engineering (hε:0<ε){κ:ℝ}(hk:0<κ)(g:Fin b→Mode):∃ (Z':ℝ)(t:Fin b→ℝ)(j:Fin b→ℕ→ℕ) (M P':ℕ),0<Z' ∧ 4*C.S.a M < κ ∧ (∀i:Fin b,1< t i ∧ Tendsto (j i) atTop atTop ∧ Tendsto (fun m=> C.S.scale (j i m)/C.S.scale m) atTop (𝓝 (t i))) ∧
         ∀ (m:Fin b→ ℕ)(ρ:Fin b→ℝ), (∀i,P' ≤ m i ∧ 0<ρ i ∧ tail C (ρ i) (m i))→ ∀(z:Fin b→ E4),Drama.far (C.S.a M) z → ∀xe:∀i:Fin b,Fin (n i)→ E4, (∀ i:Fin b,g i≠.fused→Band (n i) lamp (ρ i) (xe i))→(∀i:Fin b,g i=.signed→∀l,Placed (n i) (C.S.a (j i (m i))) (xe i) l) → ∀ h:∀i:Fin b,S.Field (d i),(∀i:Fin b,g i=.fused→‖h i‖≤1)→
         ‖evaluation S (∏ i:Fin b,scaledBranch (g i) (S.classTokens ∘ v i) (D i) 1 (z i) (xe i) (h i))‖ ≤ Z'*∏ i:Fin b, scaleMap g (fun i=>(ρ i)^(-(mass (v i):ℝ)+(d i)+1/64)) (fun i=>(ρ i)^(-(mass (v i):ℝ)-ε)) (fun i=>(1:ℝ)) i:= by
         let Q(i):= ‖LinearMap.toContinuousLinearMap (S.representative (d i))‖+1
         obtain ⟨M,J,P,hκ,hJ,hfit,hP,B,hb,hbudget⟩:=layout D Q (fun i=>by unfold Q;exact add_pos_of_nonneg_of_pos (norm_nonneg (LinearMap.toContinuousLinearMap (S.representative (d i)))) one_pos) κ hk hF
         choose A t j ht hj hJ' ha hr using fun i:Fin b=> portion hA hT lamp J hε hF (h:=d i) (v:=v i)
         obtain ⟨K,hK,hC⟩:=decode_hold (n:=n) D B
         obtain ⟨P',hq⟩:=eventually_atTop.mp (eventually_all.mpr hr|>.and (eventually_all.mpr fun i=>signed_power (v:=v) (d:=d) hA i (1/64) (by norm_num) _ (ha i))) -- uses And under upper binder,
         let H' := ∏i:Fin b, max 1 (P i)
         let Z':=cash P K
         have hP' : 0 < H':=Finset.prod_pos fun i hi=>lt_of_lt_of_le zero_lt_one (le_max_left ..)
         have hZ': 0 < Z':=by unfold Z' cash; apply mul_pos; exact_mod_cast (show 0 < Fintype.card (Fin b→Fin 2) from Fintype.card_pos_iff.mpr (by infer_instance)); exact Finset.prod_pos fun i hi=>lt_of_lt_of_le zero_lt_one (le_max_left ..)
         refine ⟨Z'*H',t,j,M,P',mul_pos hZ' hP',hκ,fun i=>⟨ht i,hj i,hJ' i⟩,?_⟩
         rintro m ρ hm' z hz xe hConfig hGrid u hu
         have hL(i):=(hq (m i) (hm' i).1).1 i; have hS (i):=(hq (m i) (hm' i).1).2 i _ (hm' i).2.2 -- syntax replace
         let w(i):=charge (v i) (d i) (m i); let E(i):=A i (m i)
         let Rraw(i):=(ρ i)^(-(mass (v i):ℝ)-ε); let Rsigned(i):=(ρ i)^(-(mass (v i):ℝ)+(d i)+1/64)
         let r0:=scaleMap g Rsigned Rraw (fun _=>1)
         let r1:=scaleMap g E Rraw P
         let r2(i):=if g i=.signed then r1 i/w i else r1 i
         have hE(i:Fin b):0 < E i:= (ha i).pos _
         have hpwr := hA.notes
         have hw(i):0 < w i:=Real.rpow_pos_of_pos (hpwr.pos _) _
         have hBnd:= price_mixed (A:=E) D H hm hc lamp hL (fun i=>(hm' i).2.2) (fun i=>(hm' i).2.1) hConfig hGrid hJ (fun k e=>(hbudget k e).1) (fun k e=>(hbudget k e).2.1) (fun k e=>(hbudget k e).2.2) hfit hz u hu (fun j=> (hP j).1) (make_room (fun i=> (hP i).2)) hE hK hC -- hOrder args hc before H etc.
         let V(i):=S.classTokens ∘ v i
         have hr(i):0<r1 i:=by dsimp [r1,scaleMap]; split; exact hE i; exact Real.rpow_pos_of_pos (hm' i).2.1 _; exact (hP i).1
         have hr0(i):0< r0 i:=by dsimp [r0,scaleMap]; split; exact Real.rpow_pos_of_pos (hm' i).2.1 _; exact Real.rpow_pos_of_pos (hm' i).2.1 _; exact zero_lt_one
         have h0(i):0 < r2 i:=by unfold r2; split; exact div_pos (hr ..) (hw ..); exact hr ..
         change ‖evaluation S (∏ i:Fin b,scaledBranch (g i) (V i) _ (w i) _ _ _)‖ ≤ Z' * (∏ i:Fin b,r1 i) at hBnd -- need cases due match order
         suffices hm' : _ ≤ Z' * (∏ i:Fin b,r2 i) by
           rw [mul_assoc Z']; apply hm'.trans; refine mul_le_mul_of_nonneg_left (((le_of_eq Finset.prod_mul_distrib).trans' (Finset.prod_le_prod (fun i _=>h0 i|>.le) (fun i hi=>?_)))) hZ'.le
           calc _ ≤ (if g i=.fused then P i else 1)*r0 i := by cases heq:g i <;> simp [r1,r2,r0,scaleMap,heq] <;> exact hS i
                _ ≤ _ := mul_le_mul_of_nonneg_right (by split <;> simp only [le_sup_right, le_sup_left]) (hr0 i).le
         apply trueWeight H g V D w r1 hr z xe u hw Z' hZ' hBnd
end YM.MultipleContact.ScheduleRow
