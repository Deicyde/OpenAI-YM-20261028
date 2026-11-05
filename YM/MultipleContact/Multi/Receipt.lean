import YM.MultipleContact.Multi.Nodes
import YM.Next.UV_STRESS.Annulus

/-! Cutoff inequalities transported to a fixed, strict configuration of multiple centers. Constituent leaves of uncertified raw branches use micro tilings. One branch may already contain a signed coefficient from merger. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact.Drama
open Function Filter MeasureTheory Lattice Wilson RG Cells Table Extraction Set Script Arbor Flight Scene
open Next.UVStress
open scoped Topology BigOperators Classical ContDiff
variable {b:ℕ}{G:Gauge}{C:Family G}{F:Extraction.Order}{n d l : Fin b→ℕ}{w A:Fin b→ℝ}{g:Fin b→Mode}{v:∀i,Fin (n i)→ C.book.Token}{u:(ℕ×ℕ)  → ∀i, C.book.Ref (d i)}{J M t:ℕ}{z:Fin b→ Cover}{x y:∀i:Fin b,Fin (n i) → Cover}
local notation "I"=>Fin b
private lemma liftLate {P:ℕ→ℕ→Prop} {q: Filter (ℕ×ℕ)}(h:∀ᶠ p:ℕ in atTop,∀ᶠ N:ℕ in atTop,P N p)(hq:q ≤ F.fuse):∀ᶠ i:ℕ×ℕ in q, P i.1 i.2:=by
         refine Eventually.filter_mono hq ?_; rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually h] with p hp; exact (F.mesh.cofinal.eventually hp)
lemma exact_grid (hC:C.Makes)(hfit:(b:ℝ)*(6*C.S.a J) < C.S.a M)(hM:M ≤ J) (hSep:far (C.S.a M) (C.S.gridPoint t ∘ z))
   {q: Filter (ℕ×ℕ)}(hq:q ≤ F.fuse)(hW:∀i:I,∀ᶠ k:ℕ×ℕ in q,∃ (h:J ≤ k.1), let T:=center C.S k.2 h 0;let f:= trial w v u y t (g i) i k; Interior (T.chamber 0) f ∧ T.rootTest (C.beta k.1 k.2) f ≤ A i) :
    ∀ᶠk in q, ‖report C (∏ i:I,text n (w i) (g i) i) (loc z y) t (prot v (u k)) k‖≤ ∏ i:I,A i:=by
         have ha:=liftLate (F:=F) (q:=q) (Terrain.rendezvous C hC J M hM z hfit (fun i j hij=> hSep j i hij.symm)) hq
         filter_upwards [eventually_all.mpr hW,ha] with k hk ⟨ho,hq0⟩; rw [report_form]
         refine hq0 (fun i:I=>trial w v u y t (g i) i k) A (fun i=> (hk i).choose_spec)
structure Tickets (C:Family G)(F:Extraction.Order)(w:Fin b→ℝ)(v:∀i,Fin (n i) → C.book.Token)(u:ℕ×ℕ → ∀i, C.book.Ref (d i))(g:I→Mode)
    (J:ℕ)(μ1 μ2 l:I→ℕ)(x:∀i,Fin (n i)→ Cover)(K:∀i,Fin (n i)→ℝ)(A:I→ℝ) : Prop where
    signed (i:I)(hs:g i=Mode.signed): Wage F C (Loss C (j:=l i) (x i) (v i) (w i) (fun k=>u k i)) J (A i)
    fused(i:I)(hs:g i=Mode.fused):Wage F C (Fused C (fun k=>u k i)) J (A i)
    raw (i:I)(hs:g i=Mode.raw):
       J≤ μ1 i ∧ μ1 i ≤ μ2 i ∧
       (2*C.S.a (μ1 i)) < C.S.a J ∧
       (Fintype.card (Signed×Fin (n i)):ℝ)*(6*C.S.a (μ2 i))<C.S.a (μ1 i) ∧
       (∀j:Fin (n i),Wage F C (Unit C (v i j).2) (μ2 i) (K i j)) ∧
       (∏ j:Fin (n i),K i j) ≤ A i
private lemma rawCost (hC:C.Makes) {i:I}{μ₁ μ₂:ℕ}(h: J≤ μ₁ ∧ μ₁ ≤ μ₂ ∧ (2*C.S.a μ₁)< C.S.a J ∧ (Fintype.card (Signed×Fin (n i)):ℝ)*(6*C.S.a μ₂)<C.S.a μ₁)
      (hSmall:∀k:Fin (n i), 8*‖C.S.gridPoint t (y i k)‖ ≤ C.S.a J)(hsep:far (C.S.a μ₁) (C.S.gridPoint t ∘ y i))
      {A:Fin (n i)→ℝ} (hWage:∀j:Fin (n i),Wage F C (Unit C (v i j).2) μ₂ (A j)): Wage F C (trial w v u y t Mode.raw i) J (∏j:Fin (n i),A j):=by
       have hr:=liftLate (F:=F) (Terrain.micro_actual C hC J μ₁ μ₂ h.2.1 h.1 (y i) hSmall (fun k j h=>hsep j k h.symm) h.2.2.2 h.2.2.1 (fun j:Fin (n i)=> (v i j).1)) (le_refl _)
       filter_upwards [hr,eventually_all.mpr hWage] with i' ⟨hk,hm,hpass⟩ hw
       refine ⟨hk,hpass (fun j=>(v i j).2) A (fun j=> (hw j).choose_spec)⟩
private lemma signed_move {i:I}(h:l i≤t)(hx:y i=fun s=>pushSite C.S h (x i s))(hp:ℕ×ℕ) : t ≤ hp.fst→(trial w v u y t Mode.signed i) hp =Loss C (j:=l i) (x i) (v i) (w i) (fun k=>u k i) hp:=fun h'=> by
      funext W;unfold trial Loss; rw [hx]; dsimp only;congr 2; exact Finset.prod_congr rfl fun s hs=>by rw [location_down C.S h h']
lemma wage_eq {tA:ℝ}{f f':Farm C}(h:∀ᶠ i in F.fuse, f i = f' i)(hw:Wage F C f J tA): Wage F C f' J tA:= by filter_upwards [h,hw] with k h ⟨hx,hh⟩; rw [h] at hh; exact ⟨hx,hh⟩
variable {cell1 cell2:Fin b→ℕ}{K:∀i,Fin (n i)→ℝ}
variable {F' : Filter (ℕ×ℕ)} (ht:Tickets C F w v u g J cell1 cell2 l x K A)
include ht
private def admitted (g:I→Mode)(J:ℕ)(μ1:I→ℕ)(y:∀i,Fin (n i)→ E4):Prop:= ∀ i:I,g i=Mode.raw→ (∀s:Fin (n i),8*‖y i s‖< C.S.a J)∧ far (C.S.a (μ1 i)) (y i)
private lemma receiveWages (hC:C.Makes) (hs:∀i,g i=Mode.signed→∃h:l i≤ t,y i=fun s=> pushSite C.S h (x i s))
    (ha:admitted (C:=C) g J cell1 (fun i=>C.S.gridPoint t ∘ y i)): ∀i:I,Wage F C (trial w v u y t (g i) i) J (A i):= by
       intro i; cases hgi:g i
       · obtain ⟨h,hG⟩:=hs i hgi; refine wage_eq ( ((large_mesh F t).mono fun imp hh=>(signed_move h hG imp hh).symm)) (ht.signed i hgi)
       · obtain ⟨hh,hq,he,hB',hP,hA⟩:=ht.raw i hgi
         have hz' := rawCost (w:=w) (u:=u) hC ⟨hh,hq,he,hB'⟩ (fun j=>(ha i hgi).1 j |>.le) (ha i hgi).2 hP
         filter_upwards [hz'] with i ⟨h,h'⟩; exact ⟨h,h'.1,h'.2.trans hA⟩
       exact ht.fused i hgi

variable {xe:∀ i,Fin (n i)→ E4}
def Settled (C:Family G)(M:ℕ)(xe:∀i,Fin (n i)→ E4)(g:I→Mode):Prop:= (∀ i,g i≠ Mode.fused→ Injective (xe i)) ∧ ∀ i,∀s, ‖xe i s‖≤C.S.a M
omit ht in
private lemma far_tends {xe:I→ E4}{z:ℕ→I→ E4}{a:ℝ}(h:far a xe)(he:∀i,Tendsto (z · i) atTop (𝓝 (xe i))): ∀ᶠ k in atTop,far a (z k):=by
       suffices ∀ᶠ k in atTop,∀ p:{u:I×I // u.fst ≠ u.snd}, 4*a < ‖z k p.val.fst-z k p.val.snd‖ from this.mono fun i hi s t h=>hi ⟨(s,t),h⟩
       exact eventually_all.mpr fun ⟨⟨b,e⟩,hh⟩=> ((he b).sub (he e)).norm.eventually (lt_mem_nhds (h _ _ hh))
omit ht in
private lemma admitted_tends {rent:I→ℕ}(he:admitted (C:=C) g J rent xe) {x':ℕ→ (∀ i,Fin (n i)→ E4)}(hx:∀i,Tendsto (x' · i) atTop (𝓝 (xe i))): ∀ᶠ k in atTop,admitted (C:=C) g J rent (x' k):= by
       have ix : ∀ᶠ k in atTop, ∀s:{i:I //g i=Mode.raw}, ∀ t:Fin (n s.val), 8*‖x' k s.val t‖ < C.S.a J:= eventually_all.mpr fun ⟨i, hi⟩=> eventually_all.mpr fun t=> (((tendsto_pi_nhds.mp (hx i) t).norm.const_mul 8).eventually (gt_mem_nhds ((he i hi).1 t)))
       exact (ix.and (show ∀ᶠ k in atTop,∀s:{i:I // g i=Mode.raw},far (C.S.a (rent s.val)) (x' k s) from eventually_all.mpr fun i=>far_tends ((he i.val i.property).2) (tendsto_pi_nhds.mp (hx i)))).mono fun k ⟨ha,hb⟩ i hi=>⟨ha ⟨i,hi⟩,hb ⟨i,hi⟩⟩

omit ht in
private lemma render_templates {S:Table C.book} (x:ℕ→∀i,Fin (n i)→ E4){s:ℕ→I→ E4}{z:I→ E4}(hs:∀i,Tendsto (s · i) atTop (𝓝 (z i)))(hy:∀i,Tendsto (x · i) atTop (𝓝 (xe i))) (H:S.Hierarchy) (hF:far (C.S.a M) z)(hG': Settled C M xe g)
   (v:∀i,Fin (n i)→ S.Tag)(W:Π i,S.Field (d i))(w:I→ℝ):
    Tendsto (fun t=>render S (∏ i:I,text n (w i) (g i) i) (site (s t) (x t)) (token v W)) atTop (𝓝 (render S (∏ i:I,text n (w i) (g i) i) (site z xe) (token v W))):=by
         let program:=∏ i:I,text n (w i) (g i) i
         let K(i):Set E4:={x | ‖x - z i‖ ≤ C.S.a M}
         have hv : Admissible (site z xe) univ program:= allowed_full (W:=E4) (disj_sites hF (K:=K) (fun _ _=>id)) w g ?_ ?_
         · refine (render_cont S H program (token v W) (site z xe) hv).tendsto.comp (tendsto_pi_nhds.mpr (fun i=>?_))
           rcases i with ⟨i,k⟩; rcases k with _|k
           · exact hs ..
           exact ((tendsto_pi_nhds.mp (hy i) k).add (hs i))
         -- allowed_full demands range for ALL letters including nonexistent raw; use weakened K? actual fused with noninjective extras. Need different lemma. replace
         · intro i j; rcases j with _|j
           · simpa only [site,K,sub_self,norm_zero,Set.mem_setOf_eq] using (C.S.a_pos M).le
           have he:= hG'.2 i j
           change ‖(xe i j+z i)-z i‖ ≤ _; simpa using he
         exact fun i hi k j e=> (hG'.1 i hi) ((add_right_cancel (show xe i k+ _=xe i j+_ from e)))
private lemma tends_budget {P:Filter (ℕ×ℕ)}(hb:P ≤ F.fuse){S:Table C.book}(H:S.Hierarchy)(href:F.PointLimits C S)(U: Symbols n → Cover)
       {v0:Π i, C.book.Ref (d i)}(hv:∀i,Tendsto (u · i) P (𝓝 (v0 i)))(hp:Flight.prevent (∏i:I,text n (w i) (g i) i) (C.S.gridPoint t ∘ U)):
       Tendsto (fun k=> report C (∏i,text n (w i) (g i) i) U t (prot v (u k)) k) P (𝓝 (render S (∏ i,text n (w i) (g i) i) (C.S.gridPoint t ∘ U) (token (fun i=>S.classTokens∘ v i) (fun i=>S.project _ (v0 i))))):=by
          let D(i:Symbols n):ℕ:=match i with | ⟨i,none⟩=> d i | ⟨i,some s⟩=>(v i s).fst
          let value (v0:∀ i, C.book.Ref (d i))(i:Symbols n):C.book.Ref (D i):=match i with | ⟨i,none⟩=>v0 i | ⟨i,some j⟩=>(v i j).snd
          have he(i v'):⟨D i,value v' i⟩=prot v v' i:=by rcases i with ⟨i,s⟩; cases s <;> rfl
          have hT (i): Tendsto (fun k=> value (u k) i) P (𝓝 (value v0 i)):=by rcases i with ⟨i,s⟩; rcases s with _|s; exact hv _; exact tendsto_const_nhds
          have hh : (fun p=>(⟨D p,S.project (D p) (value v0 p)⟩:S.Tag)) = token (fun i=>S.classTokens∘v i) (fun i=>S.project (d i) (v0 i)) := by
              funext i; exact congr_arg S.classTokens (he i _ ) |>.trans (word_eq v v0 S i).symm
          have hv:= Flight.through F H href hb _ U t D (fun p k=>value (u k) p) (value v0) hT hp
          rw [hh] at hv; change Tendsto (fun k=>report C _ _ _ ((fun k=>prot v (u k)) k) _) _ _; rw [show (fun k=>prot (C:=C) v (u k))=(fun k i=> (⟨D i,value (u k) i⟩:C.book.Token)) from funext fun k=> funext fun i=>(he ..).symm]
          exact hv
variable {fl:Filter (ℕ×ℕ)}[hf:fl.NeBot]{v0:Π i, C.book.Ref (d i)}
variable {s:Fin b→ E4}
set_option maxHeartbeats 1800000
lemma passage {S:Table C.book}(H:S.Hierarchy)(href:F.PointLimits C S)(hb':fl ≤ F.fuse)
       (hv:∀i,Tendsto (u · i) fl (𝓝 (v0 i))) (hC:C.Makes)(hM:M ≤ J)(hfit: b*(6*C.S.a J) < C.S.a M)(hFar:far (C.S.a M) s)
       (hR:∀i,g i=Mode.signed→ xe i=C.S.gridPoint (l i) ∘ x i)(hA:∀i,g i=Mode.signed→∀a:Axis,Injective ((fun u:E4=>u a) ∘ xe i))(ha:admitted (C:=C) g J cell1 xe)(hconfig:Settled C M xe g):
        ‖evaluation S (∏i:Fin b,expression (S:=S) (g i) (w i) (S.classTokens ∘ v i) (S.project (d i) (v0 i)) (s i) (xe i))‖ ≤ ∏ i,A i:= by
        let V(i):=S.classTokens ∘ v i; let p(i):=S.project (d i) (v0 i)
        let code := ∏i:I,text n (w i) (g i) i
        obtain ⟨z₀,x₀,hz,hX,hRest⟩:= coordinates xe s l g x hR hA
        let zi(t):= C.S.gridPoint t ∘ z₀ t; let xi(t i):= C.S.gridPoint t ∘ x₀ t i
        suffices hv : ‖render S code (site s xe) (token (S:=S) V p)‖ ≤(∏ i:I,A i) by
           have he:Script.rewrite (fun i:Symbols n=>(token (S:=S) V p i,site s xe i)) code = ∏ i:Fin b,expression (S:=S) (g i) (w i) (V i) (p i) (s i) (xe i):= by
              exact (map_prod (Script.rewrite (fun i:Symbols n=>(token (S:=S) V p i,site s xe i))) (fun i=>text n (w i) (g i) i) Finset.univ).trans
                 (Finset.prod_congr rfl fun i _=> Drama.step (S:=S) (n:=n) (w i) (g i) V p s xe i)
           exact hv.trans' (Eq.trans_le (congr_arg (fun a=> ‖evaluation S a‖) he.symm) (le_refl _))
        have far_now := far_tends (xe:=s) hFar hz
        have now := admitted_tends ha hX
        refine le_of_tendsto (render_templates (M:=M) xi hz hX H hFar hconfig V p w).norm ?_
        filter_upwards [hRest,far_now,now] with t ⟨K,hg,hxExact⟩ hFar ha
        change ‖render S code (site (zi t) (xi t)) (token V p)‖ ≤ _
        rw [site_loc (z₀ t) (x₀ t) t C.S]
        have hb:= tends_budget (t:=t) ht hb' H href (loc (z₀ t) (x₀ t)) hv ?_
        · exact le_of_tendsto (x:=fl) (hb.norm) (exact_grid (t:=t) hC hfit hM hFar hb' fun i:I=> ((receiveWages ht hC hxExact ha i).filter_mono hb'))
        intro a
        obtain ⟨K,hK,hϵ⟩:= K a
        rw [← site_loc (z₀ t) (x₀ t) t C.S]; exact allowed_full hϵ w g (fun i j=>hK ⟨i,j⟩) (fun i _=> hg i ..)
end YM.MultipleContact.Drama
#print axioms YM.MultipleContact.Drama.passage
