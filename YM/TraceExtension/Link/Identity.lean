import YM.TraceExtension.WilsonTrace

/-! Verification of the unit on the operator domain in Final. Although it
suffices to work with the actual given unit label and its continuation and
centering, here is a check that in operator language it's really doing
identity and subtracting the VEV times identity. Uses holomorphic uniqueness
*before* taking the W distribution boundary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
namespace Identity
open Function Filter MeasureTheory Boundary Set Mink Complex Table
open scoped Topology Classical InnerProductSpace ContDiff NNReal
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}(F:Spec.Final C f S){d n:ℕ}
local notation "T'" => selected F
private def roto (i:Fin (n+1)): Equiv.Perm (Fin (n+1)):= (finSuccEquiv n).trans (finSuccEquiv' i).symm
private lemma roto_at (i:Fin (n+1)) : roto i 0=i:=by simp [roto]
private lemma roto_after (i:Fin (n+1))(j:Fin n): roto i j.succ=i.succAbove j:=by simp[roto]
private def tearAt (i:Fin (n+1))(y: Points (n+1)) : Points n:= points fun j=>y (i.succAbove j)
private lemma east_tear (i:Fin (n+1))(x: Heights (n+1))(h:x∈east (n+1)): (x ∘ i.succAbove) ∈east n:=h.comp (Fin.strictMono_succAbove i)
private lemma strict_tear (i:Fin (n+1))(x: Times (n+1))(h:x∈strict (n+1)): (x ∘ i.succAbove) ∈strict n:=east_tear i (fun j=>(x j).im) h
private lemma use_unit {x:Points (n+1)}(hx:x∈conf (n+1))(i:Fin (n+1))(v:Fin n→S.Tag):
   S.useAt (selected F) x (i.insertNth ⟨d,S.unit d⟩ v)= S.useAt (selected F) (tearAt i x) v:=by
   let q : Fin n→ C.book.Token:=fun i=>⟨(v i).1, S.representative _ (v i).2⟩;let W:= Fin.cons (α:=fun _=>C.book.Token) (C.book.one d) q; let h:= selected_hierarchy F; let r:= roto i
   have he(j):S.classTokens (q j)=v j:=by change (⟨(v j).1,S.project _ (S.representative _ (v j).2)⟩:S.Tag)=_; rw [S.rep]
   have ht: i.insertNth (α:=fun _=>S.Tag) ⟨d,S.unit d⟩ v ∘ r=S.classTokens ∘ W:=by
       funext j; refine Fin.cases ?_ (fun p=>?_) j
       · simp only[Function.comp_apply,r,roto_at,W,Fin.cons_zero,Fin.insertNth_apply_same];rfl
       simp only [Function.comp_apply, W, Fin.cons_succ, he, r, roto_after, Fin.insertNth_apply_succAbove]
   rw [← S.class_perm _ h.laws.toSymmetric r hx, ht]; have hp:=Points.rearrange_in r hx
   rw[S.at_project _ h.laws.toSymmetric (selected_respects F) hp W,h.laws.unital hp d]
   rw[show (Points.rearrange r x).tail=tearAt i x from ?_]; rfl
   ext1 z; change x (r z.succ)=_; rw [show r z.succ=i.succAbove z from roto_after ..];rfl

private lemma waves_unit (i:Fin (n+1))(v:Fin n→S.Union)(x:SpacePoints (n+1)) (d:ℕ) :
    Set.EqOn (fun z : Times (n+1)=> F.A.waves.F _ z x (i.insertNth (S.pin d (S.unit d)) v))
      (fun z : Times (n+1)=> F.A.waves.F _ (z ∘ i.succAbove) (x ∘ i.succAbove) v) (strict (n+1)):=by
   let w:=F.A.waves
   have ht:= F.realization.chosen
   let a':Times (n+1)→ₗ[ℂ] Times n:={toFun:=fun r=> r ∘ i.succAbove,map_add':=fun _ _=> rfl, map_smul':= fun _ _=> rfl}
   let b:=LinearMap.toContinuousLinearMap a'
   apply Next.BOUNDARY.ordered_eq _ _ (ht.heat.hol _ _ _) ((ht.heat.hol _ _ _).comp b.differentiable.differentiableOn (strict_tear i))
   intro t he
   obtain ⟨d',u,hu⟩:= F.sector.derivatives.joint F.room.kernel.laws.toSymmetric F.phase.transport.injection v
   let U(j):S.Tag:=⟨d',u j⟩
   have hz:v=fun j=> S.pin (U j).1 (U j).2:=hu
   let V:= i.insertNth (α:=fun _=>S.Tag) ⟨d,S.unit d⟩ U
   have hh:i.insertNth (α:=fun _=>S.Union) (S.pin d (S.unit d)) v= fun j => S.pin (V j).1 (V j).2:=by
       funext j
       induction j using Fin.succAboveCases i
       next => rw [Fin.insertNth_apply_same,show V i=⟨d,S.unit d⟩ from Fin.insertNth_apply_same ..]
       next j => rw [Fin.insertNth_apply_succAbove, show V (i.succAbove j)=U j from Fin.insertNth_apply_succAbove ..,hz]
   rw [hh,ht.heat.roots _ V _ t he,hz]
   change _=F.A.waves.F _ (fun j=> (↑((t ∘ i.succAbove) j):ℂ)*I) _ _
   rw[ht.heat.roots _ U _ _ (east_tear i t he)]
   unfold V; rw [use_unit F (clear he x)];rfl

private lemma slopes_unit (i:Fin (n+1))(d:ℕ)(v:Fin (n+1)→S.Union) (t:Fin (n+1)→Test4)(hv:v i=S.pin d (S.unit d))(p: Heights (n+1))(hp:p∈east (n+1))(s:ℝ)(hs:0<s):
    F.A.waves.atSlopes v p s (Joint.materialize _ t) = (∫ x:E4,t i x) * F.A.waves.atSlopes (v ∘ i.succAbove) (p ∘ i.succAbove) s (Joint.materialize n (t ∘ i.succAbove)):=by
    let k:= (fun _ : Fin (n+1)=> E4)
    let w:=F.A.waves; let q:=v∘i.succAbove; let X x:= w.restricted q (s • (p ∘ i.succAbove)) x* Joint.materialize n (t∘i.succAbove) x; let Z(y:E4 × (Fin n→E4)):= t i y.1 * X (points y.2)
    let A:= (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1)=> E4)).toHomeomorph.toMeasurableEquiv; let E := A.trans (MeasurableEquiv.piFinSuccAbove k i)
    have hE:MeasurePreserving E volume volume:= (volume_preserving_piFinSuccAbove k i).comp (Points.volume_product (n+1))
    have hV:v=i.insertNth (α:=fun _=>S.Union) (S.pin d (S.unit d)) q:= by funext j; induction j using Fin.succAboveCases i <;> simp [hv,q]
    have hH(x:Points (n+1)) : w.restricted v (s • p) x= w.restricted q (s • (p ∘ i.succAbove)) (tearAt i x):=by
        unfold Waves.restricted; rw [hV]; exact waves_unit F i q (trace x) d (on_profile _ _ _ hs hp)
    unfold Waves.atSlopes
    calc
       _ = ∫ x:Points (n+1), Z (E x):=by
          apply integral_congr_ae; refine ae_of_all _ fun x=>?_ 
          change F.A.waves.restricted _ _ _ * _ = Z (E x)
          rw [show F.A.waves.restricted _ _ _=_ from hH x, Joint.material_at,i.prod_univ_succAbove _]; unfold Z X; rw [Joint.material_at]; change _ = t i (x i) * _; exact mul_left_comm _ _ _
       _ = ∫ y:E4 × (Fin n→ E4), Z y := hE.integral_comp E.measurableEmbedding Z
       _ = (∫ x:E4,t i x)*(∫ y: Fin n→ E4,X (points y)):=by unfold Z; exact integral_prod_mul (μ:=volume) (ν:=volume) (t i) (fun x=>X (points x))
       _ = _:=by
          congr 1; let B:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=> E4)).toHomeomorph.toMeasurableEquiv
          have ht:MeasurePreserving B volume volume:= Points.volume_product n
          exact ht.symm.integral_comp B.symm.measurableEmbedding X
lemma erase_unit (i:Fin (n+1))(d:ℕ)(v:Fin (n+1)→S.Union)(t:Fin (n+1)→Test4)(hv:v i=S.pin d (S.unit d)):
    F.A.world.W (n+1) v (Joint.materialize _ t)= (∫ x:E4,t i x)* F.A.world.W n (v ∘ i.succAbove) (Joint.materialize n (t ∘ i.succAbove)):=by
    let h:=F.realization.chosen; let p: Heights (n+1):=fun i=>(i.val:ℝ)
    have he:p∈east _:=fun i j hi=> by simpa only [p,Nat.cast_lt] using (show i.val<j.val from hi)
    have hz:= h.emerges.profile _ v p he (Joint.materialize _ t)
    refine tendsto_nhds_unique hz ?_; exact ((h.emerges.profile _ (v∘i.succAbove) _ (east_tear i p he) (Joint.materialize n (t∘i.succAbove))).const_mul _).congr' ((show ∀ᶠ s:ℝ in 𝓝[>] 0,0 < s from self_mem_nhdsWithin).mono fun j hj=> (slopes_unit F i d v t hv p he j hj).symm)

private lemma surf_get (W:Surface S)(v: Fin n → Letter S) :
    W.expect (List.ofFn v)= W.W n (Prod.fst ∘ v) (Joint.materialize n (Prod.snd ∘ v)):=by
   unfold Surface.expect
   let l:=List.ofFn v
   have hz : l.length=n:=List.length_ofFn
   have hP {A B:ℕ}(v: Fin A→ Letter S)(u: Fin B→Letter S)(h:A=B)(hu:∀ i, v i=u (Fin.cast h i)): W.W A (fun i=>(v i).1) (Joint.materialize A fun i=>(v i).2)= W.W B (fun i=> (u i).1) (Joint.materialize B fun i=>(u i).2):=by
       subst B; have ht:v=u:= funext hu;rw[ht]
   refine hP (fun i=> l.get i) v hz ?_
   intro i; simp[l,List.get_eq_getElem]; rfl

private lemma spell {X:Type*}(u v:List X)(p:X):∃ i:Fin ((u++v).length+1),
    let f:=i.insertNth (α:=fun _=>X) p (u++v).get
    List.ofFn f = u++ p::v:=by
   induction u with
   | nil=>
     change ∃ i:Fin (v.length+1),_
     refine ⟨0,?_⟩; intro f
     have hh:Fin.tail f=v.get:= funext fun j=> by rw [Fin.tail]; unfold f; simp
     rw [List.ofFn_succ]; change f 0 :: List.ofFn (Fin.tail f)= _; exact congr_arg₂ List.cons (by unfold f; simp;rfl) ((congr_arg List.ofFn hh).trans (List.ofFn_get v))
   | cons x u ih=>
     change ∃ i:Fin ((u++v).length+1+1),_
     obtain ⟨i,hI⟩:= ih
     let g:=i.insertNth (α:=fun _=>X) p (u++v).get
     refine ⟨i.succ,?_⟩; intro f
     have ht:f 0=x:=by change i.succ.insertNth (α:=fun _:Fin ((u++v).length+2)=>X) p (fun j => (x::(u++v)).get j) 0=x; rw [← show (i.succ).succAbove 0=(0:Fin ((u++v).length+2)) from Fin.succ_succAbove_zero _,Fin.insertNth_apply_succAbove]; rfl
     have hx: Fin.tail f=g:=by
        funext j; induction j using Fin.succAboveCases i
        next=> simp [Fin.tail,f,g]
        next j=> change i.succ.insertNth (α:=fun _:Fin ((u++v).length+2)=>X) p (fun j=> (x::(u++v)).get j) ((i.succAbove j).succ)= _; unfold g; rw[← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove,Fin.insertNth_apply_succAbove];rfl
     rw[List.ofFn_succ]; change f 0 :: List.ofFn (Fin.tail f)= _;rw[ht]; change x :: List.ofFn (show Fin ((u++v).length+1) → X from Fin.tail f)=x::(u++p::v); congr 1; exact (congr_arg List.ofFn hx).trans hI
lemma expect_unit (u v:Sentence S)(p: Test4) : F.A.world.expect (u++(S.pin d (S.unit d),p)::v)= (∫ x,p x) * F.A.world.expect (u++v):=by
    let W:=F.A.world; let g:= S.pin d (S.unit d); obtain ⟨i,hI⟩:= spell u v (g,p); let n:=(u++v).length; let y:Fin n → Letter S:=(u++v).get; let K:=i.insertNth (α:=fun _=>Letter S) (g,p) y
    have he:K i=(g,p):=Fin.insertNth_apply_same ..
    rw[← show List.ofFn K= _ from hI,surf_get,(congr_arg F.A.world.expect (List.ofFn_get (u++v))).symm]
    change _= (∫ x,p x)* W.expect (List.ofFn y)
    rw[surf_get]; let L:=Prod.fst ∘ K; let R:=Prod.snd ∘ K;
    have ht : K ∘ i.succAbove=y:= funext fun j=> Fin.insertNth_apply_succAbove ..
    have hh:= erase_unit F i d L R (congr_arg Prod.fst he); simp_rw [show R i=p from congr_arg Prod.snd he,show L ∘ i.succAbove=Prod.fst ∘ y from ht ▸ rfl,show R ∘ i.succAbove=Prod.snd ∘ y from ht ▸ rfl] at hh; exact hh

open Fields
private lemma vectors_span (Y:Fields S)(hY:Y.Total) : Submodule.span ℂ (Set.range Y.evaluates) = ⊤:=by
   let P:=Submodule.span ℂ (Set.range Y.evaluates)
   have hx:(Set.range Y.vector)=Y.domain.subtype '' (Set.range Y.evaluates):= (range_comp _ _)
   apply (Submodule.map_injective_of_injective Y.domain.injective_subtype)
   have hp:=hY.cyclic; rw [hx,Submodule.span_image] at hp
   change P.map _= _; rw[← hp]; simp

lemma op_unit (v:Test4)(d:ℕ) :
    F.action.operators.field (S.pin d (S.unit d)) v= (∫ x,v x) • (LinearMap.id (R:=ℂ)):=by
   let W:=F.action.operators; let ψ:=F.A.world; let J:=F.action.J; let p:= (S.pin d (S.unit d),v); have H:= F.realization.qt; let c:=∫ x,v x
   let D:=W.domain
   have hx(i j:Sentence S): inner ℂ (W.evaluates i) (W.evaluates (p::j))=inner ℂ (W.evaluates i) (c • W.evaluates j):=by
      rw[inner_smul_right]; change inner ℂ (W.vector i) (W.vector (p::j))=c*inner ℂ (W.vector i) (W.vector j)
      rw [W.general _ H.meets _ H.adj,W.general _ H.meets _ H.adj]; exact expect_unit F (Sentence.rev J i) j v
   have hspan : Submodule.span ℂ (range W.evaluates)=⊤:=vectors_span W H.total
   have hm(j:Sentence S): W.evaluates (p::j)=c • W.evaluates j:=by
       refine ext_inner_left ℂ fun x=>?_
       have he:x∈Submodule.span ℂ (range W.evaluates):=hspan ▸ Submodule.mem_top
       induction he using Submodule.span_induction with
       | mem w h=> rcases h with ⟨i,rfl⟩; exact hx i j
       | zero => simp
       | add x y _ _ h1 h2=>simp only[inner_add_left,h1,h2]
       | smul x y _ h=>simp only[inner_smul_left,h]
   ext1 i
   change W.field _ _ i= (c • LinearMap.id (R:=ℂ): D →ₗ[ℂ] D) i
   have he:i∈ Submodule.span ℂ (range W.evaluates):=hspan ▸ Submodule.mem_top
   induction he using Submodule.span_induction with
   | mem x h=> rcases h with ⟨j,rfl⟩; exact hm j
   | zero=> rw[map_zero,map_zero]
   | add x y _ _ hx hy=> rw[map_add,hx,hy,map_add]
   | smul a x _ hx=>rw[map_smul,hx,map_smul]
lemma center_field (v : Test4) :
    F.action.operators.field (pinned F) v = F.action.operators.field (S.pin 4 (stressTrace F.sector.energy)) v -
        (euclideanVEV S (selected F) (stressTrace F.sector.energy) * ∫ x,v x) • LinearMap.id (R:=ℂ):=by
    unfold pinned center theta centerIn; rw [map_sub,map_sub]; rw [map_smul,map_smul]; simp only [LinearMap.sub_apply, LinearMap.smul_apply,op_unit, smul_smul]
lemma vacuum_stress (v: Test4) : inner ℂ F.action.operators.vacuum
    (excitation F.action.operators (S.pin 4 (stressTrace F.sector.energy)) v)= euclideanVEV S (selected F) (stressTrace F.sector.energy)*(∫ x,v x) :=by
   let Y:=F.action.operators; let N:= S.pin 4 (stressTrace F.sector.energy); let Ω:= Y.omega; let c:=euclideanVEV S (selected F) (stressTrace F.sector.energy)*(∫ x,v x)
   have hp:= pinned_centered F v; have ht:inner ℂ Ω Ω=1:=by
       change inner ℂ Y.vacuum Y.vacuum =1; rw [inner_self_eq_norm_sq_to_K,show ‖Y.vacuum‖ = 1 from F.realization.qt.total.norm]; simp
   change inner ℂ Ω ((Y.field N v) Ω) = c
   apply sub_eq_zero.mp; refine Eq.trans ?_ hp
   change _= inner ℂ Ω ( (Y.field (pinned F) v) Ω); rw [show Y.field _ v= _ from center_field F v]; change _=inner ℂ Ω ( (Y.field N v) Ω - c • Ω ); rw [inner_sub_right,inner_smul_right,ht,mul_one]
end Identity
end YM.TraceExtension
#print axioms YM.TraceExtension.Identity.center_field
