import YM.MultipleContact.Matching.Read

/-! Generic nodes to physical exterior positions in the same estimated chambers. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Local
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Work.A01
open scoped Topology BigOperators Classical
open YM.Next.UVStress
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order} {t d D p J:ℕ}
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable (q:∀i:ι,Fin (n i)→ C.book.Token) (ℓ:∀i:ι,Fin (n i)→ Cover)

omit [Fintype ι] in
lemma cons_generic' {n:ℕ}{y:Points n}{x:E4} (hy:y∈generic n)(he:∀ (a:Axis) i,x a≠y i a): Points.cons x y∈generic _:=by
   intro a i j; refine Fin.cases ?_ (fun i=>?_) i
   · refine Fin.cases (fun _=>rfl) (fun j h=>(he a j h).elim) j
   refine Fin.cases (fun h=>(he a i h.symm).elim) (fun j h=> congr_arg Fin.succ (hy a h)) j

lemma shifted {ι':Type*}[Finite ι'] {y:E4}{n:ι'→ℕ}(hy:∀a:Axis,y a≠0)(z:∀i,Points (n i)) (Q:Schedule): ∃ z':∀k:ℕ,∀i,Points (n i), (∀i,Tendsto (z' · i) atTop (𝓝 (z i))) ∧ ∀ᶠ k in atTop, ∀ i,Points.cons y (Points.cons 0 (z' k i))∈generic (n i + 2):=by
    letI:= Fintype.ofFinite ι'
    let dir:∀ i,Points (n i):=fun i=> points (fun x=>WithLp.toLp 2 (fun a:Axis=>(x.val+1:ℝ)))
    let v(k i):=z i+Q.a k • dir i
    have ht(i): Tendsto (v · i) atTop (𝓝 (z i)):= by simpa [v] using! (Q.shrinks.smul_const (dir i)).const_add (z i)
    have ht'(i) (x:Fin (n i))(a:Axis): Tendsto (fun k=>v k i x a) atTop (𝓝 (z i x a)):=by exact ((show Continuous (fun w:Points _=>w x a) from by fun_prop).tendsto _).comp (ht i)
    have ha(i) (x:Fin (n i))(a:Axis) (c:ℝ):∀ᶠ k in atTop,c≠ v k i x a:=by
       by_cases he:z i x a=c
       · filter_upwards with k; rw [show v k i x a=z i x a+Q.a k * (↑x+1) from rfl,he]
         exact ne_of_lt (lt_add_of_pos_right _ (by have h:=Q.a_pos k; positivity))
       exact ((ht' i x a).eventually (isOpen_ne_fun continuous_const continuous_id|>.mem_nhds (fun h=>he h.symm)))
    have hh (i)(e : {p:Fin (n i)×Fin (n i) | p.1 ≠ p.2})(a:Axis):∀ᶠ k in atTop,v k i e.val.1 a ≠ v k i e.val.2 a :=by
       let x:=e.val.1;let u:=e.val.2
       by_cases h:z i x a=z i u a
       · have hh:(x:ℝ) ≠ (u:ℝ):=by exact_mod_cast (show x.val ≠ u.val from fun h=>e.property (Fin.ext h))
         filter_upwards with k
         change (z i x a+Q.a k * ((x.val:ℝ)+1)) ≠ z i u a+Q.a k *(u.val+1:ℝ)
         rw [h]; intro he; exact hh (by nlinarith only [(Q.a_pos k),he])
       exact (((ht' i x a).prodMk_nhds (ht' i u a)).eventually (isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds h))
    refine ⟨v,ht,?_⟩
    filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (fun x=>eventually_all.mpr (ha i x · 0))), eventually_all.mpr (fun i'=>eventually_all.mpr (fun x=>eventually_all.mpr (fun a=>ha i' x a (y a)))),eventually_all.mpr fun i=> eventually_all.mpr (fun e=>eventually_all.mpr fun a=>hh i e a)] with k h0 hy' hv i
    apply cons_generic' (cons_generic' (?_) (fun a u=>h0 i u a))
    · intro a; exact Fin.cases (hy a) (fun i=>hy' _ i a)
    · intro a x u he
      by_contra h';exact hv i ⟨(x,u),h'⟩ a he

variable (hc:S.Hierarchy)(hp:F.PointLimits C S)
variable (hq:Cells.CellHyp C F)(hC:C.Makes)
variable {r A1 A2 h wt:ℝ}
omit [Fintype ι] in
lemma once_tends {n':ℕ}(q':Fin n' → C.book.Token)(z:Points n') (hz:Points.cons 0 z ∈ conf _) (v:S.Field D)(hc:S.Hierarchy) : ContinuousAt (fun p:Points n' × S.Field D=>once q' ⟨D,p.2⟩ p.1) (z,v):=by
    let b:=Module.finBasis ℂ (S.Field D)
    let g (y:Points n') := YM.Work.A01.frontRead (S.classTokens ∘ q') (Points.cons 0 y) D -- maybe
    have he(y) (k): once q' ⟨D,k⟩ y=∑ i,(b.coord i k)*once q' ⟨D,b i⟩ y:=by
       change _=∑ i, (b.coord i k)* _
       simp_rw [once,disc,← YM.Work.A01.front_eval]; change g y k=∑ i,(b.coord i k)* (g y (b i)); nth_rw 1 [← b.sum_repr k]; rw [map_sum]; exact Finset.sum_congr rfl (fun i _=>(g y).map_smul _ _)
    rw [show (fun p:Points n' × S.Field D=>once (S:=S) q' ⟨D,p.2⟩ p.1)=fun p=>∑ i,(b.coord i p.2)*once q' ⟨D,b i⟩ p.1 from funext fun p=>he p.1 p.2]
    apply tendsto_finsetSum Finset.univ (fun i hi=>?_); refine ContinuousAt.mul (by exact ((b.coord _).continuous_of_finiteDimensional.comp continuous_snd).continuousAt) (?_)
    apply (cont_disc hc _ hz).continuousAt.comp_of_eq (show Continuous (fun p:Points n' × S.Field D => Points.cons 0 p.1) from ?_).continuousAt (by simp)
    exact YM.Work.A02.continuous_cons.comp (continuous_const.prodMk continuous_fst)
omit [Fintype ι] in
include hc in
private lemma pullback {zctx:∀i,Points (n i)}{yPoint:E4}{z':ℕ→∀i,Points (n i)}(ht:∀i,Tendsto (z' · i) atTop (𝓝 (zctx i)))(hconf:∀i,Points.cons yPoint (Points.cons 0 (zctx i))∈conf _)
       {V' B':S.Tag}(he:∀ᶠ k:ℕ in atTop, ∃ v:S.Field D, bonded q V' B' yPoint wt D (z' k) v A1 A2):∃ v:S.Field D,bonded q V' B' yPoint wt D zctx v A1 A2:=by
       classical
       let v (k:ℕ) := if H : ∃w:S.Field D,bonded q V' B' yPoint wt D (z' k) w A1 A2 then H.choose else 0
       have hb:∀ᶠ k in atTop, bonded q V' B' yPoint wt D (z' k) (v k) A1 A2:=by
          filter_upwards [he] with k h
          dsimp [v]; rw [dif_pos h]; exact h.choose_spec
       obtain ⟨b,hB,hh,w,Hw⟩:=finite_extract (𝓛:=atTop) v A1 (hb.mono fun _ h=>h.1)
       refine ⟨w,le_of_tendsto Hw.norm (((hb.mono fun k hk=>hk.1)).filter_mono hB),fun i=>le_of_tendsto (x:=b) ?_ (((hb.mono fun k hk=>hk.2 i)).filter_mono hB)⟩
       have ht(i):= (ht i).mono_left hB
       have hf:=(once_tends (q i) _ (Points.tail_in (hconf i)) w hc).tendsto.comp ((ht i).prodMk_nhds Hw)
       have hx:= (show Continuous (fun x:Points (n i)=>Points.cons yPoint (Points.cons 0 x)) from (YM.Work.A02.continuous_cons.comp (continuous_const.prodMk (YM.Work.A02.continuous_cons.comp (continuous_const.prodMk continuous_id))))).tendsto (zctx i)
       exact ((Tendsto.const_smul ((cont_disc hc _ (hconf i)).continuousAt.tendsto.comp (hx.comp (ht i))) wt |>.sub hf).norm)
variable (hL:∀ i,Injective (Fin.cons (α:=fun _=>Cover) 0 (ℓ i))) (hr:0<r)
include hc hp hC hq hL hr
open Matching
omit [Fintype ι] hc hp hq hC hL hr in
lemma locations_open {u:ℝ}{i:ι}{L:ℕ→Points (n i)}{z:Points (n i)}(ht:Tendsto L atTop (𝓝 z))(hv:Locations C J u (ℓ i) z):∀ᶠ k in atTop,Locations C J u (ℓ i) (L k):=by
    have he (j:Fin _) (a:Axis):∀ᶠ k in atTop,|L k j a-C.S.gridPoint J (ℓ i j) a| < C.S.a J/2-u:=
        (((show Continuous (fun w:Points (n i)=>(w j) a) from by fun_prop).tendsto z).comp ht |>.sub_const (C.S.gridPoint J (ℓ i j) a) |>.abs |>.eventually (gt_mem_nhds (hv j a)))
    exact eventually_all.mpr fun j=>eventually_all.mpr fun i=> he _ _
lemma comparableGrid {m:ℕ}:∃A> (0:ℝ),∀ V B (m j D:ℕ), ∀ h A1 A2:ℝ, Box C J j m D d t h B V F A1 A2 → ∀ y':Cover, (fuga C.path.levels (m+1))/16≤ ‖C.S.gridPoint j y'‖ → ‖C.S.gridPoint j y'‖≤4*topZone C.path.levels (C.S.block m) (m+1) → ∀z:∀i,Points (n i), (∀ i,Locations C J r (ℓ i) (z i))→ (∀ i,Points.cons (C.S.gridPoint j y') (Points.cons 0 (z i))∈conf _) → (∀a:Axis,C.S.gridPoint j y' a≠0) → ∃ v:S.Field D, bonded q ⟨t,S.project t V⟩ ⟨d,S.project d B⟩ (C.S.gridPoint j y') ((fuga C.path.levels (m+1))^h) D z v (‖LinearMap.toContinuousLinearMap (S.project D)‖* A1) (A*A2):=by
    obtain ⟨A,hA,Ha⟩:=readGrid (t:=t) (d:=d) (J:=J) hc hp q hq hC ℓ hL hr
    refine ⟨A,hA,fun V B m j D h A1 A2 hBox y h₁ h₂ z hZ hy hne=>?_⟩
    let b:=C.S.gridPoint j y; let wt:ℝ:=(fuga C.path.levels (m+1))^h -- replace
    let L:=‖LinearMap.toContinuousLinearMap (S.project D)‖*A1
    let P (z) : Prop:=∃v:S.Field D,bonded q ⟨t,S.project t V⟩ ⟨d,S.project d B⟩ b wt D z v L (A*A2)
    obtain ⟨z',hz',hg⟩:=shifted hne z C.S
    apply pullback q hc hz' hy
    have hc' (i) : ∀ᶠ k in atTop, Locations C J r (ℓ i) (z' k i):=locations_open ℓ (hz' _) (hZ i)
    filter_upwards [hg,eventually_all.mpr hc'] with k hk hk'
    let Z:= z' k; let Gm(t i):= Extraction.Order.grid C t (address (C.S.a t) (Z i))
    let v (t i):= address (C.S.a t) (Z i)
    have hT(i):Tendsto (Gm · i) atTop (𝓝 (Z i)):= chosen _
    have hO(i):∀ᶠ t in atTop,Points.cons b (Points.cons 0 (Gm t i)) ∈ generic _:=by
        let u(i) (z:Points (n i)) :=Points.cons b (Points.cons 0 z)
        apply (show Continuous (u i) from (YM.Work.A02.continuous_cons.comp (continuous_const.prodMk (YM.Work.A02.continuous_cons.comp (continuous_const.prodMk continuous_id))))).continuousAt.tendsto.comp (hT i) |>.eventually ((genericOpen _).mem_nhds (hk i))
    apply pullback q hc hT (fun i=>generic_conf _ (hk i))
    filter_upwards [eventually_all.mpr hO,eventually_all.mpr fun i=> locations_open ℓ (hT i) (hk' i)] with t ht hu
    apply Ha V B _ _ _ _ _ _ hBox (v t) t (fun i=>?_) y h₁ h₂ _ (fun i=>rfl) hu ht
    rw [show Extraction.Order.grid C t (Fin.cons 0 (v t i))= Points.cons 0 (Gm t i) from ?_]
    · intro a j k h; exact Fin.succ_inj.mp (ht i a (show Points.cons b _ j.succ a=_ from h))
    ext1 j; refine Fin.cases ?_ (fun k=>rfl) j
    change C.S.gridPoint t 0=0
    ext1 i; change C.S.a t*((↑(0:ℤ)):ℝ)=0; simp
end YM.MultipleContact.Local
