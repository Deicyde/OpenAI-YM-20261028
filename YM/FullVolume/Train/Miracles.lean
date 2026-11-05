import YM.FullVolume.Train.Pins
import YM.Next.STATIONARY.Level.Recurse
/-! Pin producers retain convergence in cover coefficient spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Function Lattice Laurent RG Wilson Precision Tree Exterior Bloch Stock
open Craft Next Next.Free Flight Retort Filter Set Matrix
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge}{A: Levels G} {l:ℕ→ℝ}{X K:MapPrices}{B T:Horizon A}
private lemma perunik {X Y:Type} {F:ℕ→ Matrix X Y ℝ} {x y}(h:Tendsto F atTop (𝓝 x))(e:Tendsto F atTop (𝓝 y)):x=y:=by
   letI : T2Space (Matrix X Y ℝ) := inferInstanceAs (T2Space (X→Y→ℝ))
   exact tendsto_nhds_unique h e
def Loom {X Y:Type}(S:ℕ→Row X Y):=∃ R,Tendsto S atTop (𝓝 R)
structure Mite (H:Horizon A) :Prop where
   diagonal m : Loom fun N=>(H.H N m).diagonal
   dual m: Loom fun N=> (H.H N m).dual_diag
   roots m: Loom fun N=> (H.H N m).roots
   metric m: Loom fun N=> (H.H N m).metric
   inverse m: Loom fun N=> (H.H N m).inverse
structure Amplify (H:Horizon A) :Prop extends Mite H where
   prediction m: Loom fun N=> (H.towers N m).A0
   T m: Loom fun N=> (H.towers N m).T
   mf m: Loom fun N=> (H.towers N m).mf
   mn m: Loom fun N=> (H.towers N m).mn
   o m: Loom fun N=> (H.towers N m).o
lemma Loom.copies {X Y:Type}{S Q:ℕ→Row X Y}(h:Loom S)(he:S=ᶠ[atTop] Q): Loom Q:=⟨_,h.choose_spec.congr' he⟩
lemma stellar (h:Exhibits A X B l) (hl:∀ i,0≤ l i): Mite B:=by
    have he(i):∀ᶠ N:ℕ in atTop, Defined A.clock.kernel.penalty (l (A.clock.J i)) (location A N i) (B.H N i):= (eventually_ge_atTop _).mono fun N hx=> h.offered.1 N i hx
    have hs(i):=Retort.dominant A i (l (A.clock.J i)) (hl _)
    have hu (i): Loom fun N=> (B.H N i).metric:= Loom.copies (hs i).2.2.2.2 ((he i).mono fun n ht=> ht.metric.symm)
    refine ⟨fun i=> Loom.copies (hs i).1.2 ((he i).mono fun n ht=>ht.diag.symm),fun i=> Loom.copies (hs i).2.1.2 ((he i).mono fun n ht=>ht.dual.symm),fun i=>?_,hu,fun i=> Loom.copies (hs i).2.2.1.2 ((he i).mono fun n ht=>ht.inverse.symm)⟩
    let j:= A.clock.J i; obtain ⟨F,hF⟩:= hu i
    have H:=X.alpha_pos j
    have hG :Fleet (fun N=> (B.H N i).metric) F (X.α j) (X.Ω j):=⟨hF,H,(eventually_ge_atTop _).mono fun N hi=> (h.classic.covers _ _ hi).2.1⟩
    let W:= fun N=> (B.H N i).roots; have hb n : ∀ᶠ i in atTop,((W i).acts n).PosSemidef:= (eventually_ge_atTop _).mono (fun z hv=> h.vivid _ _ hv n)
    have hp n: ∃ R,Tendsto (fun i=> ((W i).acts n)ᵀ*(W i).acts n) atTop (𝓝 R):=by
        let U:= (A.params i).clip.direct • (1:Matrix (Body 2 n) (Body 2 n) ℝ)
        refine ⟨_,((hG.muster n).sub_const U).congr' ?_⟩; filter_upwards [eventually_ge_atTop i] with z hz; have hx := (h.classic.traces _ _ hz n).roots; rw [full_cover] at hx
        rw [← hx]; change U+_-U=_; abel
    obtain ⟨V,hV⟩:= evening H ((eventually_ge_atTop _).mono (fun n hz=> (h.classic.covers _ _ hz).2.2.2.1)) hb hp; exact ⟨_,hV.hull⟩
private lemma transposeM {X Y: Type}[Fintype X][Fintype Y]{A:ℕ→Matrix X Y ℝ}{r} (he:Tendsto A atTop (𝓝 r)):Tendsto (fun i=>(A i)ᵀ) atTop (𝓝 rᵀ):= (show ContinuousAt transpose r from continuous_id.matrix_transpose.continuousAt).tendsto.comp he
private lemma deliver (h:Exhibits A X B l)(hl:∀ i,0≤l i)(hv: Mite B) (hc: Bid.Retained T B)(hk:T.Suffices K)
   (m:ℕ)(y Xz z:ℝ)(hy:0<y)(hz:0<z) (G':ℕ→C3)(Q:∀ N,m<N→ Bid.Committed l B T N m (G' N) y Xz z):
    Loom (fun N=>(T.towers N m).A0) ∧ Loom (fun N=> (T.towers N m).T) ∧ Loom (fun N=> (T.towers N m).mf)∧ Loom (fun N=> (T.towers N m).mn) ∧ Loom (fun N=> (T.towers N m).o):=by
   obtain ⟨F,σ,c,hF⟩:= Retort.stock_take (angular A m (l (A.clock.J (m+1))) (l (A.clock.J m)) (hl _))
   have he:= eventually_gt_atTop m
   obtain ⟨R,hR⟩:= evening hz (he.mono fun _ ht=>(Q _ ht).strip) (fun n=>he.mono fun i ht=>warmly hy hz (Q _ ht).strip (Q _ ht).funds n)
          (fun n=> ⟨_, (hF.muster n).congr' (he.mono fun i ht=> ((Q _ ht).square n).1)⟩)
   obtain ⟨hp,hS⟩:=concord A m
   have hF0 : Loom (fun N=> (B.towers N m).T):= Loom.copies hS.2 (he.mono fun _ hz=>(h.offered.2 _ _ hz).2.symm)
   refine ⟨Loom.copies hp.2 (he.mono fun n h'=> ((h.offered.2 n m h').1.symm.trans (hc.2 n m h').1.symm)), Loom.copies hF0 (he.mono fun n h'=> (hc.2 n m h').2.symm),?_⟩
   have hk0:= K.alpha_pos (A.clock.J (m+1)); have hV:=X.alpha_pos (A.clock.J (m+1)); have hp:=X.alpha_pos (A.clock.J m)
   obtain ⟨S,hS'⟩:=hF0
   let b:= A.S.block m
   have hZ : ∃ c,Fleet (fun i=>(B.towers i m).T) S (X.α (A.clock.J (m+1))) c := ⟨_,hS',hV,he.mono fun i hh=> (h.classic.legs i m hh [] (by simp)).2⟩
   obtain ⟨c0,hC⟩:=hZ
   have hY i : ∃ F,Fleet (fun n=>(B.H n i).inverse) F (X.α (A.clock.J i)) (X.Ω (A.clock.J i)) :=
       ⟨_,(hv.inverse i).choose_spec, X.alpha_pos _,(eventually_ge_atTop _).mono fun n hx=> (h.classic.covers _ _ hx).2.2.1⟩
   obtain ⟨D,hU⟩:= hY (m+1); obtain ⟨D',hV'⟩:= hY m
   have hh (i) (c:Side): ∃ X,Tendsto (fun n=> (B.H n i|>.full (A.params i).clip c)) atTop (𝓝 X):=by
       let R:= fun n=> (B.H n i).roots
       obtain ⟨S,hS⟩:=hv.roots i
       have hk: Fleet R S (X.α (A.clock.J i)) (X.Ω (A.clock.J i)):= ⟨hS,X.alpha_pos _,(eventually_ge_atTop _).mono fun n hi=> (h.classic.covers _ _ hi).2.2.2.1⟩
       let X := { B.H i i with roots:= S}
       refine ⟨X.full (A.params i).clip c,tendsto_pi_nhds.mpr fun ⟨x,w⟩=>tendsto_pi_nhds.mpr fun j=> ?_⟩
       cases w
       · exact tendsto_const_nhds
       exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hk.muster c) _) _
   have hJ:= Stationary.bound_climb G A m
   let a:= A.S.side m
   have hj : ∃ c F,Fleet (fun n=> (T.towers n m).mf) F (K.α (A.clock.J (m+1))) c:=by
        have hG:= he.mono fun N hn=> (hk.costs N m hn).2.2.1
        refine ⟨_,crest hk0 hG a hJ ?_⟩
        intro r t F W hr ht hw hy i
        let f:= A.S.side (m+1) i; let v:= (A.clock.op m i).ratio
        have hS:= promote_crew (c:=a i) (f:=f) (r:=v) (S:=fun n=>(B.towers n m).T) hC
        obtain ⟨M₀,H₀⟩:= hh m (a i); obtain ⟨M₁,H₁⟩:=hh (m+1) f
        have hu:=(copies_crew (S:=fun n=> (T.towers n m).mf) v ((((H₁.matrix_product (hU.muster f)).matrix_product hS).matrix_product (transposeM H₀)).congr' (he.mono fun N h=>(Q N h|>.generated i|>.mf).symm )))
        exact (perunik (hw.muster (a i)) (hu.comp hr.tendsto_atTop)).trans (perunik (hu.comp ht.tendsto_atTop) (hy.muster (a i)))
   obtain ⟨c'',F,hF⟩:= hj
   have he1:= he.mono fun N hn=>(hk.costs N m hn).1
   have he2 := he.mono fun N hn=>(hk.costs N m hn).2.1
   refine ⟨⟨_,hF.hull⟩,⟨_,(crest hk0 he1 a hJ ?_).choose_spec.hull⟩,⟨_,(crest hk0 he2 a hJ ?_).choose_spec.hull⟩⟩
   · intro r t F W hr ht hw hy i; obtain ⟨V,hV⟩:=hh m (a i)
     have hu:= (((tendsto_const_nhds (x:=(d 1 (a i)).transpose)).matrix_product (transposeM hV)).const_smul (Real.sqrt A.clock.kernel.penalty)⁻¹).congr' (f₂:=fun N=> (T.towers N m|>.mn.acts (a i))) (he.mono fun N h=>(Q N h|>.generated i|>.mn).symm)
     exact (tendsto_nhds_unique (hw.muster (a i)) (hu.comp hr.tendsto_atTop)).trans (tendsto_nhds_unique (hu.comp ht.tendsto_atTop) (hy.muster (a i)))
   intro r t F W hr ht hw hy i; let c:= a i; obtain ⟨V,hV⟩:=hh m c
   let U := Matrix (Co c Layers2) (Co c Layers2) ℝ; let U' := Matrix (Co c (TypeFace 3)) (Co c Layers2) ℝ
   have H: Continuous (fun x:U×U'=> stack x.1 x.2):=by
       refine continuous_pi fun ⟨i,x⟩ => continuous_pi fun j=>?_
       cases x <;> rename_i k
       · change Continuous fun (x:U×U')=> x.1 (i,k) j; exact (continuous_apply_apply _ _).comp continuous_fst
       change Continuous fun (x:U×U')=> x.2 (i,k) j; exact (continuous_apply_apply _ _).comp continuous_snd
   have hZ:= hR.muster c; have h1:=(tendsto_const_nhds (x:=(1:U))).sub ((hV.matrix_product (hV'.muster c)).matrix_product (transposeM hV)); have h2:= ((hZ.matrix_product (tendsto_const_nhds (x:= d 2 c))).matrix_product (hV'.muster c)).matrix_product (transposeM hV)
   have hu:= (H.continuousAt.tendsto.comp (h1.prodMk_nhds h2)).congr' (f₂:=fun N=> (T.towers N m|>.o.acts c)) (he.mono fun N h=>(Q N h|>.generated i|>.image).symm)
   exact (tendsto_nhds_unique (hw.muster (a i)) (hu.comp hr.tendsto_atTop)).trans (tendsto_nhds_unique (hu.comp ht.tendsto_atTop) (hy.muster (a i)))
lemma relayT {P:Supply.Sheet G}: ∃ K:MapPrices,∀ A: Levels G,A.clock.stage=P.profile→ A.clock.kernel=P.kernel →
     ∀ B:Horizon A, Exhibits A X B l → (∀ i,0≤l i)→∃ T:Horizon A,Bid.Retained T B∧ T.Suffices K ∧ Amplify T :=by
   obtain ⟨K,hK⟩:=Bid.pinsT l Work.F07.answer Work.F08.answer Work.F09.answer P X
   refine ⟨K,fun A h ht B hX hL=>?_⟩
   obtain ⟨T,hT,hM,y,V,z,hy,hz,H⟩:= hK A h ht B hX
   have hg:= stellar hX hL
   choose! D I using H
   have hm m:=deliver hX hL hg hT hM m _ _ _ (hy _) (hz _) (fun N=> D N m) (fun N h=> I _ _ h)
   refine ⟨T,hT,hM,?_,fun i=> (hm i).1, fun i=> (hm i).2.1, fun i=> (hm i).2.2.1, fun i=> (hm i).2.2.2.1, fun i=> (hm i).2.2.2.2⟩
   constructor <;> intro i <;> rw [hT.1]
   · exact hg.diagonal i
   · exact hg.dual i
   · exact hg.roots i
   · exact hg.metric i
   exact hg.inverse i
end YM.Next.Free
#print axioms YM.Next.Free.relayT
