import YM.RG08.Slate.Force

/-! # Coarse-node symmetry and its legal all-period transformation. Perturbed about
 the chart origin, no data loan from the actual Ward charge mechanism. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix MeasureTheory Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)

abbrev node (w:Site c→G.El):= w ∘ S.ratio.parent

def tumble (w:Site c→G.El) : House F (G:=G) F where
 arrow u p:=node S w p.val.1 * u p *(node S w (p.val.1+step p.val.2))⁻¹
 sound h j H:=by
    funext p;apply mul_left_cancel (a:=node S w p.val.1); apply mul_right_cancel (b:=(node S w (p.val.1+step p.val.2))⁻¹); exact congrFun H p
 cost:= measurePreserving_pi _ _ (fun p:F.Free=> (G.preserve_two_sided (node S w p.val.1) (node S w (p.val.1+step p.val.2))⁻¹))

lemma drowse (w:Site c→G.El)(u:F.Slice G):F.drape ((tumble S F w).arrow u)= Lattice.gauge (node S w) (F.drape u):=by
 funext i; by_cases he:i∈F.trunks
 · have ht : node S w (i.1+step i.2)=node S w i.1 := congr_arg w (F.trunk_internal he)
   unfold Lattice.gauge;rw [show F.drape _ i=1 from F.on_tree _ ⟨i,he⟩,show F.drape u i=1 from F.on_tree _ ⟨i,he⟩,ht,mul_one,mul_inv_cancel]
 unfold Lattice.gauge; rw [show F.drape _ i=_ from F.off_tree _ ⟨i,he⟩,show F.drape u i=_ from F.off_tree u ⟨i,he⟩];rfl

variable {X : Type}[Fintype X] (v : Lines G c 1→X)
structure Vector where
 act : Cellar X→Site c→G.El
 zero : ∀ i j, act 0 i=act 0 j
 fast : ∀ i, ContinuousAt (fun t=>act t i) 0
 ticket : ∀ i, Pace (fun t=>G.mat (act t i))
 roll : ∀ i,Pace (fun t=>G.mat (act t i)⁻¹)
variable (K:Vector (c:=c) (X:=X) (G:=G))

def siteBox (x:Cellar X)(u:G.Color)(i j:Site c):G.El:=K.act x i * G.lieExp u*(K.act x j)⁻¹
def tub (p : Cellar X)(y:G.Color)(i j:Site c): G.Color:= G.plog (G.mat (siteBox K p y i j))
lemma nigh (i j:Site c):siteBox K 0 0 i j=1:=by unfold siteBox; rw [G.mat_lieExp_zero,mul_one, K.zero i j,mul_inv_cancel]
lemma tub_nigh (i j:Site c):tub K 0 0 i j=0:=by unfold tub;rw [nigh,G.mat_one,G.plog_one]
lemma tub_pace (i j:Site c): Pace (fun z:Cellar X×G.Color=>tub K z.1 z.2 i j):=by
 let V(z:Cellar X×G.Color):=G.mat (siteBox K z.1 z.2 i j)
 have ht:V 0=1:=by unfold V;rw [Prod.fst_zero,Prod.snd_zero,nigh,G.mat_one]
 refine ContDiffAt.comp (f:=V) (g:=G.plog) _ (ht.symm ▸ G.plog_diff) ?_
 unfold V siteBox
 simp only [Gauge.mat_mul]
 exact (show ContDiffAt ℝ ω (fun z:Cellar X × G.Color=> G.mat (K.act z.1 i)*G.mat (G.lieExp z.2)) 0 from (ContDiffAt.comp (0:Cellar X × G.Color) (f:=Prod.fst) (g:=fun x=>G.mat (K.act x i)) (K.ticket i) contDiffAt_fst).mul (G.exp_jet.comp contDiff_snd).contDiffAt).mul (ContDiffAt.comp (0:Cellar X × G.Color) (f:=Prod.fst) (g:=fun x=>G.mat (K.act x j)⁻¹) (K.roll j) contDiffAt_fst)
lemma tub_view (i j:Site c):∀ᶠ z :Cellar X×G.Color in 𝓝 0,G.lieExp (tub K z.1 z.2 i j)=siteBox K z.1 z.2 i j:=by
 refine (show Tendsto (fun z:Cellar X×G.Color=>siteBox K z.1 z.2 i j) _ (𝓝 1) from ?_).eventually G.plog_right
 rw [← nigh K i j]; have h(l:Site c) : ContinuousAt (fun z:Cellar X×G.Color => K.act z.1 l) 0:= ContinuousAt.comp (g:=fun x=>K.act x l) (f:=Prod.fst) (K.fast l) continuousAt_fst
 exact (((h i).mul (G.lieExp_cont.comp continuous_snd).continuousAt).mul (h j).inv).tendsto

def back (i:TypeFace 1): Axis:=axisEquiv.symm i
@[simp] lemma back_axis(i:Axis):back (coord i)=i:=axisEquiv.symm_apply_apply i

def pigment (q:Site c)(a:TypeFace 1):Cellar X→L[ℝ]G.Color:= (heavy G).toContinuousLinearMap.comp (ContinuousLinearMap.pi (fun j=>ContinuousLinearMap.proj (v (q,a,j))))

def arch (x:Cellar X): Cellar (Lines G c 1):=fun i=>tub K x (pigment v i.1 i.2.1 x) i.1 (i.1+step (back i.2.1)) i.2.2
def wheel (x:Cellar X)(z:AxisChart G F): AxisChart G F:=fun i=> tub K x (z i) (S.ratio.parent i.val.1) (S.ratio.parent (i.val.1+step i.val.2))

lemma colorLens (i:G.ColorIndex):ContDiff ℝ ω (fun y:G.Color=>y i):=by
 exact (contDiff_apply ℝ ℝ i).comp (heavy G).symm.contDiff
lemma zoom: Pace (arch v K):=by
 apply contDiffAt_pi.mpr; intro i; let Q(x:Cellar X):=(x,pigment v i.1 i.2.1 x)
 have he:Q 0=0:=by unfold Q;rw [map_zero];rfl
 exact (colorLens i.2.2).contDiffAt.comp _ (ContDiffAt.comp 0 (f:=Q) (g:=fun z=>tub K z.1 z.2 i.1 (i.1+step (back i.2.1))) (he.symm ▸ tub_pace K i.1 _) (contDiffAt_id.prodMk (pigment v _ _).contDiff.contDiffAt))
lemma grip:Pace (uncurry (wheel S F K)):=by
 apply contDiffAt_pi.mpr;intro i
 let Q(x:Cellar X×AxisChart G F):=(x.1,x.2 i)
 have h:Pace Q:=contDiffAt_fst.prodMk ((contDiff_apply ℝ G.Color i).contDiffAt.comp (f:=@Prod.snd (Cellar X) (AxisChart G F)) 0 contDiffAt_snd)
 exact (tub_pace K _ _).comp (f:=Q) (0:_) h

 -- status unfolded coord legs
omit [Fintype X] in
lemma beaker [Fintype X] (i:Stationary.Lines G c 1) (x:Cellar X): (Slate.borne v x (i.1,i.2.1)) i.2.2=(pigment v i.1 i.2.1 x) i.2.2:=rfl
lemma archings (q:Site c)(j:Axis)(x:Cellar X)(i:G.ColorIndex): borne id (arch v K x) (q,coord j) i=tub K x (pigment v q (coord j) x) q (q+step j) i:=by
 change arch v K x (q,coord j,i)=_
 unfold arch;rw [back_axis]
lemma enfold:
 ∀ᶠ x:Cellar X in 𝓝 0, represent (Slate.borne id (arch v K x))=Lattice.gauge (K.act x) (represent (Slate.borne v x)):=by
 have he (i:Lattice.Edge (Site c)):∀ᶠ x:Cellar X in 𝓝 0,G.lieExp (tub K x (pigment v i.1 (coord i.2) x) i.1 (i.1+step i.2))=siteBox K x (pigment v i.1 (coord i.2) x) i.1 (i.1+step i.2):=by
    refine (show Tendsto (fun x:Cellar X=>(x,pigment v i.1 (coord i.2) x)) _ (𝓝 0) from ?_).eventually (tub_view K _ _)
    simpa only [map_zero,id_eq,Prod.zero_eq_mk] using! (continuous_id.prodMk (pigment v i.1 (coord i.2)).continuous).tendsto 0
 filter_upwards [eventually_all.mpr he] with x hx;funext e; simp only [Lattice.gauge,Work.F03.represent_link]; specialize hx e
 rw [show borne id (arch v K x) (e.1,coord e.2)=tub K x (pigment v e.1 (coord e.2) x) e.1 (e.1+step e.2) from ?_]
 · rw [hx]; unfold siteBox; congr 3
 ext i;exact archings v K _ _ _ i

lemma spent:
 ∀ᶠ z:Cellar X × AxisChart G F in 𝓝 0, exposure F 0 (wheel S F K z.1 z.2)=(tumble S F (K.act z.1)).arrow (exposure F 0 z.2):=by
 let a (i:F.Free):=tub_view K (S.ratio.parent i.val.1) (S.ratio.parent (i.val.1+step i.val.2))
 have he (i:F.Free):∀ᶠ z:Cellar X × AxisChart G F in 𝓝 0,G.lieExp (wheel S F K z.1 z.2 i)=siteBox K z.1 (z.2 i) (S.ratio.parent i.val.1) (S.ratio.parent (i.val.1+step i.val.2)):=by
    refine (show Tendsto (fun x:Cellar X × AxisChart G F=>(x.1,x.2 i)) (𝓝 0) (𝓝 0) from (continuous_fst.prodMk ((continuous_apply _).comp continuous_snd)).tendsto (0:_)).eventually (a i)
 filter_upwards [eventually_all.mpr he] with z hz; funext p
 simp only [Work.F05.exposure,Precision.link_one,Precision.replica_one,tumble,Pi.one_apply,mul_one]
 exact hz p

def route : Solved S F v id (arch v K) (wheel S F K) 1 0 where
 rates:=fun x=>tumble S F (K.act x)
 grip:=grip S F K
 run0:=funext fun i=>tub_nigh ..
 zoom:=zoom v K
 fit0:=funext fun i=>by unfold arch;rw [map_zero,tub_nigh];rfl
 paid':=spent S F K
 field:=by
    filter_upwards [(continuous_fst.tendsto (0:Cellar X ×AxisChart G F)).eventually (enfold v K)] with z hz
    refine ⟨node S (K.act z.1),?_,?_⟩
    · rw [← S.ratio.root_embed, map_zero,pull_id,drowse]
    rw [pull_id,show node S (K.act z.1) ∘ S.ratio.embed= K.act z.1 from by funext p; exact congrArg _ (S.ratio.embed_parent _)]
    exact hz
end YM.RG08.Quarry
