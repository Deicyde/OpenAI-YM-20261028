import YM.TraceExtension.Perfect.Plants
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}
def mist (o:Site f)(b:Axis): Gal G f:=fun U=> edgeColor.symm fun x=> if x.1=o then tulip o b x.2 U else 0
def petalPush (o:Site f)(b:Axis)(u:Link G f): Link G f:= edgeColor.symm fun x=>if x.1=o then petal o b x.2 u else 0
lemma mist_analytic (o:Site f)(b:Axis): Cloaked (mist (G:=G) o b):=by
 let U x:=fun e:Edge (Site f)=>if e.1=o then tulip o b e.2 (input G f x) else 0
 refine ⟨(edgeColor (G:=G) (n:=f)).symm.contDiff.contDiffAt.comp _ (show ContDiffAt ℝ ω U 0 from contDiffAt_pi.mpr fun i=>?_),fun T _ _ _ _ V k w _ _ _ _=>Eventually.of_forall fun x=>?_⟩
 · unfold U; split; exact tulip_cont ..;exact contDiffAt_const
 unfold mist; apply edgeColor.injective; funext i; rw [armor_at]; simp only[ContinuousLinearEquiv.apply_symm_apply]; rw[tulip_gauge];split_ifs with H; rw[H]; rw [map_zero]
lemma mist_zero (o:Site f)(b:Axis): mist (G:=G) o b 1=0:=by
 unfold mist; rw[show (fun i:Edge (Site f)=> if i.1=o then tulip o b i.2 (1:Config G f) else 0)=0 from funext fun x=>by rw[tulip_zero]; simp,map_zero]
lemma mist_home (o: Site f)(b:Axis): mist (G:=G) o b∈rains G f:=⟨mist_analytic ..,mist_zero ..⟩
lemma mist_slope (o:Site f)(b:Axis)(u:Link G f): fderiv ℝ (mist o b∘ input G f) 0 u= petalPush o b u:=by
 let X:= mist (G:=G) o b ∘ input G f; have hh:= (mist_analytic (G:=G) o b).dye
 apply edgeColor.injective; funext i; unfold petalPush; rw [ContinuousLinearEquiv.apply_symm_apply]; let p: Link G f→L[ℝ] G.Color:= ContinuousLinearMap.proj (φ:=fun _:Edge (Site f)=>G.Color) i ∘L edgeColor.toContinuousLinearMap
 change p (fderiv ℝ X 0 u)=_; rw [← show fderiv ℝ (p ∘ X) 0 u=p (fderiv ℝ X 0 u) from DFunLike.congr_fun ((p.hasFDerivAt.comp _ (hh.differentiableAt (by simp)).hasFDerivAt).fderiv) u]
 split_ifs with hi
 · rw[show p ∘ X=tulip _ _ _ ∘ input G f from ?_,petal_plan]; funext x; unfold Function.comp X; simp [p,mist,hi]
 rw [show p ∘ X=(fun _=> 0) from funext fun x=>by unfold Function.comp X; simp[p,mist,hi]]; simp

def born (x:Site f)(a b:Axis): Peat G f:= (if a=b then (1/4:ℝ) • (∑ i:Axis,∑ j:Axis,bornPair x i i j) else 0) - ∑ i : Axis,bornPair x a b i
lemma born_home (x:Site f)(a b:Axis): born (G:=G) x a b∈loom G f:=by
 apply (loom _ _).sub_mem _ ((loom _ _).sum_mem fun i _=>(born_win ..).1); split_ifs; exact (loom _ _).smul_mem _ ((loom _ _).sum_mem fun i _=>(loom _ _).sum_mem fun j _=>(born_win ..).1); exact (loom _ _).zero_mem
lemma born_trace (x:Site f): ∑ a:Axis,born (G:=G) x a a=0:=by
 unfold born; rw [Finset.sum_sub_distrib]; simp only[↓reduceIte,Finset.sum_const,card_univ]
 let W:Peat G f:= ∑ i:Axis,∑ j:Axis,bornPair x i i j
 change (4:ℕ) • ((1/4:ℝ) • W)-W=0; rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num
lemma born_symm (x:Site f)(a b:Axis) : born (G:=G) x a b=born x b a :=by
 by_cases he:a=b; subst b; rfl
 unfold born;rw [if_neg he,if_neg (Ne.symm he)]; congr 1; refine sum_congr rfl fun i _=>?_ ; funext p; exact real_inner_comm ..

variable {p:Clip}{M:PathData G}{W:Bed}{α v σ C Λ:ℝ} (h:M.Bounds p σ C Λ)(hp:Floor W p f α v)(hx:Attached W M)(hg:Bid.Sworn W f G)
local notation "Y"=> Stationary.intended (m:=f) p M
include h hp hx hg
lemma mintW : Y 0=0∧ fderiv ℝ (Y) 0=0 ∧ ∀ x y:Link G f, iteratedFDeriv ℝ 2 (Y) 0 ![x,y]=Bid.gaugeFiscal W (arm G f 1 x) (arm G f 1 y):=by
 have hh : Army (input G f) 0 := Army.powL contDiffAt_id
 apply Work.F03.hessian_of_limit (Q:=fun x y=> Bid.gaugeFiscal W (arm G f 1 x) (arm G f 1 y)) (((Work.F02.answer _ _ _ _ _ _ h).crown (0:Link G f) _ _ (input_zero ..) hh).of_le le_top) (fun x=> ?_) (fun x y z=> ?_) (fun x y=> ?_)
 · unfold input; simp_rw [map_smul]; exact Work.F03.main_limit h hx hp hg _
 · rw [map_add,Work.F03.gaugeFiscal_add]
 rw [Work.F03.metric_pair W h hx _ _ hp,Work.F03.metric_pair W h hx _ _ hp]; exact sum_congr rfl fun i _=> by rw [real_inner_comm (Work.F03.faceCurl ..), real_inner_comm (Work.F03.ellLine ..)]
-- Hessian E
lemma aroma_gone (x:Site f)(b:Axis):
   let Q:= aroma p M (mist x b)
   Q∈loom G f∧∀ u v, iteratedFDeriv ℝ 2 (Q∘input G f) 0 ![u,v]= Bid.gaugeFiscal W (arm G f 1 u) (arm G f 1 (petalPush x b v))+Bid.gaugeFiscal W (arm G f 1 v) (arm G f 1 (petalPush x b u)):=by
 intro Q; obtain ⟨ha,hM,H⟩:= mintW h hp hx hg
 let D:= mist (G:=G) x b ∘ input G f
 let X (y: Link G f):=fderiv ℝ (cartMove y) 0
 have ho : cartMove (G:=G) (c:=f) 0=ᶠ[𝓝 0] id:= by filter_upwards [input_encodes (G:=G) (m:=f)] with i hh; rw [cartMove,input_zero,mul_one,hh];rfl
 have ht(v:Link G f) : X 0 v=v:=by unfold X; rw [ho.fderiv_eq (𝕜:=ℝ), fderiv_id];rfl
 have hA : ContDiffAt ℝ ω X 0:= (Work.F05.curve_partial cartDiff).comp (f:=fun y:Link G f=>(y,0)) _ (by fun_prop)
 let L:=fun i=>X i (D i); have hD0:D 0=0:=by simp [D,mist_zero]
 have hL:L 0=0:=by simp[L,hD0]
 have hDX : ContDiffAt ℝ ω D 0:= (mist_analytic (G:=G) x b).dye
 have hL' v:fderiv ℝ L 0 v=petalPush x b v:=by
    have hw:= (hA.differentiableAt (by simp)).hasFDerivAt.clm_apply ((hDX.differentiableAt (by simp)).hasFDerivAt); rw [hw.fderiv];
    change X 0 (fderiv ℝ D 0 v)+ (fderiv ℝ X 0 v) (D 0)=_
    rw [hD0,map_zero,add_zero,ht]; exact mist_slope ..
 let T i:= fderiv ℝ (Y) i
 let F i:= T i (L i)
 have hT:ContDiffAt ℝ ω (Y) 0:= (Work.F02.answer _ _ _ _ _ _ h).crown (0:Link G f) _ _ (input_zero ..) (Army.powL contDiffAt_id)
 have he: Q ∘ input G f =ᶠ[𝓝 0] F:=by filter_upwards [slope_links (c:=f) (G:=G) hT] with a hh; exact DFunLike.congr_fun hh.1.symm (D a)
 have hY(u v): fderiv ℝ T 0 u v=Bid.gaugeFiscal W (arm G f 1 u) (arm G f 1 v):=by
    have ht:= H v u; rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_one_apply] at ht;
    have hx:= H u v; rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_one_apply] at hx; exact hx
 obtain ⟨hw,hh,hp⟩:= criss (ContinuousLinearMap.id ..) T L (hT.fderiv_right (by simp)) (hA.clm_apply hDX) hM hL
 change fderiv ℝ F 0=0 at hh
 refine ⟨⟨aroma_diff h (mist_analytic x b), (braided he).trans (fun i hi=>?_)⟩,fun u v=> ?_⟩
 · interval_cases i <;> ext1 x
   · simp only[iteratedFDeriv_zero_apply]; exact hw
   simp [iteratedFDeriv_one_apply,hh]
 rw [(he.iteratedFDeriv ℝ 2).eq_of_nhds]
 have hz:= hp u v; simp only [ContinuousLinearMap.id_apply,hY,hL'] at hz; exact hz
end YM.Trace.Perfect
#print axioms YM.Trace.Perfect.aroma_gone
