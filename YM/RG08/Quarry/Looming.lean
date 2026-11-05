import YM.RG08.Quarry.Ephemeral

/-! # Gauge's handshake on every slot, full FPS, also rank-one directions. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Isles Laurent Pert.Bulk
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G : Gauge}

def fbar (k:Fin 3): Cellar (foil G)→L[ℝ] G.Color:= (heavy G).toContinuousLinearMap.comp (ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (k,i)))
def menu (i:Loc G 1)(p:foil G):Market (cuff G):= if p.1=0 then (0,.inl (i.1,p.2)) else (if p.1=1 then (0:Cover) else step (back i.1),.inr p.2)

def jaw : Cellar (foil G) → Trip G:=fun x=>(fbar 0 x,fbar 1 x,fbar 2 x)
lemma jaw_pace:Pace (jaw (G:=G)):=(fbar 0).contDiff.contDiffAt.prodMk ((fbar 1).contDiff.contDiffAt.prodMk (fbar 2).contDiff.contDiffAt)
@[simp] lemma jaw_home:jaw (G:=G) 0=0:=by unfold jaw;rw [map_zero,map_zero,map_zero];rfl

def glaze (d:G.El)(i:G.ColorIndex)(z:Trip G):=flourish d z.1 z.2.1 z.2.2 i
lemma glaze_pace (d:G.El)(i:G.ColorIndex): Pace (glaze d i):= (colorLens i).contDiffAt.comp (f:=fun z:Trip G=>flourish d z.1 z.2.1 z.2.2) 0 (tall d)
lemma glaze0(d:G.El)(i:G.ColorIndex):glaze d i 0=0:=by unfold glaze flourish; simp only [gaugeIn,Prod.snd_zero,Prod.fst_zero,neg_zero,Gauge.mat_lieExp_zero,inv_one,mul_one,Gauge.mat_one,Gauge.plog_one,map_zero];rfl

def hot (d:G.El) : Loom (foil G) (cuff G) (Loc G 1) where
 offset:=menu
 fare i:= glaze d i.2 ∘ jaw
 fit i:= ContDiffAt.comp 0 (g:=glaze d i.2) (f:=jaw) (jaw_home.symm ▸ glaze_pace d _) jaw_pace
 origin _:=by rw [Function.comp_apply,jaw_home,glaze0]
lemma hot_speed (d:G.El)(i:Loc G 1)(x:Cellar (foil G)): fderiv ℝ ((hot d).fare i) 0 x=(G.adjoint d (fbar 0 x - fbar 1 x+fbar 2 x)) i.2:=by
 let p:= (hot d).fare i
 let L: G.Color→L[ℝ]ℝ:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:G.ColorIndex=>ℝ) i.2).comp (heavy G).symm.toContinuousLinearMap
 have hu (t:ℝ): HasFDerivAt (fun x: G.Color=>x i.2) L (flourish d (t • fbar 0 x) (t • fbar 1 x) (t • fbar 2 x)):= L.hasFDerivAt
 have he:= (hu 0).comp_hasDerivAt (f:=fun t:ℝ=>flourish d (t • fbar 0 x) (t • fbar 1 x) (t • fbar 2 x)) 0 (speed d _ _ _)
 have hx : (p ∘ fun t:ℝ=>t • x)=(fun x:G.Color=>x i.2) ∘ fun t:ℝ=>flourish d (t • fbar 0 x) (t • fbar 1 x) (t • fbar 2 x):=by funext t; unfold p hot; simp only [Function.comp_apply,glaze,jaw,map_smul]
 rw [←hx] at he
 have hz := ((hot d).fit i).differentiableAt (by simp)
 exact (hz.hasFDerivAt.comp_hasDerivAt_of_eq 0 (f:=fun t:ℝ=>t • x) (by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x) (zero_smul ℝ x).symm).unique he

def spear {c:Side}(q:Site c):Cellar (Cove c (cuff G))→L[ℝ] G.Color:= (heavy G).toContinuousLinearMap.comp (ContinuousLinearMap.pi fun i=>ContinuousLinearMap.proj (q,.inr i))
def badge (c:Side)(q:Lines G c 1):Cove c (cuff G):=(q.1,.inl q.2)

def raise (c:Side)(d:G.El): Vector (c:=c) (X:=Cove c (cuff G)) (G:=G) where
 act x p:=d*G.lieExp (-spear p x)
 zero _ _:=by rw [map_zero,map_zero]
 fast _:=continuousAt_const.mul (G.lieExp_cont.comp (spear _).continuous.neg).continuousAt
 ticket i:=by simp only [G.mat_mul]; exact contDiffAt_const.mul (G.exp_jet.comp ((spear i).contDiff.neg)).contDiffAt
 roll i:=by simp only [_root_.mul_inv_rev,G.mat_mul,Work.F03.exp_neg_color, inv_inv]; exact (G.exp_jet.comp (spear i).contDiff).contDiffAt.mul contDiffAt_const

variable {c:Side}
lemma predicted (d:G.El)(q:Lines G c 1):
 (fun x=>arch (badge c) (raise c d) x q)=ᶠ[𝓝 0] fun x=> (hot d).fare q.2 (x ∘ dodge (hot d) q):=by
 let f:=fun x:Cellar (Cove c (cuff G))=>x ∘ dodge (hot d) q
 let t:=jaw ∘ f
 have hh0:t 0=0:=jaw_home
 have hh1:ContinuousAt f 0:= continuousAt_pi.mpr (fun _=>(continuous_apply _).continuousAt)
 have H:Tendsto t (𝓝 0) (𝓝 0):=by change (jaw ∘ f) 0=0 at hh0; simpa only [hh0] using (show Pace jaw from jaw_pace (G:=G)).continuousAt.comp (f:=f) hh1 |>.tendsto -- t via change
 filter_upwards [H.eventually (colored d)] with x hx
 let w:=q.1+step (back q.2.1)
 have he:fbar (2:Fin 3) (f x)=spear w x:=by
    ext j; change (f x) (2,j)=x _
    unfold f Function.comp dodge hot menu w; dsimp only; simp
 have ha:fbar (0:Fin 3) (f x)=pigment (badge c) q.1 q.2.1 x:=by ext j; change (f x) (0,j)=x _; unfold f Function.comp badge dodge hot menu; dsimp only; simp
 have hQ:fbar (1:Fin 3) (f x)=spear q.1 x:=by ext j; change (f x) (1,j)=x _; unfold f Function.comp dodge hot menu; dsimp only; simp
 change tub (raise c d) x _ q.1 w q.2.2=glaze d q.2.2 (t x)
 have hT : siteBox (raise c d) x (pigment (badge c) q.1 q.2.1 x) q.1 w=gaugeIn d ((t x).1) ((t x).2.1) ((t x).2.2):=by
    unfold gaugeIn t Function.comp jaw
    dsimp only;rw [ha,hQ,he]; unfold siteBox raise; dsimp only; rw [_root_.mul_inv_rev, ← Work.F03.exp_neg_color, neg_neg]; group
 unfold tub; rw [hT,hx];rfl

lemma prophet {I:Type}[Fintype I](d:G.El)(q:Lines G c 1)(g:Cove c (cuff G)→I)(x:I→Dig):
 breath x (eye (fun t:Cellar I=> arch (badge c) (raise c d) (t ∘ g) q))=breath ((x ∘ g) ∘ dodge (hot d) q) (eye ((hot d).fare q.2)):=by
 have ht:=show Tendsto (fun x:Cellar I=>x ∘ g) (𝓝 0) (𝓝 0) from (continuous_pi (fun _=>continuous_apply _)).tendsto (0:Cellar I)
 rw [eye_same (show _=ᶠ[𝓝 0] fun x=> (hot d).fare _ ((x ∘ g) ∘ dodge (hot d) q) from ht.eventually (predicted d q))]
 apply eye_chart (g ∘ dodge (hot d) q) _ ((hot d).fit _) ((hot d).origin _)
end YM.RG08.Quarry
