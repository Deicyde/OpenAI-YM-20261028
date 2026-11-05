import YM.TraceExtension.Perfect.Tumul
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{p:Clip}{η A B σ:ℝ}{i j k:ℕ} {W:Type*}{n:W→Side}
lemma Calm.grove {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {I:W→Type}[∀ w,Fintype (I w)][∀ w,DecidableEq (I w)] (D:∀ w,I w→ℕ){X:Type*}(S:Finset X)(f:∀ w,X→Rays (I w)→E)(h:∀ x∈S, Calm D (fun w=> f w x) k): Calm D (fun w y=> ∑ i∈S,f w i y) k:=by
 induction S using Finset.induction with
 | empty=> simp only[Finset.sum_empty]; exact Calm.frozen D 0
 | insert x A hx ih=> simp only[Finset.sum_insert hx]; exact (h x (mem_insert_self ..)).over (ih (fun i hi=> h i (mem_insert_of_mem hi)))
variable (x:∀ w,Site (n w))
set_option quotPrecheck false
local notation "X!"=> fun w (i:Lines G (n w) 1)=> separation (x w) i.1
lemma mineral (e:∀ w,Edge (Site (n w)))(R:ℕ)(h:∀ w,separation (x w) (e w).1 ≤ R): Calm (X!) (fun w v=> edgeColor (G:=G) v (e w)) k:=by
 -- piP via WithLp
 let K:= X!
 have hp(i:G.ColorIndex): Calm K (fun w v=>edgeColor v (e w) i) k:=by
    apply (Calm.pick K (fun w=> ((e w).1,coord (e w).2,i)) R h).near; intro w; refine Eventually.of_forall fun z=>?_ ; exact rfl
 have hx:= Calm.piP (p:=fun w v=>fun i:G.ColorIndex=>edgeColor (G:=G) v (e w) i) hp
 exact hx.maps ((WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap)
lemma catexp (G:Gauge): ContDiffAt ℝ ω (fun x:G.Color=> G.mat (G.lieExp x)) 0:=by
 exact G.exp_jet.contDiffAt
lemma mineral_mat (e:∀ w,Edge (Site (n w)))(R:ℕ)(h:∀ w,separation (x w) (e w).1 ≤ R): Calm (X!) (fun w v=> G.mat (input G (n w) v (e w))) k:= (mineral (G:=G) (k:=k) x e R h|>.prop _ (catexp G) (fun _=>congr_fun edgeColor.map_zero _)).near (fun w=>Eventually.of_forall fun y=>by dsimp only [Function.comp_apply]; rw [input_color])
lemma path_edge (o:∀ w,Site (n w))(R:ℕ)(P:Walk)(h : ∀ w, separation (x w) (o w) ≤ R): Calm (X!) (fun w v=> G.mat (travel (input _ _ v) (o w) P)) k:=by
 induction P generalizing o R with
 | nil=> exact Calm.frozen _ (G.mat 1)
 | cons a l ih=>
    let e w:=a.used (o w); let u (w):=o w+a.vec; let g w v:=travel (input G (n w) v) (u w) l; let f w v:=a.read (input G (n w) v) (o w)
    have hu(a:Axis)(w): separation (x w) (o w+step a) ≤ R+1:=by refine (separation_triangle (x w) _ _).trans (Nat.add_le_add (h w) ?_); rw [separation_comm,separation, add_comm (o w),add_sub_cancel_right]; exact pdist_step a
    have hh(a:Axis)(w): separation (x w) (o w-step a) ≤ R+1:=by refine (separation_triangle _ _ _).trans (Nat.add_le_add (h w) ?_); rw [separation, sub_sub_cancel]; exact pdist_step a
    rcases a with ⟨a,b⟩
    have hp:Calm (X!) (fun w=>G.mat∘ f w) k:=by
        cases b
        · exact mineral_mat x _ R h
        exact (mineral_mat (G:=G) x (R+1) (fun w=>show separation (x w) (o w-step a) ≤ R+1 from hh a w) (e:=e)|>.group_inv (f:=fun w v=>input G _ v (e w)))
    refine hp.group_mul (f:=f) (g:=g) ?_ ?_ ?_
    · refine ih u (R+1) ?_; cases b; exact hu a; exact fun w=>by unfold u; rw [show (Step.mk a true).vec=-(step a:Site (n w)) from rfl,← sub_eq_add_neg];exact hh a w
    · intro w; unfold f Step.read;rw [input_zero];split <;> simp
    intro w; unfold g;rw[input_zero]; have hp:= Push.stroll_zero (G:=G) l (u w); rw [link_one] at hp; exact hp
lemma tulip_calm (a b:Axis) : Calm (X!) (fun w=>tulip (G:=G) (x w) a b∘ input G (n w)) k :=by
 have ht:= path_edge (G:=G) (k:=k) x x 0 (square a b) (fun i=>(separation_self _).le)
 let U: G.Mat→L[ℝ] G.Mat:= (1/2:ℝ) • ((ContinuousLinearMap.id ℝ G.Mat)-(starL ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap)
 refine (ht.maps (G.projectColor.toContinuousLinearMap ∘L U)).near (fun w=>Eventually.of_forall fun v=>?_)
 simp only [Function.comp_apply,tulip,Gauge.curvature,G.mat_inv]; rfl
-- local chart code
section
variable {f: Side}
def hitch (e:Edge (Site f)) : Link G f→L[ℝ] G.Color:= ContinuousLinearMap.proj e ∘L edgeColor.toContinuousLinearMap
def spout (u v:G.Color):= G.plog (G.mat (G.lieExp v * G.lieExp u))
lemma spout_cont (G:Gauge): ContDiffAt ℝ ω (uncurry (spout (G:=G))) 0:=by
 unfold uncurry spout; simp only[G.mat_mul]; apply G.plog_diff.comp_of_eq
 · exact ((catexp G).comp (f:=Prod.snd) (0:G.Color×G.Color) contDiffAt_snd).mul ((catexp G).comp (f:=Prod.fst) (0:G.Color×G.Color) contDiffAt_fst)
 · simp
 change G.mat (G.lieExp 0)*G.mat (G.lieExp 0)=1; rw [G.mat_lieExp_zero]; simp
lemma cart_spoke (v z:Link G f)(e:Edge (Site f)): edgeColor (cartMove v z) e= spout (edgeColor v e) (edgeColor z e):=by
 unfold cartMove spout; rw [show edgeColor (content _) e=_ from content_at (input G _ z*input _ _ v) e.1 e.2,Pi.mul_apply,input_color,input_color]
lemma cart_dial : ∀ᶠ v:Link G f in 𝓝 0,∀ e: Edge (Site f),∀ z:Link G f, edgeColor (fderiv ℝ (cartMove v) 0 z) e=fderiv ℝ (spout (edgeColor v e)) 0 (edgeColor z e):=by
 have hh : ∀ᶠ v:Link G f in 𝓝 0, ContDiffAt ℝ ω (cartMove v) 0:=by
    filter_upwards [(show Tendsto (fun v:Link G f=>(v,(0:Link G f))) (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually ((cartDiff (c:=f) (G:=G)).eventually (by simp))] with v hv; exact Work.F05.hold_jet hv
 refine eventually_all.mpr fun e=>?_; let q:= hitch (G:=G) e
 filter_upwards [hh,(show Tendsto (fun v: Link G f=>(q v,(0:G.Color))) (𝓝 0) (𝓝 0) from (show Tendsto q (𝓝 0) (𝓝 0) from (map_zero q) ▸ q.continuous.tendsto 0).prodMk_nhds tendsto_const_nhds).eventually ((spout_cont G).eventually (by simp))] with v hv hp z
 have hu:= Work.F05.hold_jet hp; change q (fderiv ℝ (cartMove v) 0 z)=fderiv ℝ (spout (q v)) 0 (q z)
 have hx: q ∘ cartMove v=spout (q v) ∘ q:= funext (fun z=> cart_spoke ..)
 have he:= congr_arg (fun f:Link G f→G.Color=>fderiv ℝ f 0) hx; rw [fderiv_comp 0 q.differentiableAt (hv.differentiableAt (by simp)), fderiv_comp 0 _ q.differentiableAt, q.fderiv,q.fderiv,map_zero] at he; exact DFunLike.congr_fun he z; rw [map_zero]; exact hu.differentiableAt (by simp)
end
end YM.Trace.Perfect
