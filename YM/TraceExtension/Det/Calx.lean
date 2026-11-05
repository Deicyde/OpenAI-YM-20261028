import YM.TraceExtension.Perfect.Wicker
import YM.Next.STATIONARY.Joint.OnShell

/-!
# Stationary Ward for inserts: no equations-of-motion dropped algebraically.
  Use here derivative notation X × Y real Frechet: interchange orders off shell.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Perfect Matrix Stationary Module
open scoped Topology ContDiff BigOperators
variable {X Y Z:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
    [NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z]
    {F:X→Y→Z}
lemma analytic_l (h:ContDiffAt ℝ ω (uncurry F) 0)(u:X) : ContDiffAt ℝ ω (fun z:X×Y=> fderiv ℝ (fun x=> F x z.2) z.1 u) 0:=by
    let R:= fun z:Y×X=> (z.2,z.1)
    have h': ContDiffAt ℝ ω (uncurry fun y x=>F x y) 0:= h.comp (f:=R) 0 (by unfold R; fun_prop)
    exact (Work.F05.curve_partial h'|>.comp (f:=fun z:X×Y=>(z.2,z.1)) 0 (by fun_prop)).clm_apply contDiffAt_const
lemma analytic_r (h:ContDiffAt ℝ ω (uncurry F) 0)(u:Y) : ContDiffAt ℝ ω (fun z:X×Y=> fderiv ℝ (F z.1) z.2 u) 0:= (Work.F05.curve_partial h).clm_apply contDiffAt_const
lemma keep_l (h:ContDiffAt ℝ ω (uncurry F) 0)(u:X) : ContDiffAt ℝ ω (fun z=> fderiv ℝ (fun x=> F x z) 0 u) 0:=
    (analytic_l h u).comp (f:=fun z:Y=>((0:X),z)) 0 (by fun_prop)
lemma d_l {x:X}{y:Y}(h:ContDiffAt ℝ ω (uncurry F) (x,y))(u:X) : fderiv ℝ (fun x=> F x y) x u=fderiv ℝ (uncurry F) (x,y) (u,0):=by
    let g(z:X):X×Y:=(z,y)
    have hG: HasFDerivAt g ((ContinuousLinearMap.id ℝ X).prod 0) x:= hasFDerivAt_id x|>.prodMk (hasFDerivAt_const ..)
    have hu := (show HasFDerivAt (uncurry F) (fderiv ℝ _ (x,y)) (g x) from (h.differentiableAt (by simp)).hasFDerivAt).comp x hG
    exact congr($(hu.fderiv) u)
lemma d_r {x:X}{y:Y}(h:ContDiffAt ℝ ω (uncurry F) (x,y))(u:Y) : fderiv ℝ (F x) y u=fderiv ℝ (uncurry F) (x,y) (0,u):=by
    let g(z:Y):X×Y:=(x,z)
    have hG: HasFDerivAt g ((0:Y→L[ℝ] X).prod (ContinuousLinearMap.id ℝ Y)) y:= (hasFDerivAt_const ..).prodMk (hasFDerivAt_id y)
    have hu := (show HasFDerivAt (uncurry F) (fderiv ℝ _ (x,y)) (g y) from (h.differentiableAt (by simp)).hasFDerivAt).comp y hG
    exact congr($(hu.fderiv) u)
lemma exchange_at {x:X}{y:Y}(h:ContDiffAt ℝ ω (uncurry F) (x,y))(u:X)(v:Y) :
    fderiv ℝ (fun z => fderiv ℝ (fun a=> F a z) x u) y v= fderiv ℝ (fun a=> fderiv ℝ (F a) y v) x u:=by
    let T:= fderiv ℝ (uncurry F)
    have he : ∀ᶠ z in 𝓝 y, fderiv ℝ (fun a=> F a z) x u=T (x,z) (u,0):=by
        filter_upwards [(show Tendsto (fun z=>(x,z)) (𝓝 y) (𝓝 (x,y)) from tendsto_const_nhds.prodMk_nhds tendsto_id).eventually (h.eventually (by simp))] with z hz; exact d_l hz _
    have hp : ∀ᶠ a in 𝓝 x, fderiv ℝ (F a) y v=T (a,y) (0,v):=by
        filter_upwards [(show Tendsto (fun a=>(a,y)) (𝓝 x) (𝓝 (x,y)) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (h.eventually (by simp))] with a ha; exact d_r ha _
    have ht(w:X×Y): ContDiffAt ℝ ω (fun z=> T z w) (x,y):= (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
    rw [(show (fun z => fderiv ℝ (fun a=> F a z) x u)=ᶠ[𝓝 y] _ from he).fderiv_eq,(show (fun a=> fderiv ℝ (F a) y v)=ᶠ[𝓝 x] _ from hp).fderiv_eq,d_r (F:=fun x y=>T (x,y) (u,0)) (ht _) v,d_l (F:=fun x y=>T (x,y) (0,v)) (ht _) u]
    change fderiv ℝ (fun z=> fderiv ℝ (uncurry F) z (u,0)) _ _= fderiv ℝ (fun z=> fderiv ℝ (uncurry F) z (0,v)) _ _
    rw [divided _ _ h,divided _ _ h,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; exact h.isSymmSndFDerivAt_of_omega _ _
lemma exchange (h:ContDiffAt ℝ ω (uncurry F) 0)(u:X)(v:Y): fderiv ℝ (fun z => fderiv ℝ (fun a=> F a z) 0 u) 0 v= fderiv ℝ (fun a=> fderiv ℝ (F a) 0 v) 0 u:= exchange_at h u v
lemma exchange_bend (h:ContDiffAt ℝ ω (uncurry F) 0)(u:X)(v w:Y) :
    iteratedFDeriv ℝ 2 (fun z=> fderiv ℝ (fun a=> F a z) 0 u) 0 ![v,w] = fderiv ℝ (fun a=> iteratedFDeriv ℝ 2 (F a) 0 ![v,w]) 0 u:=by
    rw [← divided v w (keep_l h u)]
    let V := fun x y=> fderiv ℝ (F x) y w
    have hp : (fun y=> fderiv ℝ (fun z => fderiv ℝ (fun a=> F a z) 0 u) y w)=ᶠ[𝓝 0] fun y=> fderiv ℝ (fun x=> V x y) 0 u:=by
       filter_upwards [(show Tendsto (fun z=>((0:X),z)) (𝓝 (0:Y)) (𝓝 0) from tendsto_const_nhds.prodMk_nhds tendsto_id).eventually (h.eventually (by simp))] with a ha; exact exchange_at ha u w
    rw [hp.fderiv_eq,exchange (F:=V) (analytic_r h w) u v]; congr 1
    refine EventuallyEq.fderiv_eq ?_
    filter_upwards [(show Tendsto (fun x:X=>(x,(0:Y))) (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (h.eventually (by simp))] with a ha
    exact divided v w (ha.comp (f:=fun z=>(a,z)) 0 (by fun_prop))

lemma f_clm {u:Y→Y}{L:Y→Y→L[ℝ]Z}(x y : Y)(hp: ContDiffAt ℝ ω u y)(h: ContDiffAt ℝ ω L y):
    fderiv ℝ (fun z=> (L z) (u z)) y x=L y (fderiv ℝ u y x)+fderiv ℝ L y x (u y):=by rw[fderiv_clm_apply (h.differentiableAt (by simp)) (hp.differentiableAt (by simp))];rfl
lemma clm_h {U:Y→Y}{B:Y→ℝ}(ht:ContDiffAt ℝ ω B 0)(h:ContDiffAt ℝ ω U 0)(h₀:U 0=0)(x y:Y):
    iteratedFDeriv ℝ 2 (fun z=> fderiv ℝ B z (U z)) 0 ![x,y]=
    iteratedFDeriv ℝ 2 B 0 ![x,fderiv ℝ U 0 y]+iteratedFDeriv ℝ 2 B 0 ![fderiv ℝ U 0 x,y]+fderiv ℝ B 0 (iteratedFDeriv ℝ 2 U 0 ![x,y]):=by
    let L:=fderiv ℝ B
    let K:= fun z=> fderiv ℝ L z y
    let P:= fun z=> fderiv ℝ U z y
    have hL: ContDiffAt ℝ ω L 0:= ht.fderiv_right (by simp)
    have hK: ContDiffAt ℝ ω K 0:= (hL.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
    have hP: ContDiffAt ℝ ω P 0:= (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
    have hp : (fun z=> fderiv ℝ (fun z=> fderiv ℝ B z (U z)) z y)=ᶠ[𝓝 0] fun z=> L z (P z)+K z (U z):=by filter_upwards [h.eventually (by simp),hL.eventually (by simp)] with z hz hv; exact f_clm _ _ hz hv
    rw[← divided x y (show ContDiffAt ℝ ω (fun z=>fderiv ℝ B z (U z)) 0 from hL.clm_apply h), hp.fderiv_eq,fderiv_fun_add ((hL.clm_apply hP).differentiableAt (by simp)) ((hK.clm_apply h).differentiableAt (by simp)), _root_.add_apply,f_clm _ _ hP hL, f_clm _ _ h hK,h₀,map_zero,add_zero,show fderiv ℝ P 0 x= _ from divided x y h, iteratedFDeriv_two_apply,iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    change L 0 (fderiv ℝ (fderiv ℝ U) 0 x y)+fderiv ℝ L 0 x (P 0)+fderiv ℝ L 0 y (fderiv ℝ U 0 x) = fderiv ℝ L 0 x (P 0)+fderiv ℝ L 0 (fderiv ℝ U 0 x) y+ L 0 _
    rw [show fderiv ℝ L 0 y (fderiv ℝ U 0 x)=_ from ht.isSymmSndFDerivAt_of_omega _ _]; unfold L; rw [add_assoc, add_comm (fderiv ℝ B 0 _)]; rfl
end YM.Trace.Det
