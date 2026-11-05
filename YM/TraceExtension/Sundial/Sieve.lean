import YM.TraceExtension.Pith.Orders

/-! Walk within even homogeneous freedom at degree four. Two real scale
 sectors separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)

-- real frame endomorphism average
set_option quotPrecheck false
local notation "Act"=> (Bel C.book).Field 4
abbrev core:= circle (compass (H:=H) h) (LinearEquiv.refl ℂ Act)
lemma core_act(v:Ortho)(x:Act): core H h v x=(turns C).act 4 v x:= rfl
-- P_l*P_r. invariant and adjoint phases
abbrev spur : Mat Act:= meanO (core H h) 1
abbrev spool : Mat Act:= meanO 1 (core H h)
abbrev spindle: Mat Act:= spur H h*spool H h
lemma paddleO(x:Act)(v:Ortho): (turns C).act 4 v (spindle H h x)=spindle H h x ∧ spindle H h ((turns C).act 4 v x)=spindle H h x:=by
    rw [← core_act H h,← core_act H h]; let f:= core H h; let F' : Ortho→* (Mat Act):=1; have hx:Continuous f:= circle_cont _ _; have hz:Continuous F':= continuous_const; have ht:F' v=1:=rfl
    have hp: f v*spur H h=spur H h:= ((underO f F' hx hz v).trans (by rw[ht,mul_one])); have he: spool H h*f v=spool H h:= ((underO F' f hz hx v).symm.trans (by rw[ht,one_mul]));
    have ha:f v*spindle H h=spindle H h:=by unfold spindle; rw [← mul_assoc,hp]
    have hb:spindle H h*f v=spindle H h:=by unfold spindle;rw[mul_assoc,he]
    exact ⟨congr_arg (fun g:Mat Act=>g x) ha, congr_arg (fun g:Mat Act=>g x) hb⟩
lemma realcat(x:Act): spindle H h ((F₀).conj H.spin 4 x)=(F₀).conj H.spin 4 (spindle H h x):=by
    let f:=core H h; have ht:Continuous f:=circle_cont ..; let F': Ortho→*(Mat Act):=1; have hz:Continuous F':=continuous_const; let P:=LinearMap.toContinuousLinearMap (StressFlux.conjQ (d:=4) H.spin)
    have hh(v x): f v (P x)=P (f v x):=((baseRights (C:=C) (H:=H) h).real ..).symm
    change spur H h (spool H h (P x))=P (spur H h (spool H h x)); rw[show ∀ x,spool H h (P x)=P (spool H h x) from mean_maps F' f hz ht P (fun v x=>rfl) hh]; exact mean_maps f F' ht hz P hh (fun v x=>rfl) _
lemma pancake(x:Act): expectation (F₀) 4 (spindle H h x)=expectation (F₀) 4 x:=by
    let f:=core H h; have ht:Continuous f:=circle_cont ..; let F': Ortho→*(Mat Act):=1; have hz:Continuous F':=continuous_const; let q:= LinearMap.toContinuousLinearMap (expectation (F₀) 4)
    have hh(v x): q (f v x)=q x:= expect_turn H _ (Maxwell.Free.gear_motion _) x v
    exact (Peg f F' ht hz q hh (fun v x=>rfl) _).trans (Peg F' f hz ht q (fun v x=>rfl) hh _)
lemma rise(x:Act)(ht:∀ v,(turns C).act _ v x=x): spindle H h x=x:=by
    let f:=core H h; have hh: Continuous f:=circle_cont ..; let F': Ortho→*(Mat Act):=1; have hz:Continuous F':=continuous_const; have he(v):f v x=x:= ht v
    change spur H h (spool H h x)=x; rw [show spool H h x=x from mean_fixed F' f hz hh x (fun v=>rfl) he]; exact mean_fixed f F' hh hz _ he (fun v=>rfl)
lemma plinth (x:Act): spindle H h (spindle H h x)= spindle H h x:= rise H h _ (fun v=> (paddleO H h x v).1)
include hp in
lemma riseS : spindle H h (stepField C)= stepField C:=by obtain ⟨j,v,hV⟩:= skyline F h hp; exact rise H h (stepField C) (legitimacy F h hV).2
lemma mortised (x y:Axis)(ht:x≠y): spindle H h (standard4 C x y)=0:=by
    obtain ⟨T,hT,hK,hJ,hκ,hR⟩:= stages (C:=C) h
    rw[hK,hJ] at hR
    let v:= (Signed.mirror x).ortho; let X:= standard4 C; let s:= spindle H h
    have hV(i): v.val i x= if i=x then -1 else 0:=by simp [v,Signed.ortho, Signed.mirror,Signed.matrix_at,eq_comm]
    have hW(i): v.val i y= if i=y then 1 else 0:=by simp [v,Signed.ortho, Signed.mirror,Signed.matrix_at,ht,eq_comm]
    have hy: (turns C).act 4 v (X x y)= -X x y:=by
        unfold X; rw [hR]; simp_rw[hV,hW]; simp [ite_smul, apply_ite]
    have hh : s (X x y)= -s (X x y):=by conv_lhs => rw [← (show s ((turns C).act 4 v (X x y))=s (X x y) from (paddleO H h (X x y) v).2), hy,map_neg]
    have hg:(2:ℝ) • s (X x y)=0:=by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp hh
    exact (smul_eq_zero.mp hg).resolve_left (by norm_num)
lemma null_stress (a b:Axis): spindle H h (standard4 C a b)=0:=by
    obtain ⟨T,hT,hK,hJ,hκ,hR⟩:= stages (C:=C) h; rw[hK,hJ] at hR
    let f:=spindle H h; let Y(a b):= f (standard4 C a b)
    have ht : Tensorial (turns C) Y:=by
       intro K a b; unfold Y; rw [(paddleO H h _ K).1,← (paddleO H h _ K).2,hR K a b]; simp only [map_sum,map_smul];rfl
    have he(i): Y i i=Y a a:= flat_diag Y ht (mortised H h) ..
    have hp : (4:ℝ) • Y a a=0:=by
       rw [show (4:ℝ) • Y a a=∑ i:Axis,Y i i by simp_rw [he]; rw[Fin.sum_univ_four];module];unfold Y; rw [← map_sum, trace_none C, map_zero]
    by_cases hv:a=b; subst b
    exacts [(smul_eq_zero.mp hp).resolve_left (by norm_num), mortised H h a b hv]
include h in
lemma patch_s(a b:Axis): centering (F₀) 4 (standard4 C a b)=standard4 C a b:=by
    obtain ⟨T,hT,hκ,hV⟩:= Litpay (C:=C) h; exact zero_center (⟨standard4 C a b,(kernel_mem.mp ((show T.T.J=standard4 C from hT) ▸ hV.currents.1)).2 a b⟩:Active (F₀))
end YM.Trace.Sundial
