import YM.TraceExtension.Perfect.Shape

/-! # Post-L perturb budget final for interpolating first fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {W:Type*} {I:W→ Type}[∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]{D:∀ w,I w→ℕ}
   {G:Gauge}{f g:∀ w,Rays (I w)→G.El}{N:ℕ}

lemma Calm.group_mul (h:Calm D (fun w=> G.mat ∘ f w) N)(g': Calm D (fun w=>G.mat ∘ g w) N)(hf:∀ w,f w 0=1)(hg:∀ w,g w 0=1): Calm D (fun w x=> G.mat (f w x*g w x)) N:=by
     refine ((h.duo g').prop (fun v:G.Mat×G.Mat=> v.1*v.2) (a:=(1,1)) (by fun_prop) (fun i=>by simp [hf,hg])).near (fun w=> Eventually.of_forall fun x=>?_); simp
lemma Calm.group_inv (h:Calm D (fun w=> G.mat ∘ f w) N): Calm D (fun w x=> G.mat (f w x)⁻¹) N:= (h.maps (starL ℝ : G.Mat≃L[ℝ] G.Mat).toContinuousLinearMap).near (fun w=> Eventually.of_forall fun a=>by change star (G.mat (f w a))=_; exact (G.mat_inv _).symm)

namespace Lot
variable {P:Patch}{Y:KernelChoices}{p:Clip}{α B β v:ℝ} (L:W→ Lot G P Y p α B)
set_option quotPrecheck false
variable (K:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1))
    (o:∀ w,Site (L w).f)(hb:0<β)(hp: ∀ w,(K w).strip β (v/P.L.val))
local notation "K!"=>fun w=> installed (L w).s.ratio (K w)
local notation "F!"=>fun w=>fresh (L w).wood (L w).ρ (K! w) (o w)
local notation "Z"=>fun w=> outing (L w).wood (K! w) (o w) (G:=G)
include hb hp
lemma gown (x:∀ w,Site (L w).f): Calm (fromV L x) (fun w q=> G.mat (Z w q (x w))) N:=by
    refine (cut_station L K o hb hp x|>.group_mul (g:=fun w q=> salute (L w).wood (K! w) q (x w)) (f:=fun w v=> switchSite (uniformM (of (gaugePad (K! w) (o w) ((L w).s.ratio.count.val+1))) v) (x w)) (locate_station L K hb hp x) (fun _=> by simp) (fun _=> by simp [salute]))
lemma tailor_f (e:∀ w,Edge (Site (L w).f)): Calm (fromV L (fun w=>(e w).1)) (fun w x=> G.mat ((F! w x).1 (e w))) N:=by
    let U w:=encamp (L w).wood (L w).ρ
    let y(w):=(e w).1
    let Y(w):= y w+step (e w).2
    have hv:=gown L K o hb hp y (N:=N); have ht:=gown L K o hb hp Y (N:=N)
    have hx(w): separation (Y w) (y w) ≤ 1:=by unfold Y; rw [separation,add_comm (y w), add_sub_cancel_right]; exact pdist_step _
    have hp'(t:∀ w,Site (L w).f)(w): Z w 0 (t w)=1:= congr_fun (out_flag .. |>.2) _
    have hw:= moss L ht 1 hx
    apply ((hv.group_mul (g:=fun w x=> (U w x).1 (e w)) (f:=fun w x=> Z w x (y w)) (wine L e) (hp' y) (fun w=> by unfold U; rw [encamp_zero (L w).law];rfl)).group_mul (hw.group_inv (f:=fun w x=> Z w x (Y w))) (fun w=>by change _*_= (1:G.El);simp [hp' y,U,encamp_zero (L w).law]) (fun i=>by simp [hp' Y])).near
    intro w; refine Eventually.of_forall fun x=>?_ ; dsimp only; rw [fresco];rfl
lemma tailor_c (e:∀ w,Site (L w).c): Calm (fromV L (fun w=> (L w).s.ratio.embed (e w))) (fun w x=> G.mat ((F! w x).2 (e w))) N:=by
    apply ((gown L K o hb hp (fun w=> (L w).s.ratio.embed (e w))).group_inv (f:=fun w x=> Z w x ((L w).s.ratio.embed (e w)))).near
    intro w; refine Eventually.of_forall fun x=>?_ ; dsimp only;rw [fresco]; simp [wages,encamp,abode]
lemma tailor_content (a:∀ w,Body 1 (L w).f): Calm (fromV L (fun i=> (a i).1)) (fun w x=>edgeColor (content ((F! w x).1)) (edgeOf (a w))) N:=by
    have ht:= (tailor_f L K o hb hp (fun w=>edgeOf (a w)) (N:=N)).prop G.plog (a:=1) G.plog_diff (fun w=>by dsimp only; rw [fresh_zero (L w).law]; rfl)
    refine ht.near (fun w=> Eventually.of_forall fun x=>?_); rcases e:(a w) with ⟨v,i⟩
    apply Eq.symm; exact content_at ..
end Lot
end YM.Trace.Perfect
