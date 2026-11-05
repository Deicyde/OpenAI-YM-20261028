import YM.TraceExtension.Perfect.Graces

/-! # Bundle analytic mesh chart operations, finite permutations/windows, only post-L. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
namespace Lot
variable {P:Patch}{Y:KernelChoices}{p:Clip}{α D:ℝ} {W:Type*}(L:W→ Lot G P Y p α D)
  {N:ℕ} (i:∀ w,Edge (Site (L w).f))
set_option quotPrecheck false
-- anchor root to input for Calm (fine coordinate)
abbrev tab (a : Lot G P Y p α D):= Lines G a.c 1
def fromV (y:∀ w,Site (L w).f): (w:W)→ (L w).tab→ℕ:= fun w i=> separation (y w) ((L w).s.ratio.embed i.1)
variable {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T]
local notation "Lx"=> fun w=>(L w).tab
lemma moss {x y:∀ w,Site (L w).f}{Z:∀ w,Link G (L w).c→ T}(hp:Calm (fromV L x) Z N) (d:ℕ)(hx:∀ w,separation (x w) (y w)≤d): Calm (fromV L y) Z N:=by
 apply hp.heater d; intro w i; unfold fromV; apply (separation_triangle _ (x w) _).trans; rw [separation_comm (y w),add_comm]; exact Nat.add_le_add_left (hx w) _
lemma occupied (u:∀ w,Site (L w).c)(e:∀ w,Axis) : Calm (fromV L (fun w=>(L w).s.ratio.embed (u w))) (fun w x=> edgeColor x (u w,e w)) N:=by
 let f (w:W)(x:Link G (L w).c)(j:G.ColorIndex):= x (u w,coord (e w), j)
 have he : Calm (fromV L (fun w=>(L w).s.ratio.embed (u w))) f N:= Calm.piP f fun j=> Calm.pick _ (fun w=>(u w,coord (e w),j)) 0 (fun w=> (separation_self _).le)
 let G': (G.ColorIndex→ℝ) ≃L[ℝ] G.Color:= (WithLp.linearEquiv (p:=2) ℝ _).symm.toContinuousLinearEquiv
 exact he.maps G'.toContinuousLinearMap
lemma pumping (e:∀ w, Edge (Site (L w).c)): Calm (fromV L (fun w=>(L w).s.ratio.embed (e w).1)) (fun w x=> G.mat (input G (L w).c x (e w))) N:=by
 have h:= occupied L (fun w=> (e w).1) (fun w=>(e w).2) (N:=N)
 refine (h.forward (fun x=> G.mat (G.lieExp x)) (fun _=>G.exp_jet.contDiffAt) 0 (fun i=> by simp)).near (fun w=> ?_); exact Eventually.of_forall fun x=> congr_arg G.mat (input_color x (e w)).symm
lemma carpet (i:∀ w,(L w).wood.Free): Calm (fromV L (fun w=> ((i w).val).1))
     (fun w x=> (L w).ρ (arm G (L w).c 1 x) (i w)) N:=by
    let F w (x:Link G (L w).c)(j:G.ColorIndex):= (L w).ρ (arm G (L w).c 1 x) (i w) j
    let A : (G.ColorIndex→ℝ) ≃L[ℝ] G.Color:=(WithLp.linearEquiv (p:=2) ℝ _).symm.toContinuousLinearEquiv
    let R:= fromV L (fun w=> ((i w).val).1)
    suffices he: Calm R F N from he.maps A.toContinuousLinearMap
    refine Calm.piP F (fun j=>?_)
    let U w:= (arm G (L w).c 1).trans (Push.Uniform.tint G (Body 1 (L w).c)).symm
    let P w: (L w).tab≃ Push.Uniform.Primary (L w).c G:= (Equiv.prodAssoc ..).symm
    let Y(w):=Key (L w).wood G
    have he:= earnings L (fun w=> (i w,j)) (N:=N)
    have ht(w:W)(z:(L w).tab): U w (desk z)=desk (P w z):=by
       funext y; rcases y with ⟨⟨m,l⟩,k⟩; change desk z (m,l,k)= desk (P w z) ((m,l),k); by_cases he:z=(m,l,k)
       · rw [he,show P w (m,l,k)=((m,l),k) from rfl]; simp [desk]
       have hh: P w z≠ ((m,l),k):= fun h=> he ((P w).injective h)
       rw [show desk z (m,l,k)=0 from Pi.single_eq_of_ne (Ne.symm he) _,show desk (P w z) ((m,l),k)=0 from Pi.single_eq_of_ne (Ne.symm hh) _]
    apply cell_move P R he (fun w=> (U w).toContinuousLinearMap) ht (fun w i=> rfl) |>.near
    intro w; exact Eventually.of_forall fun x=> by change Push.Uniform.station _ _ _=_; simp [Push.Uniform.station,U];rfl

lemma wine (e:∀ w, Edge (Site (L w).f)): Calm (fromV L (fun w=>(e w).1)) (fun w x=> G.mat ((encamp (L w).wood (L w).ρ x).1 (e w))) N:=by
 classical
 let J(v:Bool) (w:W):Prop:= decide ((e w)∈ (L w).wood.trunks)=v
 refine Calm.assemble Finset.univ (P:=J) (fun w=>⟨_,Finset.mem_univ _,rfl⟩) (fun v _=>?_); cases v
 swap
 · exact (Calm.frozen _ (1:G.Mat)).near (fun w=>Eventually.of_forall fun x=>by change (1:G.Mat) = G.mat ((encamp (L w.val).wood (L w.val).ρ x).1 (e w.val)); rw [show (encamp (L w.val).wood (L w.val).ρ x).1 (e w.val)=1 from (L w.val).wood.on_tree _ ⟨_, of_decide_eq_true w.property⟩]; rfl)
 let Y':= {w:W// J false w}; let i (w:Y'): (L w.val).wood.Free:=⟨e w.val,of_decide_eq_false w.property⟩
 have hr(w:Y')(x:Link G (L w.val).c): (encamp (L w.val).wood (L w.val).ρ x).1 (e w.val) = G.lieExp ((L w.val).ρ (arm G (L w.val).c 1 x) (i w)) * replica (L w.val).s.ratio (input G (L w.val).c x) (e w.val):= (L w.val).wood.off_tree _ (i w)
 let D w (x:Link G (L w).c):= G.mat (replica (L w).s.ratio (input G (L w).c x) (e w))
 let r(w:W):=(L w).s.ratio
 have hd: Calm (fromV L (fun w=>(e w).1)) D N:=by
      let V (b:Bool) (w:W):Prop:= decide ((r w).parent ((e w).1+step (e w).2)=(r w).parent (e w).1)=b
      refine Calm.assemble Finset.univ (P:=V) (fun w=>⟨_,Finset.mem_univ _,rfl⟩) (fun b _=>?_); cases b
      swap
      · exact (Calm.frozen _ (1:G.Mat)).near (fun w=>Eventually.of_forall fun x=>by
           rw [show D w.val x=G.mat 1 from congr_arg G.mat (show replica (r w.val) (input G (L w.val).c x) (e w.val)=1 from if_pos (of_decide_eq_true w.property))];rfl)
      let C w : Edge (Site (L w).c) := ((r w).parent (e w).1,(e w).2)
      have hp:= moss L (x:=fun w=> (r w).embed (C w).1) (y:=fun w=> (e w).1) (pumping L C (N:=N)) P.L.val (fun w=>?_)
      rotate_left
      · refine le_trans (b:=(L w).s.ratio.count.val) ?_ (by rw [show ((L w).s.ratio.count) = (L w).s.patch.L from rfl,(L w).patch]); rw [separation_comm]; have he:= Corona.near (r w) (e w).1; change separation _ ((r w).embed ((r w).parent (e w).1)) ≤ (r w).count.val; omega
      refine (hp.from (fun w:{x// V false x}=> w.val)).near ?_; intro w; exact Eventually.of_forall fun x=> congr_arg G.mat (Eq.symm (show replica (r w.val) (input G (L w.val).c x) (e w.val)=_ from if_neg (of_decide_eq_false w.property)))
 have hf:= (carpet (N:=N) (W:=Y') (fun w=>L w.val) i).forward (fun z:G.Color=>G.mat (G.lieExp z)) (fun _=> G.exp_jet.contDiffAt) 0 (fun w=> by rw [map_zero,(L w.val).law.1];rfl)
 have hV(w:W):D w 0=1:=by simp [D]
 let M (v:G.Mat× G.Mat):= v.1*v.2
 refine ((hf.duo (hd.from (fun w:Y'=>w.val))).prop M (a:=((1,1):G.Mat×G.Mat)) (by unfold M;fun_prop) ?_).near ?_
 · intro w; exact Prod.ext (show G.mat (G.lieExp ((L w.val).ρ (arm G _ 1 (0:Link G _)) (i w)))=1 from by rw [map_zero,(L w.val).law.1];simp) (hV w.val)
 intro w; exact Eventually.of_forall fun x=> by dsimp only [Function.comp_apply,M]; rw [hr w]; rw [G.mat_mul]
end Lot
end YM.Trace.Perfect
