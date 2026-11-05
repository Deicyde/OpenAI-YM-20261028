import YM.TraceExtension.Perfect.Foci

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W:Type*}{I:W→Type} [∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]{N:ℕ}{G:Gauge}
lemma Calm.constFamily {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](D:∀ w,I w→ℕ)(Z:W→X)(C:ℝ)(hc:0 ≤ C)(hp:∀ w, ‖Z w‖≤C): Calm D (fun w x=>Z w) N:=by
 refine ⟨fun w=>contDiffAt_const,1,C,zero_lt_one,hc,fun w m hm=>?_⟩
 cases m with
 | zero=> rw [zero_price]; simpa [spot,shelter] using hp w
 | succ m=> unfold cost leaf bank; rw [Finset.sum_eq_zero]; exact hc; intro i _; rw [iteratedFDeriv_const_of_ne (by omega)]; simp
namespace Lot
variable {P:Patch}{Y:KernelChoices}{p:Clip}{α D β v:ℝ}(L:W→ Lot G P Y p α D)
set_option quotPrecheck false
variable (K:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1)) (o:∀ w,Site (L w).f)(hb:0<β)(hp: ∀ w,(K w).strip β (v/P.L.val))
local notation "K!"=>fun w=> installed (L w).s.ratio (K w)
local notation "F!"=>fun w=>fresh (L w).wood (L w).ρ (K! w) (o w)
include hb hp
variable (i:∀ w,Lines G (L w).f 1)
lemma lantern (e:∀ w,Site (L w).c)(d:ℕ)(hd:∀ w,separation ((L w).s.ratio.embed (e w)) (i w).1 ≤ d):
    Calm (fromV L (fun w=> (i w).1)) (fun w x => gaugeColor (armament (L w).s (F! w x) (desk (i w))) (e w)) N:=by
 let Q w:= ((i w).1,(i w).2.1)
 let X w:= edgeColor (desk (i w)) (edgeOf (Q w))
 have he : Calm (fromV L fun w=> (i w).1) (fun w _=>X w) N:=by
    let T : EuclideanSpace ℝ G.ColorIndex ≃L[ℝ] (G.ColorIndex→ℝ):= LinearEquiv.toContinuousLinearEquiv (WithLp.linearEquiv 2 ℝ _)
    let Z w j:=T (X w) j
    apply Calm.near ((show Calm (fromV L fun w=> (i w).1) (fun w x=> Z w) N from ?_).maps T.symm.toContinuousLinearMap)
    · intro w; exact Eventually.of_forall fun _ => T.symm_apply_apply _
    apply Calm.piP; intro j; refine Calm.constFamily _ _ 1 zero_le_one (fun w=>?_)
    change ‖edgeColor (desk (i w)) (edgeOf (Q w)) j‖≤_
    rw [edge_parts]; unfold desk; simp only [Pi.single_apply]; split <;> simp
 let f w:= fixRoot (L w).s (e w,vac) (Q w)
 let B:=16*(P.radius:ℝ); have hz:0≤ B:=by unfold B; positivity
 have hs : Calm (fromV L (fun w=> (i w).1)) (fun w x=> G.adjoint (road (L w).s (F! w x) (e w) (i w).1) (X w)) N:= (moss L (on_road L K o hb hp e (fun w=> (i w).1) d hd) d hd).adgo he
 refine (hs.mapsF (fun w=> f w • ContinuousLinearMap.id ℝ _) hz (fun w x=>?_)).near (fun w=>?_)
 · change ‖f w • x‖≤_; rw [norm_smul, Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   apply (fix_meter .. |>.1).trans; unfold B; rw [show P.radius=(L w).s.patch.radius from congr_arg Patch.radius (L w).patch.symm]
 exact Eventually.of_forall fun x=> (candry (S:=(L w).s) (i w) (e w) (F! w x)).symm
set_option maxHeartbeats 510000 in
lemma elements (t:∀ w,(L w).s.Choices)(z:∀ w,Lines G (L w).c 1)(d:ℕ)(h:∀ w,separation ((L w).s.ratio.embed (z w).1) (i w).1≤d):
    Calm (fromV L (fun w=> (i w).1)) (fun w x=> shuttle (L w).s (t w) (F! w x) (input G (L w).c x) (desk (i w)) (z w)) N:=by
 let P' (u:Axis×G.ColorIndex)(w:W):Prop:= (z w).2=(coord u.1,u.2)
 refine Calm.assemble Finset.univ (P:=P') (fun w=> ⟨(axisEquiv.symm (z w).2.1,(z w).2.2),Finset.mem_univ _,Prod.ext (axisEquiv.apply_symm_apply _|>.symm) rfl⟩) ?_
 rintro ⟨a,k⟩ -
 let y w := (z w).1; let V w:= (y w,a); let A:= fromV L (fun w=> (i w).1)
 let F w (x:Link G (L w).c) := armament (L w).s (F! w x) (desk (i w)); let X w (x:Link G (L w).c):= gaugeColor (F w x) (y w); let u w := y w+step a; let U w (x:Link G (L w).c):=G.adjoint (input G (L w).c x (V w)) (gaugeColor (F w x) (u w))
 let g w:= (L w).s.ratio
 have hu(w):separation ((g w).embed (u w)) (i w).1 ≤ P.L.val+d :=by
      apply (separation_triangle _ ((g w).embed (y w)) _).trans; apply Nat.add_le_add _ (h w)
      refine (Next.Free.scaled_root (g w) (u w) (y w)).trans (le_trans (Nat.mul_le_mul_left _ (show separation (u w) (y w) ≤ 1 from ?_)) ?_); · unfold u; rw [separation,add_comm (y w),add_sub_cancel_right];exact pdist_step _
      rw [Nat.mul_one]; exact (show _=_ from congr_arg (fun p:Patch=>p.L.val) (L w).patch).le
 have htV : Calm A U N:= (moss L (pumping L V) d h).adgo (lantern L K o hb hp i u _ hu)
 have he : Calm A (fun w x=> X w x - U w x) N:= ((lantern L K o hb hp i y d h).over (htV.maps (-(ContinuousLinearMap.id _ _)))).near (fun w=> Eventually.of_forall fun x=> by change X w x+ -U w x=_; exact (sub_eq_add_neg ..).symm)
 have hx:= (moss L (polarized L K o hb hp t i y a k) d h).over (he.maps (EuclideanSpace.proj k))
 refine (hx.from (fun w:{w// P' (a,k) w}=> w.val)).near (fun w=>?_)
 refine Eventually.of_forall fun x=>?_
 rw [show z w.val = (y w.val,coord a,k) from Prod.ext rfl w.property]; simp only [shuttle,_root_.add_apply,ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.add_apply]; congr 1; exact congr_arg (fun z:G.Color=> z k) (cant_at (input G (L w.val).c x) (F w.val x) (V w.val)).symm
end Lot
end YM.Trace.Perfect
