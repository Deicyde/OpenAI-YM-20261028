import YM.TraceExtension.Perfect.Pith

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Lattice Laurent RG Wilson Function Finset Filter
open scoped BigOperators Topology
variable {c f: Side} {A: Type*} [AddCommGroup A] [Module ℝ A]
def elm (a:Axis)(J:Site f→A)(x:Site f):= Pull.dTap (fun i=> J (x+i •step a)) 0
def twig (a:Axis)(J:Site f→A)(x:Site f):= J (x+step a)-J x
def takeRoot (S:Sheaf) (J:Site f→A) (x:Site f):= S.take (fun q:Cover=> J (x+wrap f q)) 0
def verse (S:Sheaf)(r:Ratio c f)(J:Site f→A):Site c→A:=takeRoot S J ∘ r.embed
lemma takeRoot_at (S:Sheaf)(J:Site f→A)(x:Site f)(w:Cover): takeRoot S J (x+wrap f w)=S.take (fun q:Cover=> J (x+wrap f q)) w:=by
 let F : Cover→A:=fun q=> J (x+wrap f q); have he : (fun q:Cover=> J (x+wrap f w+wrap f q))=fun q=> F (q+w):=by ext1 q; unfold F; rw[map_add]; congr 1; abel
 rw [takeRoot,he,S.shift_f]; dsimp only; rw[zero_add]

variable (r:Ratio c f)(L:Side)(h:r.count = L)
include h
lemma embedded_shift (x:Site c)(i:Axis)(j:ℤ): r.embed (x+j •step i)=r.embed x+wrap f (j • Sheaf.v L i):=by
 rw [show r.embed _= r.root (x+ j • step i) from rfl,map_add,map_zsmul]; rw [show r.root (step i)=r.embed (step i) from rfl,← wrap_step c i,r.embed_wrap,map_zsmul,h]; rfl
lemma elm_verse (J:Site f→A)(X:Sheaf)(x:Site c)(a:Axis): elm a (verse X r J) x=Pull.dTap (fun l=>X.take (fun q:Cover=> J (r.embed x+wrap f q)) (l • Sheaf.v L a)) 0:=by unfold elm verse;simp_rw [comp_apply,embedded_shift r L h,takeRoot_at]
omit h in
lemma elm_r (J:Site f→A)(a:Axis)(x:Site f)(w:Cover):
   elm a J (x+wrap f w)=Pull.dTap (fun l=> J (x+wrap f (w+l •step a))) 0 :=by unfold elm; congr 1; ext1 i; rw [map_add,map_zsmul,wrap_step]; congr 1; abel
lemma elm_flux (J:Site f→A)(a:Axis): (L.val:ℝ) • verse (Sheaf.main L) r (elm a J)=elm a (verse (Sheaf.flux L a) r J):=by
 ext1 x; rw [elm_verse r L h]; let F:=fun w=> J (r.embed x+wrap f w)
 have ht: (fun w=> elm a J (r.embed x+wrap f w)) = Sheaf.take (Sheaf.take F (Sheaf.band (step a))) (Sheaf.Δ (step a)):=funext fun w=> by rw [Sheaf.calc_fd]; exact elm_r _ _ _ _
 rw [Pi.smul_apply,verse, Function.comp_apply,takeRoot,ht,← Pi.smul_apply,Sheaf.flux_delta,Sheaf.calc_fd]; simp only [zero_add]; rfl
lemma verse_twig (J:Site f→A)(a:Axis)(x:Site c)(S:Sheaf): twig a (verse S r J) x= Sheaf.take (Sheaf.take (fun z=> J (r.embed x+wrap f z)) S) (Sheaf.Δ (Sheaf.v L a)) 0:=by
   unfold twig verse; simp only [Function.comp_apply]; rw [r.embed_leap,h]; rw [← show Lattice.wrap f (Sheaf.v L a)=L.val • step a by unfold Sheaf.v;rw [map_nsmul,wrap_step],takeRoot_at, Sheaf.rises, zero_add]; rfl
lemma twig_r (J:Site f→A)(a:Axis): verse (Sheaf.main L) r (twig a J)=((L.val:ℝ))⁻¹ • twig a (verse (Sheaf.leafEdge L a) r J):=by
 ext1 x; rw [Pi.smul_apply,verse_twig r L h]; let F:=fun w=> J (r.embed x+wrap f w)
 have hv : (fun w=> twig a J (r.embed x+wrap f w))=Sheaf.take F (Sheaf.Δ (step a)):= funext fun w=>by unfold twig; rw [Sheaf.rises]; unfold F; rw [map_add,wrap_step, add_assoc]
 rw [verse, Function.comp_apply,takeRoot,hv,Sheaf.main_leaf]; rfl
lemma verse_trail (X:Sheaf)(a:Axis)(hX:∀ f: Cover→ A,Sheaf.take f (Sheaf.flux L a)= Sheaf.take f (Sheaf.main L)+Sheaf.take (Sheaf.take f X) (Sheaf.Δ (Sheaf.v L a)))(J:Site f→A):
   verse (Sheaf.flux L a) r J=verse (Sheaf.main L) r J+twig a (verse X r J):=by ext1 x; rw [Pi.add_apply,verse_twig r L h,verse, Function.comp_apply,takeRoot,hX];rfl
omit h in
def mixer (S:Sheaf)(r:Ratio c f): (Site f→A)→ₗ[ℝ] (Site c→A) where
 toFun:=verse S r
 map_add' X Y:=funext fun x=>congr_fun (Sheaf.add_f S (fun w=> X (r.embed x+wrap f w)) (fun w=>Y (r.embed x+wrap f w))) 0
 map_smul' u X:=funext fun x=>congr_fun (Sheaf.smul_f S (fun w=>X (r.embed x+wrap f w)) u) 0
-- difference operators
omit h in
def sprig (a:Axis): (Site f→A)→ₗ[ℝ] (Site f→A) where
 toFun:=twig a
 map_add' X Y:=by funext x; simp only[twig,Pi.add_apply]; abel
 map_smul' u X:=funext fun x=> (smul_sub u ..).symm
omit h in
lemma rate_elm (Y:Site f→A)(u:ℝ)(a:Axis): elm a (u • Y)=u • elm a Y:=by
 unfold elm Pull.dTap; funext x; simp only [Pi.smul_apply, ← smul_sub]; simp_rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; exact smul_comm ..
end YM.Trace.Perfect
