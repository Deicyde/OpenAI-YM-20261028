import YM.TraceExtension.Perfect.Grow
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{η D:ℝ}{B:Bed}
local notation "X"=>Link G f
local notation "A"=>arm G f 1
def fisc (B:Bed)(x y: Link G f):ℝ:= Bid.gaugeFiscal B (arm G f 1 x) (arm G f 1 y)
abbrev strive (x:X)(i:G.ColorIndex):= d 1 f *ᵥ parts G 1 (A x) i
lemma tribute (x:X)(i:G.ColorIndex)(u:Site f)(b:PlaqAxes): strive x i (u,plaquette b) = petal u b.val.1 b.val.2 x i:=by
 unfold strive; rw [← ring_plaquette]; unfold parts; rcases b with ⟨⟨a,b⟩,hb⟩; dsimp only
 have h:u+step a+step b+-step a=u+step b:=by abel
 have he:u+step a+step b-step a=u+step b:=by abel
 simp only [square,linkSum,Step.vec,Step.used,negDir,posDir,Bool.false_eq_true,↓reduceIte,add_zero,h,he,add_sub_cancel_right]; unfold petal
 simp only[PiLp.add_apply,PiLp.sub_apply]; change edgeColor x (u,a) i+(edgeColor x (_,b) i+(-edgeColor x (_,a) i+-edgeColor x (u,b) i))=_; abel
lemma fisc_pairs (x y:X)(hg:Floor B p f η D): fisc B x y= ∑ i:G.ColorIndex,(B.metric.acts f*ᵥ(strive x i)) ⬝ᵥ (strive y i):=by
 unfold fisc Bid.gaugeFiscal; apply Finset.sum_congr rfl; intro i _
 unfold K strive; rw[← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]; rw [Stationary.transposes]; nth_rw 1 [← hg.symmetric.1]; rw [Stationary.transposes]

-- forward difference identity for arbitrary plaquette chart
variable (x:Link G f)(b:Axis)(y:Link G f)(o:Site f)
abbrev leg1 (p:PlaqAxes):= p.val.1
abbrev leg2 (p:PlaqAxes):=p.val.2
lemma axis_pea (v:Site f→ℝ)(j k:Axis)(i:G.ColorIndex):
    (∑ u:Site f,v u* petal u j k (petalPush o b y) i)=(v (o-step j)-v o)*petal o b k y i-(v (o-step k)-v o)*petal o b j y i:=by
 let P:= petalPush o b y
 let NX(a:Axis)(z:Site f):ℝ:= edgeColor P (z,a) i
 let H(a:Axis):ℝ:= petal o b a y i
 have he (a) (z) : NX a z = if z=o then H a else 0:=by unfold NX P petalPush; rw[ContinuousLinearEquiv.apply_symm_apply]; split <;> rfl
 have hv (t a:Axis): ∑ u:Site f,v u*NX a (u+step t)=v (o-step t)* H a:=by
   have h(z:Site f): v z* NX a (z+step t)=if z=o-step t then v z*H a else 0 := by simp only[he,mul_ite,mul_zero,← eq_sub_iff_add_eq]
   simp_rw[h]; simp
 have hk (i) : ∑ u: Site f,v u*NX i u=v o*H i:=by simp [he,mul_ite]
 unfold petal; simp only[PiLp.add_apply,PiLp.sub_apply]; change (∑ u:Site f,v u*(NX j u+NX k (u+step j)-NX j (u+step k)-NX k u))=(v (o-step j)-v o)*H k-(v (o-step k)-v o)*H j
 simp only [mul_add,mul_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib,hv,hk]; ring

def wagesM (B:Bed)(x:X)(o:Site f)(p:PlaqAxes)(i:G.ColorIndex)(a:Axis) :=
    (B.metric.acts f*ᵥ(strive x i)) (o-step a,plaquette p)-(B.metric.acts f*ᵥ(strive x i)) (o,plaquette p)
lemma harvest (hg:Floor B p f η D): fisc B x (petalPush o b y)= ∑ i:G.ColorIndex, ∑ w:PlaqAxes,
       (wagesM B x o w i w.val.1*petal o b w.val.2 y i-wagesM B x o w i w.val.2*petal o b w.val.1 y i):=by
 rw [fisc_pairs x _ hg]; apply Finset.sum_congr rfl; intro i _; unfold dotProduct; rw [Fintype.sum_prod_type, Finset.sum_comm,← Equiv.sum_comp plaqEquiv]; apply Finset.sum_congr rfl; intro j _; simp_rw [plaq_map,tribute]; exact axis_pea b y o _ _ _ _

lemma collect_band (u: Axis → Axis→ℝ) (h:∀ i : Axis,u i i=0):
   ∑ i: Axis,∑ j:Axis,u i j=∑ v: PlaqAxes, (u v.val.1 v.val.2+u v.val.2 v.val.1):=by
 let J (i j:Axis):= if i<j then u i j else 0
 let K(i j:Axis):=if i<j then u j i else 0
 have hz(i j:Axis): u i j=J i j+K j i:=by
    by_cases he:i=j
    · subst j; simp [J,K,h]
    rcases lt_or_gt_of_ne he with h|h<;> simp [J,K,h, not_lt.mpr h.le]
 have hD(v:Axis→Axis→ℝ): ∑ i:Axis,∑ j:Axis,(if i<j then v i j else 0)= ∑ a: PlaqAxes,v a.val.1 a.val.2:=by
   -- subtype sum
   rw [← Fintype.sum_prod_type (f:=fun b:Axis×Axis=> if b.1<b.2 then v b.1 b.2 else 0)];
   let s := univ.filter (fun b:Axis×Axis=> b.1<b.2)
   have he : ∑ i∈s,v i.1 i.2= ∑ a:PlaqAxes,v a.val.1 a.val.2:=Finset.sum_subtype (p:=fun i:Axis×Axis=> i.1 < i.2) s (fun i=> by simp [s]) (fun b:Axis×Axis=>v b.1 b.2)
   rw [← he]; exact (Finset.sum_filter (fun b:Axis×Axis=> b.1<b.2) (f:=fun b=> v b.1 b.2) (s:=Finset.univ)).symm
 calc
   _ = ∑ i:Axis,∑ j:Axis,(J i j+K j i):=Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>hz i j
   _ = (∑ i:Axis,∑ j:Axis,J i j)+(∑ j: Axis,∑ i:Axis,K j i) := by simp_rw [Finset.sum_add_distrib]; congr 1; rw [Finset.sum_comm]
   _ = _:=by rw[show (∑ i:Axis,∑ j:Axis,J i j)=_ from hD u,show (∑ j:Axis,∑ i:Axis,K j i)=_ from hD (fun j i=>u i j),Finset.sum_add_distrib]
-- combine
end YM.Trace.Perfect

