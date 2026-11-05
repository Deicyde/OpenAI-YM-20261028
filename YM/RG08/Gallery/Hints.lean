import YM.RG08.Gallery.Meridian
import YM.Next.MAXWELL.Simple

/-! # Color credit, Ward closures including lie infinitesimal receipt. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open Carrel Rudder Rudder.Symmetry Anchor
open AnalyticNext.QuarticMatch.BoxChain
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J:Type}{n k e:ℕ}{G:YM.Gauge}

-- V finite-color ports on general tag alphabet J. hue evaluation per location tuple.
private def capz (i:J):G.ColorIndex↪J×G.ColorIndex:=⟨fun x=>(i,x),fun _ _ H=>Prod.mk.inj H|>.2⟩
def drip (i:J)(x:G.Color): Demo (J × G.ColorIndex):=⟨univ.map (capz i), (fun v=> if v.1=i then x v.2 else 0),fun v hv=>if_neg (by intro hr;exact hv (mem_map.mpr ⟨v.2,mem_univ _, Prod.ext hr.symm rfl⟩))⟩

def paint (a:Demo (J×G.ColorIndex))(i:J):G.Color:= heavy G (fun k=>a.play (i,k))
def career (u:G.El)(a:Demo (J×G.ColorIndex))(i:J×G.ColorIndex):=(G.adjoint u (paint a i.1)) i.2
-- assumption trajectory exactly same centering relation in same e.
def Constant (V:Script (J×G.ColorIndex))(e:ℕ):Prop:=∀ (r:G.El)(a:Demo (J×G.ColorIndex))(t:ℝ),
    ∃ x y:Tray (J×G.ColorIndex),(Demo.flat x).play=t • a.play ∧ (Demo.flat y).play=t • career r a ∧ tap e (announced V x)=tap e (announced V y)

private lemma colors (F:Flake n (J × G.ColorIndex))(x:Tape n J)(X:Tape n G.Color):
 multi F (fun i=>drip (x i) (X i))= Rudder.Symmetry.sing (fun a=>F (fun i=>(x i,a i))) X:=by
 letI : DecidableEq (J × G.ColorIndex) := Classical.decEq _
 let E : Embedding (Tape n G.ColorIndex) (Tape n (J×G.ColorIndex)):=⟨fun a i=>(x i,a i),fun _ _ he=>funext (fun i=>congrArg (fun w=> (w i).2) he)⟩
 let W (t:Tape n (J×G.ColorIndex)):=F t*∏ i,(drip (x i) (X i)).play (t i)
 change (∑ t∈desks _ n,W t)=_
 let S:=soft univ (fun i=>drip (x i) (X i))
 have hi:univ.map E⊆desks S n:=by
    intro a ha;obtain ⟨b,_,rfl⟩:=mem_map.mp ha; apply Fintype.mem_piFinset.mpr;intro i;unfold S soft; exact Finset.mem_biUnion.mpr ⟨i,mem_univ _,mem_map.mpr ⟨b i,mem_univ _,rfl⟩⟩
 rw [←Finset.sum_subset hi ?_, Finset.sum_map] -- order solves
 · apply sum_congr rfl;intro i _;simp [W,drip,E]
 intro t _ ht; apply mul_eq_zero_of_right
 have he : ¬ ∀ i,(t i).1=x i:=by intro he; exact ht (mem_map.mpr ⟨fun i=>(t i).2,mem_univ _,funext (fun i=>Prod.ext (he i).symm rfl)⟩)
 obtain ⟨i,hi⟩:= Classical.not_forall.mp he
 exact prod_eq_zero (mem_univ i) (if_neg hi)

lemma estate {V: Script (J×G.ColorIndex)}(h:Constant V e)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:n≤e+2)(hs:Forms.Sym (V e n))(x:Tape n J): (fun y=>V e n (fun i=>(x i,y i))) ∈ dressed G n:=by
 let U(y:Tape n G.ColorIndex):=V e n (fun i=>(x i,y i))
 have he(r:G.El)(X:Tape n G.Color):sing U (G.adjoint r ∘ X)=sing U X:=by
   let a(i):=drip (x i) (X i)
   let b(i:Fin n):=drip (x i) (G.adjoint r (X i))
   rw [show U=(fun y=>V e n (fun i=>(x i,y i))) from rfl,←colors,←colors]
   symm; apply unravel hs hs a b;intro c
   have hv : career r (synth univ c a)=(synth univ c b).play:=by
      funext v
      have hh : paint (synth univ c a) v.1 = ∑ i : Fin n, c i • if v.1 = x i then X i else 0 := by
        ext j
        change (∑ i, c i * (if v.1 = x i then X i j else 0)) = _
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : v.1 = x i <;> simp [hi]
      unfold career;rw [hh,map_sum,WithLp.ofLp_sum,Finset.sum_apply];apply Finset.sum_congr rfl;intro j _;rw [_root_.map_smul];change c j*(G.adjoint r (if v.1=x j then X j else 0)) _ = _;split_ifs <;> simp_all [b,drip]
   apply sorting V e _ _ ht (fun t=> hv ▸ h r (synth univ c a) t) _ hp
 refine ⟨he,?_⟩
 intro z X
 let uX (t:ℝ)(i:Fin n):=G.adjoint (G.lieExp (t • z)) (X i)
 let L(i:Fin n)(j:G.ColorIndex):G.Color→L[ℝ]ℝ := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:G.ColorIndex=>ℝ) j).comp (heavy G).symm.toContinuousLinearMap
 have hx (i:Fin n)(j:G.ColorIndex): HasDerivAt (fun t=>uX t i j) ((G.ad z (X i)) j) 0:=L i j|>.hasFDerivAt.comp_hasDerivAt (0:ℝ) (Extra.WeakScaling.Color.tangent z (X i))
 have hh(y:Tape n G.ColorIndex):HasDerivAt (fun t=>U y * ∏ i:Fin n,uX t i (y i)) (U y*(∑ i,(G.ad z (X i)) (y i) * ∏ j∈univ.erase i,X j (y j))) 0:=by
    have hh:= (HasDerivAt.fun_finsetProd (u:=univ) (f:=fun i t=>uX t i (y i)) (fun i _=>hx i (y i))).const_mul (U y)
    have hzero (i : Fin n) : uX 0 i = X i := by simp [uX, G.adjoint_one]
    simpa only [hzero, smul_eq_mul, mul_comm] using hh
 have hg:= HasDerivAt.fun_sum (u:=univ) (fun y _=>hh y)
 change HasDerivAt (fun t=>sing U (uX t)) _ _ at hg
 simp_rw [show ∀ t,sing U (uX t)=sing U X from fun i=>he ..] at hg
 have hh0:=hg.unique (hasDerivAt_const ..)
 rw [← hh0];simp only [sing, Finset.mul_sum];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;congr 1
 rw [←Finset.mul_prod_erase _ (fun k=> update X j (G.ad z (X j)) k (i k)) (mem_univ j),update_self];congr 1;apply Finset.prod_congr rfl;intro k hk;rw [update_of_ne (Finset.ne_of_mem_erase hk)]
end YM.RG08.Gallery
