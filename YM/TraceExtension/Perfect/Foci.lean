import YM.TraceExtension.Perfect.Spirit

/-! # Supported carriers: send analytics from fossil along short routes. Whole factor across shear. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W:Type*}{I:W→Type} [∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]
    {N:ℕ}{G:Gauge}
-- composition with analytic function of variable times analytic constant of varying norm when bilinear. toolkit.
lemma Calm.abide {X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
    [NormedAddCommGroup Z][NormedSpace ℝ Z]{f:∀ w,Rays (I w)→ X}{g:∀ w,Rays (I w)→ Y}{D:∀ w,I w→ℕ} (B:X→L[ℝ]Y→L[ℝ]Z)(h:Calm D f N)(hp:Calm D g N) : Calm D (fun w x=> B (f w x) (g w x)) N:=by
 -- workaround Calm.forward center by separately constant families. analytic centered decomps
 obtain ⟨a,C,c,y,H⟩:=h.shape; obtain ⟨d,T,e,hT,U⟩:=hp.shape
 let f' w (_:Rays (I w)):= f w 0; let g' w (_:Rays (I w)):= g w 0
 have hf₀(i:W): ‖f i 0‖≤C:=by
    have he:=H i 0 (Nat.zero_le N); rw [zero_price] at he; simpa [spot,shelter] using he
 have hg₀(i:W): ‖g i 0‖≤T:=by
    have he:=U i 0 (Nat.zero_le N); rw [zero_price] at he; simpa [spot,shelter] using he
 have hf : Calm D f' N:=by
    refine ⟨fun _=>contDiffAt_const,a,C,c,y,fun w n hn=>?_⟩
    cases n with
    | zero=> rw [zero_price]; simpa [f',spot,shelter] using hf₀ w
    | succ n=> unfold cost f' leaf bank; rw [Finset.sum_eq_zero]; exact y; intro i _; rw [iteratedFDeriv_const_of_ne (by omega)]; simp
 have hg : Calm D g' N:=by
    refine ⟨fun _=>contDiffAt_const,d,T,e,hT,fun w n hn=>?_⟩
    cases n with
    | zero=> rw [zero_price]; simpa [g',spot,shelter] using hg₀ w
    | succ n=> unfold cost g' leaf bank; rw [Finset.sum_eq_zero]; exact hT; intro i _; rw [iteratedFDeriv_const_of_ne (by omega)]; simp
 let V w (x:Rays (I w)):=f w x - f' w x; let Y' w (x:Rays (I w)):= g w x-g' w x
 have ha : Calm D V N:= (h.over (hf.maps (-(ContinuousLinearMap.id ..)))).near (fun w=>Eventually.of_forall fun x=> by change f w x+ -f' w x=V w x; unfold V; abel)
 have ht : Calm D Y' N:= (hp.over (hg.maps (-(ContinuousLinearMap.id ..)))).near (fun w=>Eventually.of_forall fun x=> by change g w x+ -g' w x=Y' w x; unfold Y'; abel)
 have hz := (ha.duo ht).prop (a:=(0,0)) (fun x:X×Y=> B x.1 x.2) ((B.contDiff.contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst).clm_apply contDiffAt_snd) (fun i=> Prod.ext (sub_self _) (sub_self _))
 have hx := ha.mapsF (fun i=>B.flip (g i 0)) (S:=‖B.flip‖*T) (by positivity) (fun i x=> ((B.flip (g i 0)).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((B.flip.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hg₀ i) (norm_nonneg _))) (norm_nonneg _)))
 have hy := hp.mapsF (fun i=> B (f i 0)) (S:= ‖B‖*C) (by positivity) (fun i x=> ((B (f i 0)).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf₀ i) (norm_nonneg _))) (norm_nonneg _)))
 refine ((hz.over hx).over hy).near (fun i=> Eventually.of_forall fun w=>?_)
 dsimp only [Function.comp_apply, ContinuousLinearMap.flip_apply]; unfold V f' Y' g'; rw [← (B _|>.map_add)]; simp [map_sub]

lemma Calm.adgo {f:∀ w,Rays (I w)→G.El}{X:∀ w,Rays (I w)→ G.Color}{D:∀ w,I w→ℕ}(hp:Calm D (fun w x=> G.mat (f w x)) N)(ha: Calm D X N): Calm D (fun w x=> G.adjoint (f w x) (X w x)) N:=by
 let A:= G.colorMat.toContinuousLinearMap
 let M := ContinuousLinearMap.mul ℝ G.Mat
 have ht:= Calm.abide M (Calm.abide M hp (ha.maps A)) (hp.group_inv (f:=f))
 exact ht.maps G.projectColor.toContinuousLinearMap

namespace Lot
variable {P:Patch}{Y:KernelChoices} {p:Clip}{α D β v:ℝ} (L:W→ Lot G P Y p α D)
set_option quotPrecheck false
variable (K:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1))
    (o:∀ w,Site (L w).f)(hb:0<β)(hp: ∀ w,(K w).strip β (v/P.L.val))
local notation "K!"=>fun w=> installed (L w).s.ratio (K w)
local notation "F!"=>fun w=>fresh (L w).wood (L w).ρ (K! w) (o w)
include hb hp
lemma patrol (g:∀ w,Site (L w).f) (ℓ:Walk): Calm (fromV L g) (fun w x=> G.mat (travel (F! w x).1 (g w) ℓ)) N:=by
 induction ℓ generalizing g with
 | nil=>exact Calm.frozen _ _
 | cons b ℓ ih=>
   let z w:=g w+b.vec; let q w:=b.used (g w)
   have hz(w):= Progress.StationaryScenes.Response.by_one (g w) b
   have hV : Calm (fromV L g) (fun w x=> G.mat (b.read (F! w x).1 (g w))) N:=by
       let v w (x:Link G (L w).c):= (F! w x).1 (q w)
       have he:= moss L (x:=fun w=> (q w).1) (y:=g) (tailor_f L K o hb hp q (N:=N)) 1 (fun w=>by rw [separation_comm]; exact (hz w).2)
       unfold Step.read; split
       · exact he.group_inv (f:=v)
       exact he
   have he w: b.read (F! w 0).1 (g w)= (1:G.El):=by dsimp only; rw [fresh_zero (L w).law]; unfold Step.read; split <;> simp
   have hw w: travel (F! w 0).1 (z w) ℓ=(1:G.El):=by dsimp only; rw [fresh_zero (L w).law]; have hz:= Push.stroll_zero ℓ (z w) (G:=G); rw [link_one] at hz; exact hz
   exact hV.group_mul (moss L (ih z) 1 (fun w=> by rw [separation_comm]; exact (hz w).1)) he hw
lemma on_road (g:∀ w,Site (L w).c) (y:∀ w,Site (L w).f)(r:ℕ)(h:∀ w,separation ((L w).s.ratio.embed (g w)) (y w) ≤ r): let D:=fromV L (fun w=>(L w).s.ratio.embed (g w))
    Calm D (fun w x=> G.mat (road (L w).s (F! w x) (g w) (y w))) N:=by
 intro D; let X w:=(L w).s.ratio.embed (g w)
 let P (u:Walk)(w:W):Prop:= bagWalk (X w) (y w)=u
 refine Calm.assemble ((box r).image (fun k=>route 0 k 1)) (P:=P) (fun w=>⟨_,Finset.mem_image.mpr ⟨_,?_,rfl⟩, (rfl:P _ w)⟩) (fun ℓ _=>?_)
 · change lift ((y w)-(X w))∈box r
   have ht(i:Axis): (lift (y w-X w) i).natAbs≤ r:= (component_le ..).trans ((separation_comm (y w) (X w)).trans_le (h w))
   rw [box_test]; constructor<;> intro i <;> specialize ht i <;> omega
 let f w (x: Link G (L w).c):=(F! w x).2 (g w); let T w (x:Link G (L w).c):=travel (F! w x).1 (X w) ℓ
 have he : Calm D (fun w x=> G.mat (f w x*T w x)) N:= (tailor_c L K o hb hp g).group_mul (f:=f) (patrol L K o hb hp X ℓ) (fun w=>by unfold f; dsimp only; rw [fresh_zero (L w).law]; rfl) (fun w=>by change T w 0=_; unfold T; dsimp only; rw [fresh_zero (L w).law]; have he:= Push.stroll_zero ℓ (X w) (G:=G); rw [link_one] at he; exact he)
 refine (he.from (fun w:{w// P ℓ w}=> w.val)).near ?_
 intro w; refine Eventually.of_forall fun x=>?_ ; change _= G.mat (f _ _*travel (F! _ _).1 _ _); rw [show bagWalk .. = _ from w.property]
end Lot
end YM.Trace.Perfect
