import YM.RG08.Gallery.Hints

/-! # Cabinet licenses (Ward→canonical). Includes exclusion of color singlet linear terms.
 Use bolt sign + conventions throughout (parameter flip permitted, by uniform parameter test
 use minus if generator negative). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open Carrel Rudder Rudder.Symmetry Anchor
open scoped Topology BigOperators ContDiff PowerSeries Classical
 set_option linter.unusedVariables false
variable {I J:Type}{n k e:ℕ}{G:YM.Gauge}

def Relay (g:I≃J)(V:Script I):Script J:=fun k l F=>V k l (g.symm ∘ F)
def pose (g:I≃J)(a:Demo J):Demo I where
 firm:=a.firm.map g.symm.toEmbedding
 play:= a.play ∘ g
 size' i hi:=a.size' _ (fun he=>hi (mem_map.mpr ⟨_,he,g.symm_apply_apply _⟩))
def dancer (g:I≃J)(a:Tray I):Tray J where
 base := a.base.map g.toEmbedding
 get:= a.get ∘ g.symm
 shut x hx:=a.shut _ (fun ht=>hx (mem_map.mpr ⟨_,ht,g.apply_symm_apply _⟩))

lemma pose_cry (g:I≃J)(V:Script I)(a:Tray I): announced V a= announced (Relay g V) (dancer g a):=by
 unfold announced;congr 1;funext e;apply Finset.sum_congr rfl;intro k _;congr 1; unfold dubbed;apply Finset.sum_congr rfl;intro i _
 let E:Tape i I≃Tape i J:=Equiv.arrowCongr (Equiv.refl _) g
 have hh: (desks a.base i).map (E.toEmbedding)=desks (a.base.map g.toEmbedding) i:=by
    ext y;constructor
    · intro hy;obtain ⟨x,hx,rfl⟩:=mem_map.mp hy
      apply Fintype.mem_piFinset.mpr;intro j;exact Finset.mem_map_of_mem _ (Fintype.mem_piFinset.mp hx j)
    intro hy;apply Finset.mem_map.mpr;refine ⟨E.symm y,Fintype.mem_piFinset.mpr (fun j=> ?_),E.apply_symm_apply _⟩
    obtain ⟨x,hx,hh'⟩:= Finset.mem_map.mp (Fintype.mem_piFinset.mp hy j : y j ∈a.base.map _)
    change g.symm (y j)∈ a.base; rw [← hh'];simpa using hx
 rw [volume,volume,dancer];dsimp only;rw [←hh,Finset.sum_map]
 apply Finset.sum_congr rfl;intro x _;change _ = V _ _ (g.symm ∘ (g ∘ x)) • _
 rw [show g.symm ∘ (g ∘ x)=x by ext;simp];congr 1;apply Finset.prod_congr rfl;intro j _;change a.get _=(a.get (g.symm (g _)));rw [g.symm_apply_apply];rfl

def Capri (G:YM.Gauge)(k:ℕ):Mix G.ColorIndex k≃(Cover×Exterior.TypeFace k)×G.ColorIndex:=(Equiv.prodAssoc ..).symm

def stain(u:G.El)(s:Demo (Mix G.ColorIndex 1))(i:Mix G.ColorIndex 1):ℝ:=(G.adjoint u (heavy G (fun j=>s.play (i.1,i.2.1,j)))) (i.2.2)

def Sworn (V:Script (Mix G.ColorIndex 1))(e:ℕ):Prop:=∀ (d:G.El)(a:Demo (Mix G.ColorIndex 1))(r:ℝ),∃ x y:Tray (Mix G.ColorIndex 1),(Demo.flat x).play=r • a.play ∧ (Demo.flat y).play=r • stain d a ∧ tap e (announced V x)=tap e (announced V y)
private lemma capstone (V:Script (Mix G.ColorIndex 1))(h:Sworn V e): Constant (Relay (Capri G 1) V) e:=by
 let g:=Capri G 1
 intro t a r
 obtain ⟨x,y,hx,hy,h⟩:=h t (pose g a) r
 refine ⟨dancer g x,dancer g y,?_,?_,?_⟩
 · funext i;exact (congrFun hx (g.symm i)) -- defeq
 · funext i;exact congrFun hy (g.symm i)
 rw [←pose_cry,←pose_cry];exact h

lemma heads (V:Script (Mix G.ColorIndex 1))(h:Sworn V e)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:n≤e+2)(hs:Forms.Sym (V e n)) : hue (dressed G n) (Anchor.extend 1 (V e n)):=by
 let g:=Capri G 1
 have he:=estate (capstone V h) (fun k hk i hi=>funext (fun x:Tape i _=> congrFun (ht k hk i hi) (g.symm ∘ x))) hp (fun d=> funext (fun x=> congrFun (hs d) (g.symm ∘ x)))
 intro z
 by_cases hZ:∀ i,(z i).2.card=1
 · have ht(y:Tape n G.ColorIndex):hat (Anchor.extend 1 (V e n)) z y=(Relay g V) e n (fun i=>(((z i).1,(⟨(z i).2,hZ i⟩:Exterior.TypeFace 1)),y i)):=by unfold hat hum Anchor.extend;rw [dif_pos (show permitted Cover G.ColorIndex 1 (lyre z y) from hZ)];rfl
   rw [funext ht]; apply he
 apply Eq.subst (motive:=fun x=>x∈dressed G n) _ (dressed G n).zero_mem
 ext y; unfold hat Anchor.extend hum;dsimp only; rw [dif_neg (show ¬permitted Cover G.ColorIndex 1 (lyre z y) from hZ)];rfl

lemma single_wear (F:Rudder.Raw G.ColorIndex 1)(hg:G.Simple)(he:hue (dressed G 1) F): F=0:=by
 ext x
 let v : Tape 1 (Market Tablet) := fun i => ((x i).1,(x i).2.1)
 let y : Tape 1 G.ColorIndex:=fun i=>(x i).2.2
 let f := hat F v
 let B :G.Color→ₗ[ℝ]ℝ:= ∑ i:Tape 1 G.ColorIndex,f i • ((LinearMap.proj (φ:=fun _:G.ColorIndex=>ℝ) (R:=ℝ) (i 0)).comp ((heavy G).symm.toLinearEquiv.toLinearMap))
 have ht(p:G.Color): B p=sing f (fun _=>p):=by simp only [B,LinearMap.sum_apply,LinearMap.smul_apply,sing,Fin.prod_univ_succ,Finset.univ_eq_empty,prod_empty,mul_one];rfl
 have hz:= (show (∀ u X,sing f (G.adjoint u ∘ X)=sing f X) ∧ _ from he v).1
 have hx:B=0:=Maxwell.Free.singles_inv hg B (fun q b=> by rw [ht,ht];exact hz q (fun _=>b))
 have h := ht (EuclideanSpace.basisFun G.ColorIndex ℝ (y 0));rw [hx,LinearMap.zero_apply] at h
 have hv(z:Tape 1 G.ColorIndex)(hh:z≠y):z 0≠y 0:=by intro hs;apply hh;ext i; rw [Subsingleton.elim i (0:Fin 1),hs]
 change f y=0
 unfold sing at h
 rw [Finset.sum_eq_single_of_mem y (mem_univ _)] at h
 · simpa [EuclideanSpace.basisFun_apply] using h.symm
 intro q _ hh
 simp [EuclideanSpace.basisFun_apply,hv q hh]

lemma tickets (V:Script (Mix G.ColorIndex 1))(e:ℕ)(h0:Gauged V e)(hR:Rotation V e)(hS:Sworn V e)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:n≤e+2)(hs:Forms.Sym (V e n))(h:Cohort (V e n)) {σ p :ℝ}(hu:Held (carpet _) σ p (V e n)): let F:=Anchor.extend 1 (V e n); Cloak (dressed G n) 1 F∧ Closing F∧ Held (carpet _) σ p F :=by
 intro F
 refine ⟨⟨expand_path h,expand_grade,?_, cardinality hR ht hp hs, heads V hS ht hp hs⟩,gauge_closes h0 ht hp hs,expand_cost hu⟩
 intro i; -- extension perm
 funext x; unfold woven F Anchor.extend; split_ifs with he hk hk <;> first| rfl| skip
 · exact congrFun (hs i) (fun j=>decoded Cover G.ColorIndex 1 (x j) (hk j))
 · exfalso;apply hk; intro j; obtain ⟨j,rfl⟩:=i.surjective j; exact he j
 exfalso;exact he (fun j=>hk (i j))
end YM.RG08.Gallery
