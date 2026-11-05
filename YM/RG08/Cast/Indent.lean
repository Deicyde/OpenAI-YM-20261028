import YM.RG08.Cast.Entrust

/-! # Kinetic anchor re-lift uniqueness and color rank convention, common cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Loop
open AnalyticNext.QuarticMatch.BoxChain
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix RealInnerProductSpace
variable {G:Gauge}{I:Type}{n:ℕ}{σ C:ℝ}{F:Raw I 2}{P:Side}
local notation "o" => (0:Fin 2)
local notation "u" =>(Fin.succ (0:Fin 1))

private lemma slide2 [Fintype I](F:Raw I 2):picture I 2 F=boundary u (boundary o F):=rfl
lemma bearing [Fintype I] (h:Graded F 2):Closing (picture I 2 F) ∧ Graded (picture I 2 F) 1:=by
 rw [slide2]
 constructor
 · intro y j
   change lower j (lower u (lower o (hum F y)))=0
   fin_cases j
   · exact (lower_switch u o (lower o (hum F y))).trans ((congrArg (lower u) (lower_twice o (hum F y))).trans (lower u|>.map_zero))

   exact lower_twice ..
 apply graded_iff.mpr;intro i;fin_cases i
 · exact passive (enters (graded_iff.mp h o)) (by decide)
 exact enters (passive (graded_iff.mp h u) (by decide))
lemma compress_inj [Fintype I] (F V:Raw I n){k:ℕ}(h:Graded F (fun _=>k))(hv:Graded V fun _=>k)(he:compress k F=compress k V):F=V:=by
 have hh {F:Raw I n}(H:Graded F (fun _=>k))(x:Tape n (Market (Tone I)))(he:¬permitted Cover I k x):F x=0:=by obtain ⟨i,hi⟩:=Classical.not_forall.mp he;exact graded_iff.mp H i x hi
 rw [←graded_expand k (hh h),←graded_expand k (hh hv),he]

lemma cofinal [Fintype I] {q : ℕ} {F T:Flake n (Mix I q)}(a:Fin n){σ τ C D:ℝ}(hσ:0<σ)(hτ:0<τ)(ht:Held (carpet _) σ C F)(ht':Held (carpet _) τ D T){N:ℕ→Side}(hn:Tendsto (fun i=>(N i).val) atTop atTop)(he:∀ i:ℕ,pour (P:=N i) F a=pour T a):F=T:=by
 let d (m : ℕ) := (N m).val - 1
 have hd : Tendsto d atTop atTop := tendsto_atTop.mpr fun b =>
   (hn.eventually (eventually_ge_atTop (b+1))).mono fun m hm => by
     change b+1 ≤ (N m).val at hm
     unfold d
     omega
 have hN (m : ℕ) : chain (d m) = N m := Subtype.ext (by
   have hpos := (N m).pos
   change (N m).val-1+1=(N m).val
   omega)
 funext x
 apply tendsto_nhds_unique ((Isles.pour_view ht hσ.le a x).comp hd)
 refine ((Isles.pour_view ht' hτ.le a x).comp hd).congr' (Eventually.of_forall fun m => ?_)
 change pour T a (port (chain (d m)) ∘ x) = pour F a (port (chain (d m)) ∘ x)
 rw [hN, he m]

lemma shade_pair (G:Gauge)(r:ℝ) (X:Tape 2 G.Color):
   sing (fun y=> if y o =y u then r else 0) X =r * inner ℝ (X o) (X u):=by
 let E:=(Fin.consEquiv fun _:Fin 2=>G.ColorIndex).trans (Equiv.refl _)
 unfold sing; rw [← (Fin.consEquiv fun _:Fin 2=>G.ColorIndex).sum_comp (_ : Tape 2 G.ColorIndex → ℝ), Fintype.sum_prod_type, PiLp.inner_apply,Finset.mul_sum]
 apply Finset.sum_congr rfl;intro i _
 rw [← (Equiv.funUnique (Fin 1) G.ColorIndex).symm.sum_comp (_ : Tape 1 G.ColorIndex → ℝ)]
 change (∑ j:G.ColorIndex,(if i=j then r else 0)*(∏ k:Fin 2,(X k) ((Fin.cons i (fun _=>j):Tape 2 G.ColorIndex) k)))=_
 rw [Finset.sum_eq_single i (by intro j _ hj;rw [if_neg (Ne.symm hj),zero_mul]) (by simp), if_pos rfl,Fin.prod_univ_two]
 change r * (X o i* X u i) = r*(X u i*X o i);ring

lemma beam_hue {D:Kernel (TypeFace n) (TypeFace n)}:hue (dressed G 2) (beam G D):=by
 intro x
 by_cases h:∀ i,(x i).2.card=n
 · let c(i:Fin 2):TypeFace n:=⟨(x i).2,h i⟩; let r:=D ((x o).1,c o) ((x u).1,c u)
   rw [show hat (beam G D) x=(fun y => if y o = y u then r else 0) from funext (fun i=>by unfold beam hat hum Anchor.extend;rw [dif_pos (show permitted Cover G.ColorIndex n (lyre x i) from h)];rfl)]
   constructor
   · intro k U; simp_rw [shade_pair]; congr 1
     let K:G.Color →ₗᵢ[ℝ] G.Color:={ toLinearMap := G.adjoint k, norm_map':=G.norm_adjoint k}
     exact K.inner_map_map ..
   · intro z U; simp_rw [shade_pair]
     rw [Fin.sum_univ_two];simp only [show (1:Fin 2)=u from rfl,update_self,update_of_ne (show o≠u by decide),update_of_ne (show u≠o by decide)]; rw [G.ad_skew];ring
 have he:hat (beam G D) x=0:=by funext y; exact dif_neg h
 rw [he]; exact Submodule.zero_mem _

end YM.RG08.Cast
