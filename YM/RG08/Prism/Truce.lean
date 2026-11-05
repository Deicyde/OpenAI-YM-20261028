import YM.RG08.Prism.Salute
import YM.RG08.Crown.Cost

/-! # Precision constitutive check for our two base choices, independent of every other rank
    higher order startup. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Function Matrix Lattice Exterior Wilson RG Precision Stationary RG08.Line Fold Drum Bloch Laurent Finset Filter Glyph Room Camera Tack Mount MvPolynomial
open Rudder Carrel Aggregate Spar Symmetry RG08.Cast
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries
variable {G:Gauge}{P:Side}{b:Bed}{C:Castle G}
lemma binal (x:Cellar (Lines G P 1))(M:Matrix (Body 1 P) (Body 1 P) ℝ):
 MvPolynomial.eval x (parley ((1/2:ℝ) • Cast.arcade (G:=G) M))= (1/2:ℝ)*winB (patron G M) x x:=by
 let I:= Lines G P 1
 have hf: Cast.arcade (G:=G) M = (fun t:Forms.Tape 2 I=> patron G M (t 0) (t 1)):=by
   funext t; rcases h:t 0 with ⟨v,f,g⟩;rcases hi:t 1 with ⟨x,l,k⟩
   have he:=Line.patron_cell G M (v,f) (x,l) g k
   unfold arcade;rw [show Fin.succ (0:Fin 1)=1 by rfl,h,hi]; unfold Spar.shaded; dsimp only [Matrix.of_apply]; by_cases hv:g=k <;> simpa [hv] using he.symm
 rw [hf,parley,map_sum]
 simp_rw [Pi.smul_apply,smul_eq_mul,MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,word,map_prod,eval_X,Fin.prod_univ_two]
 unfold winB mulVec dotProduct
 rw [←(Fin.consEquiv (fun _:Fin 2=>I)).sum_comp,Fintype.sum_prod_type,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
 rw [←(Equiv.funUnique (Fin 1) I).symm.sum_comp,Finset.mul_sum,Finset.mul_sum];apply sum_congr rfl;intro j _; simp;ring -- consEquiv etc
lemma proceed_grown {clip:Clip}{u γ θ L σ B:ℝ}(hc:Mount.Stable C)
    (HS:∀ n,Bid.Sworn b n G)(hG:G.Simple)(hY:C 0 0=Cast.starter G b θ)
    (hp:b.metric.strip σ B)(ht:∀ n,Floor b clip n γ u)(hs:0<σ)(hl:σ ≤ 1)(hC:0 ≤ B)(hz:Rigged (n:=1) (dressed G 2) σ θ L):Proceed C b P:=by
 intro x
 rw [reserve (stick 0) (P:=P) (stick 0) (hc.banner 0 0).path (hc.hold 0 0) (hc.weight ..) (hc.dial ..),hY]
 erw [Cast.listens b hp ht HS hs hl hC hz hG,binal]
-- Wilson
lemma proceed_start (hc:Mount.Stable C) (h:C 0 0=Crown.prize G 2) (he:b.metric.acts P=1): Proceed C b P:=by -- identity actual top
 intro x
 rw [reserve (stick 0) (P:=P) (stick 0) (hc.banner 0 0).path (hc.hold 0 0) (hc.weight ..) (hc.dial ..),h]; erw [Crown.basement,binal,he]
end YM.RG08.Prism
