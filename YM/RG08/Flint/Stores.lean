import YM.RG08.Flint.Pump
import YM.RG08.Flint.Score

/-! # Polarized cover evaluation is continuous in stencil families.
Fixed order and horizon. Extraction pointwise in test φ via septet.
Rigorous truncation for unbounded growing directions and products.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Jetty Forms Function Finset Filter Lattice Laurent Carrel MvPolynomial Glyph
open scoped Topology ENNReal Classical BigOperators
variable {I J:Type}{p d n:ℕ}{σ δ C:ℝ}{L:Loom I}{K K' B:ℝ}{F:Pack n I}{h:0<σ}

-- sparse real tapes; u cochain site & edges. no J.Phrases. auxiliary u(t j) indexed by fixed Fin.
lemma sonic_zero {i:Fin n}{X:Fin n→I→ℝ}(ht:X i=0)(f:Pearl):sonic F f X=0:=by
 unfold sonic tote flakes
 have hz(x:Tape n I):(∏ j:Fin n,X j (x j))=0:=prod_eq_zero (mem_univ i) (by rw [ht];rfl)
 simp_rw [hz,mul_zero];exact tsum_zero
lemma sonic_swap (f:Pearl)(he:Forms.Sym (fun x=>F x f))(X:Fin n→I→ℝ)(e:Equiv.Perm (Fin n)):sonic F f (X ∘ e)=sonic F f X:=by
 unfold sonic tote flakes; nth_rw 1 [← (Forms.twist (I:=I) e).tsum_eq]
 apply tsum_congr;intro i; change F (i ∘ _) f * _=_
 rw [show F (i ∘ ⇑e) f=F i f from congrFun (he e) i]; congr 1; exact Equiv.prod_comp e (fun j=>X j (i j))

-- product sums in any finite alphabet family distinct per j.
lemma sonic_bill [Fintype J](he:Lyrics F)(hh:Sings L d h F B)(hb:0≤B)(f:Pearl){a:Fin n→J→ℝ}{X:Fin n→J→I→ℝ}(hx:0≤δ)(hy:(n:ℝ)*δ≤σ/2)(hz:∀ i j,Bearing L p δ (a i j) (X i j)):
 sonic F f (fun j=>∑ i:J,X j i)=∑ t:Tape n J,sonic F f (fun i=>X i (t i)):=by
 unfold sonic tote flakes;simp_rw [Finset.sum_apply];simp_rw [Fintype.prod_sum]
 simp_rw [mul_sum]
 rw [Summable.tsum_finsetSum (f:=fun (t:Tape n J) (x:Tape n I)=>F x f*∏ i:Fin n,X i (t i) (x i)) (fun (t:Tape n J) (_:t∈Finset.univ)=> (sonic_abs he hh hb f (a:=fun i=>a i (t i)) (V:=fun i=>X i (t i)) hx hy (fun i=>hz ..)).of_norm)]
lemma sonic_pull (f:Pearl)(X:Fin n→I→ℝ)(t:Fin n→ℝ):sonic F f (fun i=>t i • X i)=(∏ i,t i)*sonic F f X:=by
 unfold sonic tote flakes;rw [← tsum_mul_left]; apply tsum_congr;intro i;simp_rw [Pi.smul_apply,smul_eq_mul,prod_mul_distrib];ring

def modal (F:Pack n I)(f:Pearl)(X:J→I→ℝ):Flake n J:=fun x=>sonic F f (X ∘ x)
lemma modal_sym (f:Pearl){X:J→I→ℝ}(he:Forms.Sym (fun x=>F x f)):Forms.Sym (modal F f X):=fun e=>funext fun t=>sonic_swap f he (X ∘ t) e
lemma modal_read [Fintype J](f:Pearl)(he:Lyrics F)(hh:Sings L d h F B)(hb:0≤B)(u:J→ℝ){X:J→I→ℝ}(a:J→ℝ)(hx:0≤δ)(hy:(n:ℝ)*δ≤σ/2)(hz:∀ i,Bearing L p δ (a i) (X i)):
 sonic F f (fun _=>∑ i:J,u i • X i)= MvPolynomial.eval u (parley (modal F f X)):=by
 rw [parley_street,sonic_bill he hh hb f (X:=fun _ i=>u i • X i) (a:=fun _ i=>|u i| * a i) hx hy (fun _ i=> (hz _).smul (u i))]
 apply sum_congr rfl;intro i _;rw [sonic_pull,mul_comm];rfl
-- damping test extension by dominated convergence, independent of radius growth.
lemma sonic_turn (f:Pearl)(he:Lyrics F)(hh:Sings L d h F B)(hb:0≤B){U:Type}{l:Filter U}[l.NeBot]{Y:Fin n→I→ℝ}{X:U→Fin n→I→ℝ}(ht:∀ i j, Tendsto (fun u=>X u i j) l (𝓝 (Y i j)))
 {a:Fin n→ℝ}(hx:0≤δ)(hy:(n:ℝ)*δ≤σ/2)(hz:∀ u i,Bearing L p δ (a i) (X u i)): Tendsto (fun u=>sonic F f (X u)) l (𝓝 (sonic F f Y)):=by
 let V(i:Fin n)(x:I):=a i*hustle p δ (L.height x)
 have hn(i):0≤a i:= (hz (Classical.choice (nonempty_of_neBot l)) i).1
 have hv(i):Bearing L p δ (a i) (V i):=⟨hn i,fun x=> (abs_of_nonneg (mul_nonneg (hn _) (hustle_nn p δ (L.nn x)))).le⟩
 have ha:=sonic_abs he hh hb f hx hy hv
 unfold sonic
 refine tendsto_tsum_of_dominated_convergence ha (fun x=> tendsto_const_nhds.mul (tendsto_finsetProd _ (fun j _=>ht j (x j)))) (Eventually.of_forall (fun u x=>?_))
 simp only [tote,flakes,Real.norm_eq_abs,abs_mul,Finset.abs_prod]
 apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
 exact prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>((hz ..).2 _).trans (le_abs_self _))
end YM.RG08.Flint
