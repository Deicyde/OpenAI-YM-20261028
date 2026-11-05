import YM.PertExtension.HuePanel

/-! Haar Reynolds projection on the actual stencil polynomials; no path
order bounds from this averaging are used downstream. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.PertExtension.Hue
open Function Filter Set Finset MeasureTheory MvPolynomial Lattice Heat.Top Next.Rank
open Wilson RG Source Bid Labels Drops
open scoped Matrix.Norms.Frobenius Topology Classical BigOperators Real ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{α β :Type*}

inductive Sheaf : (G.El→Poly α G)→Prop where
 | basic (p : Poly α G)(f:G.El→ℂ)(h:Continuous f): Sheaf fun u=> f u • p
 | append {f g:G.El→Poly α G}: Sheaf f → Sheaf g → Sheaf (f+g)
lemma Sheaf.const (p:Poly α G): Sheaf fun _=>p:=by convert Sheaf.basic p (fun _=>1) continuous_const; simp
lemma Sheaf.scale (f:G.El→ℂ){p:G.El→Poly α G}(h:Sheaf p)(hf:Continuous f) : Sheaf fun u=> f u • (p u) := by
  induction h with
  | basic p g hg=> simp_rw [smul_smul]; exact Sheaf.basic p _ (hf.mul hg)
  | @append p q h H ih ih₂=> rw [show (fun u=>f u • (p+q) u) = (fun u=>f u • p u) + (fun u=>f u • q u) by ext1;simp [smul_add]]; exact .append ih ih₂
lemma Sheaf.mul_base (b:Poly α G){p:G.El→Poly α G}(h:Sheaf p):Sheaf (fun u=>b*p u):=by
   induction h with
   | basic p g hg=> convert Sheaf.basic (b*p) g hg using 1; funext u; simp
   | @append f g h H ih ih₂=> rw [show (fun u=>b*(f+g) u)=(fun u=>b*f u)+(fun u=>b*g u) by funext u; simp only [Pi.add_apply,mul_add]];exact .append ih ih₂
lemma Sheaf.mul {p q:G.El→Poly α G}(hp:Sheaf p)(hq:Sheaf q): Sheaf (p*q):=by
   induction hp with
   | basic p f hf=> convert Sheaf.scale f (hq.mul_base p) hf using 1; funext u; simp
   | append h h' ih ih'=>rw [add_mul];exact .append ih ih'

@[fun_prop] lemma pigment (i j:G.ColorIndex) : Continuous (fun u:G.El=>((↑(G.adjoint u (EuclideanSpace.basisFun _ ℝ j) i:ℝ)):ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp
    apply G.projectColor.continuous_of_finiteDimensional.comp
    exact ((G.continuous_mat.mul continuous_const).mul (continuous_star.comp G.continuous_mat))
lemma built (P:Poly α G): Sheaf fun u=>inked u P := by
   induction P using MvPolynomial.induction_on with
   | C v=> convert Sheaf.const (C v);simp
   | add p q hp hq=> convert hp.append hq; simp
   | mul_X p i hp=>
     suffices hx : Sheaf fun u:G.El=>inked u (X i) by
         convert hp.mul hx using 1;funext u; simp
     simp_rw [Normal.exchange_x,rag,_root_.map_sum,Normal.glyph,Finsupp.linearCombination_single]
     generalize (Finset.univ: Finset G.ColorIndex)=s
     induction s using Finset.induction_on with
     | empty=>exact Sheaf.const _
     | insert j s hj ih=>
        simp_rw [sum_insert hj]
        exact .append (.basic _ _ (pigment i.2 _)) ih

abbrev Form (α : Type*)(G) := Poly α G →ₗ[ℂ] ℂ
lemma integrate_sheaf {p:G.El→Poly α G}(hp:Sheaf p) : (∀ f:Form α G, Continuous (fun u=>f (p u))) ∧ ∃ Q:Poly α G, ∀ f: Form α G, f Q = ∫ u:G.El,f (p u) ∂G.probHaar := by
   induction hp with
   | basic p g hg=>exact ⟨fun f=>by simp_rw [map_smul];exact hg.smul continuous_const, (∫ u:G.El,g u ∂G.probHaar) • p,fun f=>by simp_rw [map_smul,smul_eq_mul,integral_mul_const]⟩
   | @append p q h h' ih ih'=>
     obtain ⟨hh,P,z⟩:=ih
     obtain ⟨hh',Q,z'⟩:=ih'
     refine ⟨fun f'=>by simp_rw [Pi.add_apply,map_add]; exact (hh f').add (hh' f'), P+Q,?_⟩
     intro f'
     simp only [Pi.add_apply,map_add,z f',z' f']
     exact (integral_add (Continuous.integrable_of_hasCompactSupport (hh _) (HasCompactSupport.of_compactSpace _) (μ:=G.probHaar)) (Continuous.integrable_of_hasCompactSupport (hh' _) (HasCompactSupport.of_compactSpace _))).symm

def portrait (p : Poly α G) := (integrate_sheaf (built p)).2.choose
theorem portrait_spec (p:Poly α G)(f:Form α G): f (portrait p) = ∫ u,f (inked u p) ∂G.probHaar := (integrate_sheaf (built p)).2.choose_spec f
lemma portrait_fixed (p:Poly α G) : Fixed (portrait p) := by
   intro u x; let f(v):=display (tint v x) p
   change (display (tint u x)).toLinearMap (portrait p) = (display x).toLinearMap _;
   simp_rw [portrait_spec p (display _).toLinearMap];simp only [AlgHom.toLinearMap_apply]
   simp_rw [← hue]
   change (∫ v:G.El, display _ p ∂G.probHaar)= ∫ v:G.El, f v ∂G.probHaar
   have h(v:G.El):display (tint v (tint u x)) p=f (v*u):=by rw [show tint v (tint u x)=tint (v*u) x from funext fun i=> (G.adjoint_mul ..).symm]
   simp_rw [h]
   exact (measurePreserving_mul_right G.probHaar u).integral_comp (Homeomorph.mulRight u).measurableEmbedding f

end YM.PertExtension.Hue
