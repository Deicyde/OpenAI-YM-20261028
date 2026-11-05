import YM.MultipleContact.Direct
import Mathlib.Analysis.Distribution.TestFunction

set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact
open Filter MeasureTheory Set TopologicalSpace Metric
open scoped Topology ContDiff Distributions BigOperators Classical
variable {E F : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F]

private def budget (K:Compacts E)(j:ℕ)(f:𝓓_{K}(E,ℂ)):ℝ:= ∑ i ∈ Finset.range (j+1),ContDiffMapSupportedIn.seminorm ℝ E ℂ ⊤ K i f
omit [NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F] in
private lemma budget_pts (K:Compacts E)(j:ℕ)(f:𝓓_{K}(E,ℂ)): JetBounds j f (budget K j f):=by
    have he (i:ℕ):0≤ ContDiffMapSupportedIn.seminorm ℝ E ℂ ⊤ K i f := apply_nonneg _ _
    have hw (i:ℕ)(hi:i≤j): ContDiffMapSupportedIn.seminorm ℝ E ℂ ⊤ K i f ≤ budget K j f:= Finset.single_le_sum (fun i _=>he i) (Finset.mem_range.2 (by omega))
    exact ⟨(he 0|>.trans (hw 0 (by omega))),fun y i hi=> ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ |>.trans (hw i hi)⟩

lemma has_bound {U:Opens E} (f:𝓓(U,ℂ))(j:ℕ):∃ A:ℝ,JetBounds j f A:=by
      let K:Compacts E := ⟨tsupport f,f.hasCompactSupport⟩; let g:𝓓_{K}(E,ℂ) := .of_support_subset f.contDiff subset_closure
      exact ⟨_,budget_pts K j g⟩

lemma cont_mk {j:ℕ} {U:Opens E} {f:𝓓(U,ℂ) →ₗ[ℂ] F} (h:∀ (K:Compacts E)(hk:(K:Set E)⊆U), ∃ C:ℝ,∀ (g:𝓓_{K}(E,ℂ)),∀ (A:ℝ),JetBounds j g A→ ‖f (TestFunction.ofSupportedIn hk g)‖≤ C*A): Continuous f :=by
  apply (TestFunction.continuous_iff_continuous_comp f).mpr
  intro K hk; obtain ⟨C,hC⟩:=h K hk
  let D:𝓓_{K}(E,ℂ)→ₗ[ℂ] F := f.comp (TestFunction.ofSupportedInCLM ℂ hk).toLinearMap
  refine continuous_of_continuousAt_zero D ?_
  change Tendsto (fun g:𝓓_{K}(E,ℂ)=>D g) (𝓝 0) (𝓝 (D 0)); rw [map_zero]
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (g:𝓓_{K}(E,ℂ)):‖D g‖≤ C * budget K j g := hC g _ (budget_pts K j g)
  apply squeeze_zero (fun _=> dist_nonneg) (fun g=>le_trans (by rw [dist_zero_right]) (he g))
  have hv:Continuous (budget K j) := continuous_finsetSum _ fun i _=> (ContDiffMapSupportedIn.withSeminorms ℝ E ℂ ⊤ K).continuous_seminorm i
  change Tendsto (C * budget K j ·) _ _; have ht:= hv.continuousAt (x:=0)|>.const_mul C
  rw [show (0:ℝ)= (fun x=>C*budget K j x) 0 from (by simp [budget])]; exact ht

omit [NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F] in
theorem diff_add {f g:E→ℂ} (hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g) (s:ℝ)(x:E)(m:Option ℕ): diff s m (f+g) x=diff s m f x + diff s m g x:=by
   cases m with
   | none=>rfl
   | some m=>
     have hh (i:ℕ):coeff i (f+g) x=coeff i f x+coeff i g x:=by
        unfold coeff; rw [iteratedFDeriv_add_apply ..]
        · rw [_root_.add_apply,smul_add]
        exacts [hf.contDiffAt.of_le (mod_cast le_top),hg.contDiffAt.of_le (mod_cast le_top)]
     simp_rw [diff,Pi.add_apply,polyJet,hh,Finset.sum_add_distrib,smul_add]; abel
omit [NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F] in
theorem diff_smul {f:E→ℂ} (hf:ContDiff ℝ ∞ f) (s:ℝ)(x:E)(a:ℂ)(m:Option ℕ): diff s m (a•f) x=a•diff s m f x:=by
   cases m with
   | none=>rfl
   | some m=>
     have hh (i:ℕ):coeff i (a•f) x=a•coeff i f x:=by
        unfold coeff; rw [iteratedFDeriv_const_smul_apply]
        · rw [_root_.smul_apply,smul_comm]
        exact hf.contDiffAt.of_le (mod_cast le_top)
     simp_rw [diff,Pi.smul_apply,smul_sub,smul_comm a (cutoff s x),polyJet,hh,Finset.smul_sum]

namespace Direct
variable [FiniteDimensional ℝ E] [MeasureSpace E] [(volume : Measure E).IsAddHaarMeasure] [BorelSpace E]
variable {R p c:ℝ} {K : E→F} {m:Option ℕ} (hd:1≤Module.finrank ℝ E) (hk:Kas R p c K)

/-- Actual Taylor-subtracted jet term as a complex-linear distribution on any open U (only the ball of integration is sampled here). -/
def functional {U : Opens E} (s:ℝ)(hs:0<s)(m:Option ℕ)(hp:p+price m>-(Module.finrank ℝ E:ℝ)):
    𝓓(U, ℂ)→L[ℂ] F :=by
    have he (f:𝓓(U,ℂ)): IntegrableOn (fun x=>diff s m (f:E→ℂ) x • K x) (ball 0 R):=let A:=has_bound f (price m); (localPair hd hk f.contDiff A.choose_spec hs hp).1
    let v : 𝓓(U,ℂ)→ₗ[ℂ] F := {
       toFun := fun f=>term R s m K (f:E→ℂ)
       map_add' := fun f g=>by
          unfold term; change (∫ x:E in ball 0 R,diff s m ((f:E→ℂ)+(g:E→ℂ)) x • K x)=_
          simp_rw [diff_add f.contDiff g.contDiff,add_smul,integral_add (he f) (he g)]
       map_smul' := fun a f=>by
          unfold term; change (∫ x:E in ball 0 R,diff s m (a•(f:E→ℂ)) x • K x)=_
          simp_rw [diff_smul f.contDiff,smul_eq_mul,mul_smul,integral_smul,RingHom.id_apply]
    }
    refine ⟨v,cont_mk (j:=price m) fun _ _=> ?_⟩
    exact ⟨_,fun f _ hA=>(localPair hd hk f.contDiff hA hs hp).2⟩
lemma functional_eq {U : Opens E} (s:ℝ)(hs:0<s)(m:Option ℕ)(hp:p+price m>-(Module.finrank ℝ E:ℝ))(f:𝓓(U,ℂ)) : functional hd hk s hs m hp f=term R s m K (f:E→ℂ):=rfl
end Direct
end YM.MultipleContact
