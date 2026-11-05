import YM.RG12.Spins.Tubal
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Set Lattice Wilson RG Source Source.Drops Labels Next.Foundations Planned.AtomRegular Foliage WardBin.Lies Multi.Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}(F:Frame G d)
-- Only test homogeneous 4 nonredundant. No dimension assumption
protected def four : F.Coeff →ₗ[ℂ] F.Coeff := LinearMap.pi (fun i=> if (F.grades i).1=4 then LinearMap.proj i else 0)
private abbrev vc (i:F.Index):F.Coeff:= Pi.single i 1
private lemma watch (i:F.Index)(p:Push.Local.Probe G d)(he:p.2.val ≠ (F.grades i).1):Push.Local.runProbe F p (vc F i)=0:=by
    let z:=F.basis i
    unfold vc; rw [← F.coords_basis i] -- ununfolded
    rw [Push.Local.runProbe_eq]; simp only [LinearEquiv.symm_apply_apply]; rw [deriv_read]
    have ht:MvPolynomial.IsWeightedHomogeneous generation z.val (F.grades i).1:=by intro j he; exact congrArg Prod.fst ((Labels.weight_slot j).symm.trans ((pure_grade _ _).mp (F.pure i) he))
    change _ • read _ (tier _ z.val)=0
    rw [tier,ht.weightedHomogeneousComponent_ne _ he,map_zero,smul_zero]
lemma wiring (p:Push.Local.Probe G d)(A:F.Coeff): Push.Local.runProbe F p (Spins.four F A) = if p.2.val=4 then Push.Local.runProbe F p A else 0 :=by
   have he(i:F.Index)(v:ℂ): (Spins.four F (v • vc F i))=if (F.grades i).1=4 then v • vc F i else 0:=by funext j; by_cases h:i=j <;> by_cases H:(F.grades j).1=4 <;> by_cases Hf:(F.grades i).1=4 <;> simp_all [Spins.four,vc,LinearMap.pi_apply]
   have hx:A=∑ i, A i • vc F i:=by ext k; simp [vc,Finset.sum_apply,Pi.single_apply]
   conv=> pattern Spins.four F A; arg 2; rw [hx]
   rw [map_sum,map_sum]; by_cases h:p.2.val=4
   · rw [if_pos h]; conv_rhs=> pattern A; rw [hx]
     rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [he]; split_ifs with hh; · rfl
     rw [map_zero,map_smul,watch F i p (by rw [h]; exact Ne.symm hh),smul_zero]
   rw [if_neg h]; apply Finset.sum_eq_zero; intro i _; rw [he]; split_ifs with hh
   · rw [map_smul,watch F i p (by rwa [hh]),smul_zero]
   exact map_zero _
lemma charged (H:Finset (Push.Local.Probe G d))(C:ℝ)
    (h:∀ x:F.Coeff,∀ c:ℝ,0 ≤ c→(∀ i∈H, ‖Push.Local.runProbe F i x‖ ≤ c)→F.coeffSize x ≤ C*c)(A:F.Coeff){t:ℝ}(ht:0≤t)(hz:∀ i∈H,i.2.val=4→ ‖Push.Local.runProbe F i A‖ ≤ t):
    F.coeffSize (Spins.four F A) ≤ C*t:=by
    apply h _ _ ht; intro i hi; rw [wiring]; split_ifs with HE; · exact hz i hi HE
    simpa [norm_zero] using ht
end YM.RG12.Spins
