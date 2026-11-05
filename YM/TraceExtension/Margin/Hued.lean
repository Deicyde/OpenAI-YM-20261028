import YM.TraceExtension.Margin.Motion
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
variable (F:Frame G 4)(Z:Labels.Frame G 5) {R: Rep G s} {t:ℝ}
-- Holt operational scalar bill on component stencils
lemma vitrine (a:G.ColorIndex) (x:Axis→ Z.Coeff)(h:G.Simple)(hx:∀ i,realBar (Z.coords.symm (x i))=Z.coords.symm (x i)): let S:= Reed (Prism Z) x
    archK a (fun i=> Z.coords.symm (S i))=archK a (fun i=> Z.coords.symm (x i)):=by
    let p(i:Motion)(d:Axis):Label G 5:= (hued i d) • tensor i.1.ortho (Z.coords.symm (x (prev i d))); let w:= fun i=> Z.coords.symm (x i)
    have he(i: Motion): archK a (p i)=archK a w:= coin_r _ _ _ _ h (fun d=>by unfold p; rw[show prev i _=d from i.1.perm.symm_apply_apply d, show hued i (i.1.perm d)=sign i.1 d from congr_arg _ (i.1.perm.symm_apply_apply _)])
    intro S; let L:= (archK a).restrictScalars ℝ; change L _=L w
    have ht : (fun i=>Z.coords.symm (S i))=∑ i:Motion,rent • p i:=by
        ext1 i; unfold S; rw[reedEq,map_sum,Finset.sum_apply]; apply sum_congr rfl; intro j _; rw [show Z.coords.symm ((_ : ℝ) • _)=_ from (Z.coords.symm.toLinearMap.restrictScalars ℝ).map_smul (rent*hued j i) (Prism Z j (x (prev j i)))]; change (_:ℝ) • Z.coords.symm _= rent • p j i; rw[cloakR _ _ _ (hx _), mul_smul]
    rw[ht,map_sum]; simp_rw [map_smul]; change ∑ i:Motion,rent • archK a (p i) = archK a w; rw[sum_congr rfl (g:=fun _:Motion=>rent • archK a w) (fun i _=> congr_arg _ (he i)),Finset.sum_const,Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,rent,mul_inv_cancel₀ (by positivity),one_smul]
lemma Lease_paid (a:G.ColorIndex)(V:Bowl Z)(h:G.Simple): (Lease Z h V:ℂ)= (archK a (fun i=>Z.coords.symm (V.val i)))/12:=by
    change ((rho h ((plate Z) V):ℝ):ℂ)=archK a ((plate Z) V).val/12; rw[Kits.arch_rho _ _ h];ring
end YM.Trace.Margin
