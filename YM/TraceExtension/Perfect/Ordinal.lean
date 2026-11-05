import YM.TraceExtension.Perfect.Gain
import YM.Next.STATIONARY.Joint.Drift
import YM.Planned.PRIMARY_INTEGRAL_295.Purse

/-!
# Valuation for total-derivative jet identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Set Lattice Precision Finset
open scoped Topology ContDiff
variable {X Y V : Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup V][NormedSpace ℝ V]{n d:ℕ}{F H:X→ Y}{x:X}
open Planned.PrimaryIntegral295.Cases

def braid (F H:X→ Y)(x:X)(n:ℕ):Prop:=∀ m,m≤n→ iteratedFDeriv ℝ m F x=iteratedFDeriv ℝ m H x
lemma braided (h:F=ᶠ[𝓝 x] H): braid F H x n := fun m _=> (h.iteratedFDeriv ℝ m).eq_of_nhds
lemma braid.symm (h:braid F H x n): braid H F x n := fun i hi=>(h i hi).symm
lemma braid.trans {Z:X→Y}(h:braid F H x n)(hp:braid H Z x n): braid F Z x n:= fun _ hi=>(h _ hi).trans (hp _ hi)
lemma braid.sub {F' H':X→Y}(h : braid F H x n)(g : braid F' H' x n)
    (ha:ContDiffAt ℝ ω F x)(hb:ContDiffAt ℝ ω H x)(hc:ContDiffAt ℝ ω F' x)(hd:ContDiffAt ℝ ω H' x): braid (F-F') (H-H') x n:= fun i hi=> by rw [iteratedFDeriv_sub_apply (ha.of_le le_top) (hc.of_le le_top), iteratedFDeriv_sub_apply (hb.of_le le_top) (hd.of_le le_top),h i hi,g i hi]
lemma wove {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] {F H:Y→ V}{w:X→ Y}{a:X} (h:braid F H (w a) n)(hp:ContDiffAt ℝ ω F (w a))(hu:ContDiffAt ℝ ω H (w a))(ht:ContDiffAt ℝ ω w a): braid (F ∘ w) (H ∘ w) a n:=by
 intro i hi; ext1 z; rw [Planned.PrimaryIntegral295.Cases.compReads hp ht (by simp),Planned.PrimaryIntegral295.Cases.compReads hu ht (by simp)]; apply sum_congr rfl; intro j _; unfold caseRead; rw [h _ (j.length_le.trans hi)]
-- multiplication slabs
private lemma clm_vanish {f:X→ Y→L[ℝ]V}{v:X→ Y}(p:ContDiffAt ℝ ω f x)(g:ContDiffAt ℝ ω v x)(h₀:v x=0) (h:∀ i,i<n → iteratedFDeriv ℝ i f x=0): iteratedFDeriv ℝ n (fun y=> f y (v y)) x = 0 :=by
 let S:= interior {a|ContDiffAt ℝ ω f a∧ContDiffAt ℝ ω v a}; have hs : x∈S:=mem_interior_iff_mem_nhds.mpr ((p.eventually (by simp)).and (g.eventually (by simp)))
 let M:Y→L[ℝ]V:=0
 let B: (Y→L[ℝ]V)→L[ℝ] Y→L[ℝ]V:= ContinuousLinearMap.id ℝ _
 have he : ContDiffOn ℝ ω f S:=fun y hy=> (interior_subset hy).1.contDiffWithinAt
 have hy:ContDiffOn ℝ ω v S:=fun y hy=>(interior_subset hy).2.contDiffWithinAt
 have hz:= B.norm_iteratedFDerivWithin_le_of_bilinear he hy isOpen_interior.uniqueDiffOn hs (n:=n) (by simp)
 simp_rw [iteratedFDerivWithin_of_isOpen _ (show IsOpen S from isOpen_interior) hs] at hz
 have hu(i:ℕ)(hi:i∈ range (n+1)): ((n.choose i:ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) v x‖)=0 :=by
    have he:= mem_range.mp hi; by_cases H:i=n
    · subst i; rw [Nat.sub_self, norm_iteratedFDeriv_zero,h₀,norm_zero,mul_zero]
    rw [h i (by omega)]; simp
 rw [Finset.sum_eq_zero hu,mul_zero] at hz
 exact norm_le_zero_iff.mp hz
lemma commute {f:X→Y→L[ℝ]V}{g:X→Y→L[ℝ]V}{v:X→ Y}(ht:ContDiffAt ℝ ω f x)(hk:ContDiffAt ℝ ω g x)(hv:ContDiffAt ℝ ω v x)(hy:v x=0)(he:∀ j,j<n→iteratedFDeriv ℝ j f x=iteratedFDeriv ℝ j g x): braid (fun a=> f a (v a)) (fun a=> g a (v a)) x n:=by
 intro i hi; apply sub_eq_zero.mp; rw [← iteratedFDeriv_sub_apply ((ht.clm_apply hv).of_le le_top) ((hk.clm_apply hv).of_le le_top)]; change iteratedFDeriv ℝ i (fun y=>(f-g) y (v y)) x=0
 apply clm_vanish (ht.sub hk) hv hy (fun j hj=>?_); change iteratedFDeriv ℝ j (f-g) x=0; rw [iteratedFDeriv_sub_apply (ht.of_le le_top) (hk.of_le le_top),he j (lt_of_lt_of_le hj hi),sub_self]
lemma spirals (h:braid F H x n)(ha:ContDiffAt ℝ ω F x)(hp:ContDiffAt ℝ ω H x){r:X→ X}(ht:r x=0)(hh:ContDiffAt ℝ ω r x): braid (fun y=> fderiv ℝ F y (r y)) (fun y=> fderiv ℝ H y (r y)) x n:=by
 refine commute (ha.fderiv_right (m:=ω) (by simp)) (hp.fderiv_right (m:=ω) (by simp)) hh ht (fun j hj=>?_)
 ext1 m; ext1 u
 let v : Fin (j+1)→X := Fin.snoc m u; have he := DFunLike.congr_fun (h (j+1) hj) v
 rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_succ_apply_right] at he; simpa [v] using he
end YM.Trace.Perfect
