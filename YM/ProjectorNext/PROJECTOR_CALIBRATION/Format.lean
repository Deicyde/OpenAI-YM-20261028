import YM.Next.FOUNDATIONS.Regular
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Covered

/-! # Compatibility checks for Packet format on chosen Machine -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Function Filter Tensor Work Labels Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} {s : Finset Cover}

section Checks
variable {n : Side} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : CoverConfig G → X} (h : Empirical s f)
include h

omit h in
private lemma reelSmooth (U : Config G n) (o : Site n) :
    ContDiff ℝ ω (fun A => reel G s (expandAt o (increment U A))) := by
  apply contDiff_pi.mpr
  intro i; unfold reel expandAt increment; rw [funext (fun A => G.mat_mul .. : ∀ A : Directions G n,
    G.mat (G.lieExp (A (wrap n i.val.1 + o,i.val.2)) * U (wrap n i.val.1 + o,i.val.2))=_)] -- fix
  exact (G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const

lemma Empirical.smoothPlace (U : Config G n) (o : Site n) :
    ContDiff ℝ ω (fun A => f (expandAt o (increment U A))) := by
  obtain ⟨g,hg,he⟩ := h; simp_rw [he]; exact hg.comp (reelSmooth (s:=s) U o)

lemma Empirical.AlongPlace (o : Site n) : Packet.Along (fun U : Config G n => f (expandAt o U)) := by
  obtain ⟨Z,hZ,hz⟩ := h
  -- a different rate formula, allowing e outside s image
  let ψ (U : Config G n) := reel G s (expandAt o U)
  let lift (i : UsedEdges s) := (wrap n i.val.1 + o,i.val.2)
  let y (e j) (U : Config G n) : Scan G s := fun i => G.colorMat (Packet.forward e j (lift i)) * ψ U i
  have he : Continuous ψ := continuous_pi fun _ => G.continuous_mat.comp (continuous_apply _)
  have hy (e : Edge (Site n)) (j : G.ColorIndex) : Continuous (y e j) := continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp he)
  have hw (e j) (U : Config G n) : HasDerivAt (fun t : ℝ => ψ (increment U (t • Packet.forward e j))) (y e j U) 0 := by
    exact hasDerivAt_pi.mpr fun i => link_step _ _ (lift i)
  simp_rw [hz]
  refine Packet.along (hZ.continuous.comp he) (fun e j (U : Config G n) => fderiv ℝ Z (ψ U) (y e j U)) (fun e j U => ?_) (fun e j => ?_)
  · exact (hZ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hw e j U) (by rw [zero_smul,G07.at_zero_increment])
  exact (((hZ.fderiv_right (m:=ω) (by simp)).continuous.comp he).clm_apply (hy e j))
end Checks

namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d) {n : Side}







variable {C : Family G} (M₀ : Machine C.params d) {N p : ℕ} (E : Packet C d N p)

/-- Unmasked representation is genuinely Smooth (germ receipt) with those
placements. This is a Regular check with the required in-place locality,
no masks included. Still have to subtract x-coordinates, account mask
compensations and buy dictionary costs etc. for a top Encode. -/
theorem regular_J (hC : M₀.Release s) (hn : Machine.Opened s (C.side N p)) (he : M₀.lined E)
    (B : BudgetPoint) (x : equationSpace (C.labels.level d)) : B.Regular (Packet.sites (C.side N p) s) (E.Jorigin x) := by
  let F:=C.labels.level d
  let m0 := (C.S.a N:ℂ)^d
  have hl : m0 ≠ 0 := pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')
  let z (i : F.Index) := (↑((C.path.levels.clock.threshold N)⁻¹ ^ (F.grades i).2):ℂ) * x.val i
  let f (U : CoverConfig G) := ∑ i, z i*(M₀.energyLeg F i U-(C.beta N p:ℂ)⁻¹*M₀.divLeg F i U)
  have hj (U : Config G (C.side N p)) : E.Jorigin x U = m0⁻¹ * f (expandAt 0 U) := by
    have ht := M₀.undressed E hC hn he x U
    rw [← show m0*E.Jorigin x U=f (expandAt 0 U) from ht, inv_mul_cancel_left₀ hl]
  have hK : Small G (fun U => m0⁻¹ * f U) := (Small.constant m0⁻¹).mul (Small.sum _ _ fun i _ =>
    (Small.constant (z i)).mul ((show Small G (M₀.energyLeg F i) from ⟨_,M₀.release_energy _ hC _⟩).sub
      ((Small.constant _).mul (show Small G (M₀.divLeg F i) from ⟨_,M₀.release_div _ hC _⟩))))
  obtain ⟨s₀,h₀⟩ := hK
  have hk (U) : ContDiffAt ℝ (↑B.order : WithTop ℕ∞) (E.Jorigin x ∘ increment U) 0 := by
    rw [funext hj]; exact (Empirical.smoothPlace h₀ U (0 : Site (C.side N p))).contDiffAt.of_le le_top
  refine ⟨M₀.supported_J E hC hn he x,?_,M₀.colored_J E hC hn he x,fun U _ => hk U,fun U _ a l hh => left_has _ hh (hk U)⟩
  rw [funext hj]
  exact (Empirical.AlongPlace h₀ _).continuous.measurable

end Machine
end YM.ProjectorNext.Calibration
