import YM.RG12.Spins.Effort
/-! Lift integrated point estimate for symmetrized gaussian. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Noise
open Function Filter Set Lattice Wilson RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies ProofPorts.CommonComplexProduction.Score
open Pressure PhysicalNext.JointLoad.Heir Next Next.SectorChange AnalyticBridge.LocalGaussian
open Finset MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{C:Gaussian.Table (I × G.ColorIndex)}{χ: Chi}{K u t f a B c:ℝ}{n:Side}
local notation "μ" A => Gaussian.cloud A
local notation "Ω" => Prices G I
section
omit [DecidableEq I] in
private lemma flip_health (I:Type)[Fintype I](ν:Measure (Gaussian.Vec I))(h:ν.map (- ·)=ν) (F:Gaussian.Vec I→ℂ)(hF:Integrable F ν): Integrable (fun z=>F (-z)) ν :=
   (show MeasurePreserving (fun i:Gaussian.Vec I=>-i) ν ν from ⟨by fun_prop,h⟩).integrable_comp_of_integrable hF
lemma tender (z':ℂ)(F : Prices G I→ℂ) (he:Integrable F (μ C)) (h:C.PosDef)(hK:AnalyticBridge.LocalGaussian.Peak C K)(hk:0<K)
    (hu:0<u)(ht:0<t)(hc:0≤c)(p:ℕ) (hh:∀ z, ‖(F z+F (-z))/2-z'‖ ≤ ‖PhysicalNext.JointLoad.Heir.guard χ G I u t z-1‖*‖z'‖ + c*powers z^p) :
   ‖(∫ z,F z ∂(μ C))-z'‖ ≤ ‖z'‖*(2*Noise.fade t u K*(Fintype.card I:ℝ)*2^Fintype.card G.ColorIndex) + c*AnalyticBridge.LocalGaussian.Moments.meter (Fintype.card (I × G.ColorIndex)) 0 K p :=by
    let ν:= μ C
    let E:Ω → ℂ:= fun z=> F (-z)
    have hi:Integrable E ν:= flip_health _ ν (YM.Pert.Parity.cloud_neg C) _ he
    have hv:= YM.Pert.Parity.integral_cloud C F he.aestronglyMeasurable
    let A: Ω → ℂ:= fun z=> (F z + E z)/2
    have ha : A=(2:ℂ)⁻¹ • (F+E):=by ext1 z; exact div_eq_inv_mul ..
    have hA : (∫ z, F z ∂ν) - z' = ∫ z,A z-z' ∂ν:=by
       change _ = ∫ z, (A-(fun _:Ω=>z')) z ∂ν
       rw [ha,MeasureTheory.integral_sub' (Integrable.smul (2:ℂ)⁻¹ (he.add hi)) (integrable_const _), integral_const, probReal_univ, one_smul]; simp_rw [Pi.smul_apply]; rw [MeasureTheory.integral_smul ..,MeasureTheory.integral_add' he hi]; change _-_=(2:ℂ)⁻¹* (_+(∫ z,E z ∂ν)) -_; change (∫ z,E z ∂ν)=(∫ z,F z ∂ν) at hv; rw [hv]; ring
    let M(z:Ω):=c*powers z^p; let W(z:Ω):=‖PhysicalNext.JointLoad.Heir.guard χ G I u t z-1‖
    have hhA:Integrable A ν:= ha ▸ Integrable.smul (2:ℂ)⁻¹ (he.add hi)
    have hL:Integrable W ν:=by
      have hh:=guard_silent χ (G:=G) (I:=I) hu ht (n:=1)
      exact ((hh.real.continuous.integrable_of_hasCompactSupport hh.finite).sub (integrable_const _)).norm
    have hP:= AnalyticBridge.LocalGaussian.Moments.purchased ∅ hk h hK p
--    simp only [slopeEnvelope,load,Finset.sum_empty,mul_zero,Real.exp_zero,mul_one,Finset.card_empty] at hP
    have hx : slopeEnvelope (ι:=I × G.ColorIndex) ∅ K p=(fun z=>powers z^p):=by ext1 z; simp [slopeEnvelope,load]
    rw [hx,Finset.card_empty] at hP
    have HM:Integrable M ν:= hP.1.const_mul _
    rw [show (∫ z,F z ∂(μ C))-z' = ∫ z,A z-z' ∂(μ C) from hA]
    change ‖∫ z,A z-z' ∂ν‖ ≤ _
    refine (norm_integral_le_integral_norm ..).trans (le_trans (b:=(∫ z,W z*‖z'‖+M z ∂ν)) ?_ ?_)
    · exact MeasureTheory.integral_mono ((hhA.sub (integrable_const _)).norm) ((hL.mul_const _).add HM) hh
    rw [MeasureTheory.integral_add (hL.mul_const _) HM, integral_mul_const]; unfold M; rw [integral_const_mul,mul_comm ‖z'‖]
    exact add_le_add (mul_le_mul_of_nonneg_right (erode χ hu ht h hk hK) (norm_nonneg _)) (mul_le_mul_of_nonneg_left hP.2 hc)
end
#print axioms tender
end YM.RG12.Noise
