import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.DriftG
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shower

/-! # Financial rotations on T (full covariance), reference preserving. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open Gas Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C η r Q Y : ℝ} {R : Rep G f} {L : Side} {B : ℕ}
variable (X : Coat T F) (z : Site c→ G.El) (h : P.Funds S T) (ht : ShellAccess S G X.x W X.width C)

lemma plate_con (h : P.Funds S T) : (sluice X z).plate * sheen X z=sheen X z* X.plate := X.rinse_invar z h
include h
lemma kernelCon : (sluice X z).kernelA * sheen X z=sheen X z* X.kernelA := pad_rotates X z (plate_con X z h)
lemma relatesG : (sluice X z).relating * sheen X z=sheen X z* X.relating := by
  have he := kernelCon X z h
  have hp := inverse_up (z ∘ atEdge S)
  unfold relating Window.frameMean; rw [smul_mul_assoc,Matrix.mul_smul]; apply congr_arg; rw [mul_add,add_mul]
  change (sluice X z).kernelA*sheen X z+_= sheen X z*X.kernelA+ _
  rw [he]; exact congr_arg _ (toss he hp hp)
lemma shredsG : (sluice X z).shreds * sheen X z = sheen X z * X.shreds := by
  unfold shreds Window.flawed; rw [sub_mul,mul_sub,one_mul,mul_one];
  let Z:=sluice X z; let E:=sheen X z
  change Z.plate*Z.relating * _-_= E*(X.plate*X.relating) - _
  rw [mul_assoc, relatesG X z h, ← mul_assoc, plate_con X z h, mul_assoc]

include ht in
lemma bCon : (sluice X z).linearBill=sheen X z *ᵥ X.linearBill := by
  let Y:= sluice X z; let a:=sheen X z; let b:=colorwise (z ∘ root S)
  have hx : stand (Y.priced 0)= b *ᵥ stand (X.priced 0) := by
    rw [shade_act]; funext i
    have hp p : Y.priced 0 p = G.adjoint (z (root S p)) (X.priced 0 p) := by
      unfold Coat.priced; by_cases ht' : X.selected (Prod.fst p) (spot S (Prod.snd p))
      · change (if X.selected _ _ then _ else _)=_
        rw [if_pos ht',if_pos ht',map_smul]
        have he := springs X h ht z 0 p.1 p.2
        rw [show spinRow S z (0:Directions G f)=0 from funext fun i=> map_zero _] at he
        exact congr_arg (Coat.scale • ·) he
      change (if X.selected _ _ then _ else _)=_
      rw [if_neg ht',if_neg ht',map_zero]
    exact congr_arg (fun p:G.Color=> p i.2) (hp i.1)
  have hY : Y.form*a=b*X.form := X.contract_step z h
  unfold linearBill; rw [hx,Matrix.mulVec_mulVec,show Y.form.transpose*b=a*X.form.transpose from toss hY (inverse_up _) (inverse_up _), Matrix.mulVec_mulVec]

include ht in
lemma slopeC :
    let Y:=sluice X z; let E:= sheen X z
    Y.driftM=E *ᵥ X.driftM ∧ Y.μ=spinRow S z X.μ := by
  intro Y E
  have hg:= bCon X z h ht
  have hh : Y.driftM=E *ᵥ X.driftM := by
    unfold driftM; rw [hg,Matrix.mulVec_neg, Matrix.mulVec_mulVec,toss (kernelCon X z h) (inverse_up _) (inverse_up _), Matrix.mulVec_mulVec]
  refine ⟨hh,?_⟩
  unfold Coat.μ; rw [hh,shade_act]; rfl

def weep (z' : Air f G) : Air f G := WithLp.toLp 2 (sheen X z *ᵥ z'.ofLp)
omit h in
lemma atmospheric (z' : Air f G) : X.atmos (weep X z z')=spinRow S z (X.atmos z') := by
  unfold atmos weep; rw [WithLp.ofLp_toLp,shade_act]; rfl
include ht in
lemma fullA (β : ℝ) (w : Air f G) :
    (sluice X z).liftA β (weep X z w)=spinRow S z (X.liftA β w) := by
  unfold liftA; rw [(slopeC X z h ht).2, show (sluice X z).atmos (weep X z w)=_ from (atmospheric X z w)];
  funext; simp only [spinRow,Pi.add_apply,Pi.smul_apply,map_add,map_smul]

include h in
lemma speeds (hA : X.relating.PosDef) (hA' : (sluice X z).relating.PosDef) : MeasurePreserving (weep X z) X.dice (sluice X z).dice := by
  let a:=X.relating; let b:=(sluice X z).relating; let E:=sheen X z
  have hp : Measurable (weep X z) := by
    let f : Air f G→ₗ[ℝ] Air f G := toEuclideanLin E
    exact f.continuous_of_finiteDimensional.measurable
  have hq : X.dice=sweep a := rfl
  refine ⟨hp,Measure.ext_of_charFun ?_⟩
  have ht : b*E=E*a := relatesG X z h
  have hi : E*Eᵀ=1 := upside _
  have hf (t : Air f G) : ∃ u,weep X z u=t := by
    refine ⟨WithLp.toLp 2 (Eᵀ *ᵥ t.ofLp),?_⟩
    unfold weep; rw [WithLp.ofLp_toLp,Matrix.mulVec_mulVec,hi,Matrix.one_mulVec,WithLp.toLp_ofLp]
  funext u; obtain ⟨u,rfl⟩ := hf u
  have hx w (v : Air f G) : inner ℝ (weep X z w) (weep X z v)=inner ℝ w v := by
    simp_rw [PiLp.inner_apply,RCLike.inner_apply, starRingEnd_apply,star_trivial]; exact shade_pair ..
  have he : charFun (X.dice.map (weep X z)) (weep X z u)=charFun X.dice u := by rw [charFun_apply, integral_map hp.aemeasurable (by fun_prop)]; simp_rw [hx, ← charFun_apply]
  rw [he,hq]; change charFun (multivariateGaussian 0 a) u = charFun (multivariateGaussian 0 b) _
  unfold weep; rw [charFun_multivariateGaussian (show _ from hA.posSemidef),charFun_multivariateGaussian (show _ from hA'.posSemidef)];
  dsimp only [WithLp.ofLp_toLp]; rw [Matrix.mulVec_mulVec,ht,← Matrix.mulVec_mulVec,shade_pair]; simp; rfl
end YM.ConnectedActivityE6.Hues
