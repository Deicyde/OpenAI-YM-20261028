import YM.Pert.Lattice.Action
import YM.Push.LOOP_COEFFICIENT.Chain
import YM.Push.LOOP_COEFFICIENT.LogDet
import YM.Push.LOOP_COEFFICIENT.Tangent
/-! Local site FP derivative on root-fixed tangent parameters, no global constant ghost. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.Pert.Orb
open Lattice Filter Matrix Push.Loops
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
abbrev Parameter (G : Gauge) (n : Side) := ↥(Orb.Zero G n)

def siteEval (x : Site n) : Parameter G n →ₗ[ℝ] G.Color := LinearMap.comp (LinearMap.proj (R:=ℝ) x) (Orb.Zero G n).subtype
private def rawSpace (G : Gauge) (n : Side) := Orb.Links n → G.Color
def balance (G : Gauge) (n : Side) : (Orb.Links n → G.Color) →ₗ[ℝ] Potential G n :=
  LinearMap.codRestrict (LinkP G n)
    (LinearMap.pi (fun l => (1/2:ℝ) • LinearMap.proj (R:=ℝ) l - (1/2:ℝ) • LinearMap.proj (image l)))
    (fun a l => by simpa using (show (1/2:ℝ) • a (image l) - (1/2:ℝ) • a (image (image l)) = -((1/2:ℝ) • a l - (1/2:ℝ) • a (image l)) by rw [image_image]; abel))
lemma balance_same (a : Potential G n) : balance G n a.val = a := Subtype.ext (funext (fun l => by
  change (1/2:ℝ) • a.val l - (1/2:ℝ) • a.val (image l) = _
  rw [a.property l,smul_neg,sub_neg_eq_add,← add_smul]; norm_num))

def turn (a : Potential G n) (z : Parameter G n) (l : Orb.Links n) : G.El :=
  G.lieExp (z.val l.1) * positiveLinks a l * (G.lieExp (z.val (l.1+step l.2)))⁻¹
lemma turn_zero (l : Orb.Links n) : turn (0:Potential G n) (0:Parameter G n) l=1 := by simp [turn]
lemma turn_smooth (l : Orb.Links n) : ContDiff ℝ ω (fun p : Potential G n × Parameter G n => G.mat (turn p.1 p.2 l)) := by
  simp only [turn,G.mat_mul]
  refine (((G.exp_jet.comp (f:=fun p : Potential G n × Parameter G n => p.2.val l.1) ?_).mul ((pos_mDiff l).comp contDiff_fst)).mul ?_)
  · exact (siteEval l.1).toContinuousLinearMap.contDiff.comp contDiff_snd
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (G.exp_jet.comp (f:=fun p : Potential G n × Parameter G n => p.2.val (l.1+step l.2)) ((siteEval _).toContinuousLinearMap.contDiff.comp contDiff_snd))

def roughLog (a : Potential G n) (z : Parameter G n) : Orb.Links n → G.Color := fun l => G.plog (G.mat (turn a z l))
def shiftedLog (a : Potential G n) (z : Parameter G n) : Potential G n := balance G n (roughLog a z)
lemma rough_smooth : ContDiffAt ℝ ω (fun p : Potential G n × Parameter G n => roughLog p.1 p.2) (0,0) := by
  apply contDiffAt_pi.mpr; intro (l : Orb.Links n)
  have ht : G.mat (turn (G:=G) 0 0 l) = 1 := by rw [turn_zero,G.mat_one]
  have hh := (show ContDiffAt ℝ ω G.plog (G.mat (turn 0 0 l)) from ht.symm ▸ G.plog_diff).comp (0,0) (turn_smooth (G:=G) l).contDiffAt
  exact hh
lemma shift_smooth : ContDiffAt ℝ ω (fun p : Potential G n × Parameter G n => shiftedLog p.1 p.2) (0,0) :=
  (balance G n).toContinuousLinearMap.contDiff.contDiffAt.comp (0,0) rough_smooth

def FPField (a : Potential G n) (z : Parameter G n) : ↥(Mean G n) := dLin (shiftedLog a z)
lemma field_smooth : ContDiffAt ℝ ω (fun p : Potential G n × Parameter G n => FPField p.1 p.2) (0,0) :=
  ((dLin (G:=G) (n:=n)).toContinuousLinearMap).contDiff.contDiffAt.comp (0,0) (shift_smooth (G:=G) (n:=n))

def FPDeriv (a : Potential G n) : Parameter G n →L[ℝ] ↥(Mean G n) := fderiv ℝ (FPField a) 0
def resetFP (a : Potential G n) : Parameter G n →L[ℝ] Parameter G n := (bridgeEquiv G n).toContinuousLinearEquiv.symm.toContinuousLinearMap.comp (FPDeriv a)
lemma FP_smooth : ContDiffAt ℝ ω (FPDeriv (G:=G) (n:=n)) 0 := by
  unfold FPDeriv; exact ContDiffAt.fderiv (f:=FPField) (g:=fun _ => 0) field_smooth contDiffAt_const (by simp)
lemma turn_diff (z : Parameter G n) (l : Orb.Links n) : HasDerivAt (fun r : ℝ => G.mat (turn 0 (r • z) l)) (G.colorMat (grad z.val l)) 0 := by
  simp only [turn,pos_flat,mul_one,G.mat_mul]
  have ht := (line_diff (z.val l.1)).mul (line_diff (z.val (l.1+step l.2))).star
  simp only [zero_smul,G.mat_lieExp_zero,G.mat_one,G.colorMat_skew,mul_one,one_mul,star_one] at ht
  rw [grad,map_sub,sub_eq_add_neg]; exact ht
lemma FPDeriv_flat : FPDeriv (G:=G) (n:=n) 0 = (bridge G n).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext; intro z
  have hr : HasDerivAt (fun r : ℝ => roughLog 0 (r • z)) (grad z.val) 0 := by
    apply hasDerivAt_pi.mpr; intro l
    have ht := turn_diff z l
    rw [← mul_one (G.colorMat _)] at ht
    have hd : HasDerivAt (fun r : ℝ => delta (turn 0 ((0:ℝ) • z) l) (turn 0 (r • z) l)) (grad z.val l) 0 := delta_rate (by simpa [turn_zero] using ht)
    simpa [turn_zero,delta,roughLog] using hd
  let D := (dLin (G:=G) (n:=n)).toContinuousLinearMap
  let B := (balance G n).toContinuousLinearMap
  have hb := (D.hasFDerivAt.comp_hasDerivAt (l:=fun u => D u) _ (B.hasFDerivAt.comp_hasDerivAt _ hr))
  have he : B (grad z.val) = gZ z := by
    change balance G n (grad z.val) = _; exact balance_same (gZ z)
  rw [he] at hb
  have H := (field_smooth.comp (x:=0) (show ContDiffAt ℝ ω (fun z : Parameter G n => ((0:Potential G n),z)) 0 from contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp) |>.hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => r • z) z 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const z
  nth_rw 2 [show (0 : Parameter G n) = (0:ℝ) • z by simp] at H
  have ht := H.comp_hasDerivAt 0 hline
  change HasDerivAt (fun r : ℝ => FPField 0 (r • z)) (FPDeriv 0 z) 0 at ht
  exact ht.unique (show HasDerivAt (fun r : ℝ => FPField 0 (r • z)) (dLin (gZ z)) 0 from hb)
lemma reset_id : resetFP (G:=G) (n:=n) 0= ContinuousLinearMap.id ℝ _ := by rw [resetFP, FPDeriv_flat]; ext1 x; exact (bridgeEquiv G n).symm_apply_apply _
lemma reset_smooth : ContDiffAt ℝ ω (resetFP (G:=G) (n:=n)) 0 := by
  unfold resetFP
  exact contDiffAt_const.clm_comp FP_smooth
abbrev FPIndex (G : Gauge) (n : Side) := Fin (Module.finrank ℝ (Parameter G n))
def FPmatrix (a : Potential G n) : Matrix (FPIndex G n) (FPIndex G n) ℝ :=
  of (fun i j => (Module.finBasis ℝ (Parameter G n)).coord i (resetFP a (Module.finBasis ℝ (Parameter G n) j)))
lemma FPmatrix_smooth : ContDiffAt ℝ ω (FPmatrix (G:=G) (n:=n)) 0 := by
  unfold FPmatrix
  refine matrix_diff fun i j => ?_
  change ContDiffAt ℝ ω (fun (a : Potential G n) => (Module.finBasis ℝ (Parameter G n)).coord i (resetFP a (Module.finBasis ℝ (Parameter G n) j))) 0
  exact ((Module.finBasis ℝ (Parameter G n)).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun a => resetFP a (Module.finBasis ℝ (Parameter G n) j)) _ (ContDiffAt.clm_apply reset_smooth contDiffAt_const)
lemma FPmatrix_flat : FPmatrix (0:Potential G n) = 1 := by
  ext i j
  change (Module.finBasis ℝ (Parameter G n)).coord i (resetFP 0 (Module.finBasis ℝ (Parameter G n) j)) = (1:Matrix _ _ ℝ) i j
  rw [reset_id,Matrix.one_apply,ContinuousLinearMap.id_apply,Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply]; simp [eq_comm]
/-- FP density normalized by its flat value; input Lie algebra directions are unscaled. -/
def FP (a : Potential G n) : ℝ := (FPmatrix a).det
lemma FP_diff : ContDiffAt ℝ ω (FP (G:=G) (n:=n)) 0 := det_contDiff.contDiffAt.comp (f:=FPmatrix) _ FPmatrix_smooth
@[simp] lemma FP_flat : FP (0:Potential G n)=1 := by rw [FP,FPmatrix_flat, det_one]
lemma FP_density : FP (G:=G) (n:=n) =ᶠ[𝓝 0] (fun a => |(FPmatrix a).det|) := ((FP_diff (G:=G) (n:=n)).continuousAt.eventually_mem (Ioi_mem_nhds (by simp : (0:ℝ)<FP (0:Potential G n)))).mono (fun a h => (abs_of_pos h).symm)
end YM.Pert.Orb
