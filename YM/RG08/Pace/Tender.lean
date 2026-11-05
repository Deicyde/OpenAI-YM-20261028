import YM.RG08.Ballast.Pianist
import YM.Next.STATIONARY.Loops.HessianMatch

/-! # Quantifying the prescribed kinetic read
   Zero momentum in cover. No discretization error, same probe & roots
   as Stationary.LeadingRay. Stipulable pre-block costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary
open scoped Topology ContDiff Matrix
variable {α : Type} {w τ C A B : ℝ} {G : Gauge} {r n : ℕ} {m : Side}

abbrev Pot (G : Gauge) (r : ℕ) := Shale (Loc G 1) r

def probeK (i : G.ColorIndex) (F : Pot G 2) := alphaPay i (gallery F)
private def across (p : Momentum) : Space 1 := p ∘ Prod.snd
private lemma firmAcross {F : Space 1 → ℂ} (h : Firm w A F) : Firm w A (F ∘ across) := by
  apply h.comp across _ h.width_pos (fun p hp i=> hp i.2) (fun p x=> ⟨x ∘ Prod.snd,rfl⟩)
  rw [differentiable_pi]; intro i; exact differentiable_apply i.2

lemma kProbe_quote (G : Gauge) (w : ℝ) (hw : 0<w) :
    ∃ C≥(0:ℝ), ∀ {A}, ∀ (F : Pot G 2), Glow F w A → ∀ i, |probeK i F| ≤ C*A := by
  let v := (step (0:Axis) : Track)
  let Z := ‖axes v‖^2
  let C := (1/(w/2))/(w/4)*Z
  refine ⟨C,by unfold C Z; positivity,fun {A} F h i=>?_⟩
  let f := gallery F ![i,i] ![coord 1,coord 1] ∘ across
  have Hf := firmAcross (gallery_funds h hw ![i,i] ![coord 1,coord 1])
  let L := axisCL Axis; let u := fun _ : Fin 2 => L v
  have hf : AnalyticAt ℂ f 0 := Hf.analytic (Hf.in_range (by simp)); have he : AnalyticAt ℝ f 0 := ((hf.contDiffAt (n:=ω)).restrict_scalars ℝ).analyticAt
  have hp : leapTip (gallery F) v 1 ![i,i]= ((2:ℝ)⁻¹) • iteratedFDeriv ℂ 2 f 0 u := by
    change speedy (f ∘ L) 2 v=_; unfold speedy Tensor.diagonal Tensor.coeff
    rw [_root_.smul_apply,wired L (by rw [map_zero]; exact he),map_zero, ← (hf.contDiffAt (n:=(↑(2:ℕ):WithTop ℕ∞))).restrictScalars_iteratedFDeriv (𝕜:=ℝ)]
    norm_num [Nat.factorial]; rfl
  unfold probeK alphaPay; rw [hp]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_im,zero_mul, Complex.ofReal_re,sub_zero]
  rw [← mul_assoc,mul_inv_cancel₀ (by norm_num),one_mul]
  apply le_trans (Complex.abs_re_le_norm _) ((ContinuousMultilinearMap.le_opNorm _ _).trans ?_)
  apply (mul_le_mul_of_nonneg_right (shoot Hf) (prod_nonneg fun _ _=> norm_nonneg _)).trans_eq
  rw [show ∏ i : Fin 2, ‖u i‖=Z by simp [Z,u]; rfl]; unfold C; ring

private lemma firmUnitSum (w : ℝ) (hw : 0≤w) {F : Shift α → ℝ} [Fintype α] [DecidableEq α] (h : Width w C F) (p : Phase α) (hp : star p=p) :
    Summable (fun i => mode p i • (F i:ℂ)) := by
  apply Summable.of_norm; have hh := (h.summable hw).norm; simpa only [norm_smul,mode_real p _ hp,one_mul,Complex.norm_real]

lemma lens_minus {F H : Pot G 2} (hf : Glow F w A) (hp : Glow H τ B) (hw : 0<w) (hv : 0<τ) (a : Axis)
    (i : G.ColorIndex) : pressLens (gallery (F-H)) ![i,i] a a=
      pressLens (gallery F) ![i,i] a a-pressLens (gallery H) ![i,i] a a := by
  let z (j : Fin 2) : Loc G 1 := (![coord a,coord a] j, ![i,i] j)
  funext p
  let P := axes (roads p)
  have he : star P=P := axes_real _
  have hQ := (firmUnitSum w hw.le (finger_charge hf z) P he).tsum_sub (firmUnitSum τ hv.le (finger_charge hp z) P he)
  simp only [pressLens,gallery,aria,Laurent.read,Pi.sub_apply,Complex.ofReal_sub,smul_sub]; exact hQ
lemma lens_charge (b : ℝ) (F : Pot G 2) (a : Axis)
    (i : G.ColorIndex) : pressLens (gallery (b • F)) ![i,i] a a=b • pressLens (gallery F) ![i,i] a a := by
  funext p; unfold pressLens gallery aria Laurent.read
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  simp_rw [mul_left_comm _ (b:ℂ)]; exact tsum_mul_left
lemma probe_diff (i : G.ColorIndex) {F H : Pot G 2} (hf : Glow F w A) (hp : Glow H τ B) (hw : 0<w) (hv : 0<τ) :
    probeK i (F-H)=probeK i F-probeK i H := by
  have hh := priceL (fun i j => gallery_funds hf hw i j) ![i,i] 1 1
  have hx := priceL (fun i j => gallery_funds hp hv i j) ![i,i] 1 1
  unfold probeK alphaPay leapTip speedy; rw [lens_minus hf hp hw hv]; unfold Tensor.diagonal Tensor.coeff; rw [iteratedFDeriv_sub_apply hh.contDiffAt hx.contDiffAt,smul_sub,_root_.sub_apply,Complex.sub_re,mul_sub]
lemma probe_scale (i : G.ColorIndex) (b : ℝ) {F : Pot G 2} (hf : Glow F w A) (hw : 0<w) :
    probeK i (b • F)=b*probeK i F := by
  have hh := priceL (fun i j => gallery_funds hf hw i j) ![i,i] 1 1
  unfold probeK alphaPay leapTip speedy; rw [lens_charge]; unfold Tensor.coeff Tensor.diagonal; rw [iteratedFDeriv_const_smul_apply hh.contDiffAt]; simp [Complex.real_smul]
end YM.RG08
