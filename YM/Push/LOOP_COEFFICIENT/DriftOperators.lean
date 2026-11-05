import YM.Push.LOOP_COEFFICIENT.BondGradient
import YM.Push.LOOP_COEFFICIENT.DriftReal

/-!
# Evaluate the drift equation on the true rooted augmented backgrounds
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice RG Wilson Precision Bloch Exterior Tree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealTrace
variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
lemma observe_diff {R : (m → ℝ) → RealTrace m k} (h : ∀ v,ContDiffAt ℝ ω (fun b => R b v) 0) : ContDiffAt ℝ ω R 0 := by
  let P (i : m) := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : m => ℝ) i
  suffices H : ContDiffAt ℝ ω (fun b => ∑ i, (P i).smulRight (R b (Pi.single i (1:ℝ)))) 0 by
    convert! H using 1; funext b; apply ContinuousLinearMap.ext; intro w
    rw [show w = ∑ i : m, w i • Pi.single i (1:ℝ) from ?_, map_sum]
    · simp [P,Pi.single_apply]
    ext i; simp [Pi.single_apply, mul_ite]
  apply ContDiffAt.sum; intro i _
  let L : Matrix k k ℝ →L[ℝ] RealTrace m k := ContinuousLinearMap.smulRightL ℝ (m → ℝ) (Matrix k k ℝ) (P i)
  exact L.contDiff.contDiffAt.comp (f:=fun b => R b (Pi.single i 1)) 0 (h _)

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {W : PathData G} {A : Matrix (Body 1 f) (Body 1 c) ℝ} {t : S.Choices}

def background (G : Gauge) (S : StepData c f) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) := vary 1 (graft G S A b).2

def onVector (p : Clip) (W : PathData G) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) := vector p W t (vary 1 b) (background G S A b)

def onBase (p : Clip) (W : PathData G) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) := baseVector p W t (vary 1 b) (background G S A b)

def onAcc (G : Gauge) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) (b : Loops.Links G c) : RealTrace (BondKey G c) (JointKey G c f) := LinearMap.toContinuousLinearMap {
    toFun := acceleration (Zmap t) (background G S A b)
    map_add' x y := by simp only [acceleration,twist,Pi.add_apply,add_smul,Finset.sum_add_distrib]
    map_smul' x y := by simp only [acceleration,twist,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_smul,Finset.smul_sum] }

def amplify (B : (m → ℝ) → Matrix k k ℝ) (R : (m → ℝ) → RealTrace m k) (x : m → ℝ) : RealTrace m k := (matrixMulCLM k k k (B x)).comp (R x)

def observed (p : Clip) (W : PathData G) (t : S.Choices) (A : Matrix (Body 1 f) (Body 1 c) ℝ) := amplify (fun b => (onBase p W t A b)⁻¹) (onAcc G t A)

lemma observed_value (v b) : Yresp p W t (vary 1 b) (background G S A b) v = (observed p W t A b v).trace := rfl

@[simp] lemma background_zero : background G S A 0 = 1 := by simp [background]
lemma positions_background (v) : positions (background G S A v) = vary 1 (liftMatrix G A *ᵥ v) := by rw [background,show positions _ = _ from positions_graph (graft G S A v),graft, project_graph]

lemma background_diff {x : Loops.Links G c} : MatDiffAt (background G S A) x := (matDiffAt_const _).vary (graft G S A).contDiff.contDiffAt.snd
lemma onVector_diff (h : S.patch.Branches S.kernel G) {σ C Λ : ℝ} (hw : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (onVector p W t A) 0 := smooth_vector h hw t background_zero background_diff vary_diff
lemma onBase_diff (h : S.patch.Branches S.kernel G) {σ C Λ : ℝ} (hw : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (onBase p W t A) 0 := smooth_base h hw t background_zero background_diff vary_diff
private lemma acc_jet_diff (h : S.patch.Branches S.kernel G) : ContDiffAt ℝ ω (fun z : Loops.Links G c × Loops.Dual G c f => localize (Zmap t) (background G S A z.1) z.2) 0 := by
  let X := Loops.Links G c × Loops.Dual G c f
  have hu := background_diff (x:= (0:Loops.Links G c)) (S:=S) (A:=A)
  have hz := Zmap_diff h t (U:=background G S A) background_zero hu
  have he := (hu.comp (f:= Prod.fst) (x:=(0:X)) contDiffAt_fst).vary contDiffAt_snd
  exact (hz.comp (f:=Prod.fst) (x:=(0:X)) contDiffAt_fst).displacement
      (Zmap_diff h t (U:= fun z : X => vary (background G S A z.1) z.2) (x:=0) (by simp [X]) he) (by simp [X])

lemma onAcc_diff (h : S.patch.Branches S.kernel G) : ContDiffAt ℝ ω (onAcc G t A) 0 := by
  have hf : ContDiffAt ℝ ω (fun z : Loops.Links G c × Loops.Dual G c f => localize (Zmap t) (background G S A z.1) z.2) 0 := acc_jet_diff h
  apply observe_diff; intro w
  change ContDiffAt ℝ ω (fun b => ∑ i, w i • bilinearAt (fun z => localize (Zmap t) (background G S A b) z i) 0) 0
  apply ContDiffAt.sum; intro i _; refine ContDiffAt.const_smul _ ?_
  have hu := bilinearAt_diff (f:=fun b z => localize (Zmap t) (background G S A b) z i) (x:=0) (y:=0) (contDiffAt_pi.mp hf i)
  exact hu.comp (f:=fun b => (b,0)) (0:Loops.Links G c) (contDiffAt_id.prodMk contDiffAt_const)

lemma amplify_diff {B : (m → ℝ) → Matrix k k ℝ} {R : (m → ℝ) → RealTrace m k} (hb : ContDiffAt ℝ ω B 0) (hr : ContDiffAt ℝ ω R 0) :
    ContDiffAt ℝ ω (amplify B R) 0 := observe_diff fun w => smooth_mul hb (hr.clm_apply (g:=fun _ => w) contDiffAt_const)

variable (t) {F : Forest S.ratio} {ρ : fieldDir G c 1 → AxisChart G F} {P : ChartRatio G}
variable (h : Admission F ρ p W A P)
include h
lemma onBase_unit : IsUnit (onBase p W t A 0) := by
  obtain ⟨_,_,_,hw⟩ := h.paths
  rw [onBase,background_zero,vary_zero,← vector_flat h.branches hw]; exact h.invert_vector t
lemma observed_diff : ContDiffAt ℝ ω (observed p W t A) 0 := by
  obtain ⟨_,_,_,hw⟩ := h.paths
  exact amplify_diff ((inv_contDiffAt _ ((isUnit_iff_isUnit_det _).mp (onBase_unit t h))).comp 0 (onBase_diff h.branches hw)) (onAcc_diff h.branches)
lemma observed_ward : respCoeff (observed p W t A) * R_g (1:Config G c) = 0 := by
  apply pairing_ext (Y:=0); intro x y
  rw [← Matrix.mulVec_mulVec,response_pair,← response_value (observed_diff t h), Matrix.zero_mulVec, dotProduct_zero]
  exact response_prepared h t y x

lemma observed_drift (K : Matrix (Body 1 c) (Body 1 c) ℝ) (hA : mean S * A = 1 - S.kernel.penalty⁻¹ • K) :
    let L := -liftMatrix G K; let R := observed p W t A
    bilinearAt (fun b => Real.log (onVector p W t A b).det) 0 = bilinearAt (fun b => Real.log (onBase p W t A b).det) 0 +
      (L.transpose * respCoeff R + (respCoeff R).transpose * L - L.transpose * accCoeff R * L) := by
  obtain ⟨_,_,_,hw⟩ := h.paths
  dsimp only; rw [← (JZ_leading t h.branches K hA).2]
  have he := onBase_diff (t:=t) (A:=A) h.branches hw
  refine drift_equation (observed_diff t h) (JZ_diff t h.branches) (JZ_leading t h.branches K hA).1 (fun w => ?_) ?_ he (onBase_unit t h)
  · have ht := response_zero (t:=t) h.branches hw h.simple w
    simpa only [← observed_value,background_zero,vary_zero,response,Prod.fst_zero,Prod.snd_zero] using ht
  have hi := ((isUnit_iff_isUnit_det _).mp (onBase_unit t h)).ne_zero
  have hv := (beam_near h.branches t)
  have hB := background_diff (x:= (0:Loops.Links G c)) |>.continuousAt (v:=background G S A)
  rw [ContinuousAt,background_zero] at hB
  filter_upwards [(det_contDiff.contDiffAt.comp 0 he).continuousAt.eventually_ne hi,hB.eventually hv] with x hI hx
  change vector _ _ _ _ _ = _
  rw [vector_eq hw t _ _ hx.bonds,← show onBase p W t A x = _ from rfl]
  change onBase p W t A x + acceleration _ _ _ = onBase p W t A x * (1 + (onBase p W t A x)⁻¹ * acceleration _ _ _)
  rw [mul_add,mul_one,← mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hI),one_mul]; rfl
end YM.Push.Loops
