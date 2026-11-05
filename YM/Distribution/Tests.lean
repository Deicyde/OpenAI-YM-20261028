import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Joint tempered testing & signs

Use ℂ-linear tempered distributions as CLMs. Test `f`, no conj, on full
positions and on relatives. Lebesgue. Signs/2π constants are PROVED for
radian coordinate pairing. Generic over position vector spaces, instantiate
E4 and Points with indicated volumes. (If using weak/pt topology, use the
Mathlib Pt alias with same underlying CLMs; we don't claim convergence in
strong dual topology.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open MeasureTheory Measure Filter Complex Function
open scoped Topology BigOperators FourierTransform InnerProductSpace

abbrev Probe (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] := SchwartzMap X ℂ
abbrev Distn (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] := Probe X →L[ℂ] ℂ

namespace Probe
variable {V X : Type*} [NormedAddCommGroup V]
section
variable [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Linear and used on the **test argument**. -/
def along (e : V ≃L[ℝ] X) : Probe X →L[ℂ] Probe V := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
@[simp] theorem along_at (e : V ≃L[ℝ] X) (x : Probe X) (v) : along e x v = x (e v) := rfl
@[simp] theorem along_inv (e : V ≃L[ℝ] X) (x : Probe X) : along e.symm (along e x)=x := by ext1; simp
@[simp] theorem along_for (e : V ≃L[ℝ] X) (x : Probe V) : along e (along e.symm x)=x := by ext1;simp

def ahead (u : V) : Probe V →L[ℂ] Probe V := SchwartzMap.compSubConstCLM ℂ u
@[simp] theorem ahead_at (u : V) (x : Probe V) (v) : ahead u x v = x (v-u) := rfl

def bar : Probe V →L[ℝ] Probe V := SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)
@[simp] theorem bar_at (x : Probe V) (v) : bar x v=star (x v) := rfl
@[simp] theorem bar_twice (x : Probe V) : bar (bar x)=x := by ext1; simp
@[simp] theorem bar_scal (x : Probe V) (a : ℂ) : bar (a • x)=star a • bar x := by ext1;simp
@[simp] theorem bar_along (x : Probe X) (e : V ≃L[ℝ] X) : bar (along e x)=along e (bar x) := by ext1;simp
@[simp] theorem bar_ahead (x : Probe V) (u : V) : bar (ahead u x)=ahead u (bar x) := by ext1; simp
end

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def q : ℝ := 2 * Real.pi
def pref (V : Type*) [AddCommGroup V] [Module ℝ V] := q ^ Module.finrank ℝ V
lemma qpos : 0<q := by unfold q; positivity
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma prepos : 0 < pref V := pow_pos qpos _

def collapse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 q⁻¹ (inv_ne_zero qpos.ne'))

def plane {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x k : V) :=
  Complex.exp (↑(inner ℝ x k) * I)

section
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
@[simp] lemma plane_norm (x k : V) : ‖plane x k‖=1 := by simp [plane]
@[simp] lemma plane_zero (x : V) : plane x 0=1 := by simp [plane]
lemma plane_dot (x k : V) : plane x k=plane k x := by rw [plane,plane,real_inner_comm]
lemma plane_inverse (x k : V) : plane x (-k)=star (plane x k) := by
  rw [plane,plane]; simp [← Complex.exp_conj]
lemma plane_add (x u k : V) : plane x (u+k)=plane x u * plane x k := by simp [plane,inner_add_right,add_mul,Complex.exp_add]
@[fun_prop] lemma plane_cont : Continuous (fun p : V × V => plane p.1 p.2) := by unfold plane;fun_prop
@[simp] lemma shrinking (x : V) : collapse x=q⁻¹ • x := rfl
@[simp] lemma expanding (x : V) : collapse.symm x=q • x := by
  apply collapse.injective; simp only [ContinuousLinearEquiv.apply_symm_apply,shrinking,smul_smul,inv_mul_cancel₀ qpos.ne',one_smul]
end

def hat : Probe V →L[ℂ] Probe V := (along collapse).comp (FourierTransform.fourierCLM ..)
def port : Probe V →L[ℂ] Probe V := (FourierTransform.fourierInvCLM ..).comp (along collapse.symm)

@[simp] theorem comes (f : Probe V) : port (hat f)=f := by
  change 𝓕⁻ (along collapse.symm (along collapse (𝓕 f))) = _
  rw [along_inv, FourierTransform.fourierInv_fourier_eq]
@[simp] theorem travels (f : Probe V) : hat (port f)=f := by
  change along collapse (𝓕 (𝓕⁻ (along collapse.symm f))) = _
  rw [FourierTransform.fourier_fourierInv_eq, along_for]

/-- Tests transform with signs as indicated. -/
theorem hat_eq (f : Probe V) (p : V) : hat f p = ∫ b, plane b (-p) * f b := by
  change (𝓕 (⇑f)) (collapse p) = _
  rw [Real.fourier_eq']
  simp only [plane,shrinking, inner_neg_right, real_inner_smul_right,smul_eq_mul]
  congr! 6
  field_simp [qpos.ne',Real.pi_ne_zero]
  rfl

theorem port_eq (f : Probe V) (x : V) : port f x = ((pref V)⁻¹:ℝ) • (∫ p, plane p x * f p) := by
  change ⇑(𝓕⁻ (along collapse.symm f) : Probe V) _ = _
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
  rw [pref,show _ • _ = _ from (Measure.integral_comp_smul_of_nonneg (hR := qpos.le) volume (fun p => plane p x * f p) q).symm]
  simp only [plane, along_at, expanding,real_inner_smul_left, q,smul_eq_mul]

lemma positiveFourier (f : Probe V) (x : V) : (∫ b, plane b x * hat f b) = pref V • f x := by
  conv_rhs => rw [← comes f]
  rw [port_eq,smul_smul,mul_inv_cancel₀ prepos.ne',one_smul]

end Probe
namespace Distn
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Distribution Fourier convention (test by same hat). -/
def fourier (F : Distn V) := F.comp Probe.hat
def inverse (F : Distn V) := F.comp Probe.port
@[simp] lemma fourier_at (F : Distn V) (f) : fourier F f=F (Probe.hat f) := rfl
@[simp] lemma inverse_at (F : Distn V) (f) : inverse F f=F (Probe.port f) := rfl
@[simp] theorem same (F : Distn V) : fourier (inverse F)=F := by ext1; simp
@[simp] theorem one (F : Distn V) : inverse (fourier F)=F := by ext1; simp
end Distn

end YM.Boundary
