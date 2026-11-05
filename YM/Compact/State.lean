import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Support
import YM.Hilbert.Kolmogorov




/-!
# C(X) representation to actual compact spectral measure

No separability assumption on H. Riesz positive Λ's owely in refl-positive
character steps. std Lean linear second slot. Quotient later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Rep
open MeasureTheory Measure Filter Set Function Complex CompactlySupported
open scoped Topology NNReal ENNReal Real InnerProductSpace
variable {X : Type*} [TopologicalSpace X] {H : Hilbert}

/-- Integrands on character space. -/
abbrev CC (X : Type*) [TopologicalSpace X] := C(X,ℂ)
abbrev CR (X : Type*) [TopologicalSpace X] := C(X,ℝ)

variable (A : CC X →⋆ₐ[ℂ] H.Op)

def insert : CR X →ₗ[ℝ] CC X where
  toFun f := ⟨fun x => (f x:ℂ),continuous_ofReal.comp f.continuous⟩
  map_add' f g := by apply ContinuousMap.ext; intro x; exact ofReal_add ..
  map_smul' c f := by apply ContinuousMap.ext; intro x; exact ofReal_mul ..

@[simp] lemma insertion (f : CR X) x : insert f x=(f x:ℂ) := rfl

/-- Positive vector state. (No unit assumption on v.) -/
def Λ (v : H) : CC X →ₗ[ℂ] ℂ :=
  (innerSL ℂ v).toLinearMap.comp (((ContinuousLinearMap.apply ℂ H.space v).toLinearMap).comp A.toAlgHom.toLinearMap)
lemma atState (v : H) f : Λ A v f=inner ℂ v (A f v) := rfl

def Λ₀ (v : H) : CR X →ₗ[ℝ] ℝ :=
  reCLM.toLinearMap.comp (((Λ A v).restrictScalars ℝ).comp insert)

lemma real (v : H) (u : CR X) : Λ A v (insert u) = ↑(Λ₀ A v u) := by
  have h : (A (insert u)).adjoint=A (insert u) := by
    change star _=_
    rw [← map_star, show star (insert u)=insert u from ContinuousMap.ext fun x => by
      change star (↑(u x):ℂ) = _
      simp]
  have he : starRingEnd ℂ (Λ A v (insert u))=Λ A v (insert u) := by
    rw [atState,inner_conj_symm,← ContinuousLinearMap.adjoint_inner_right,h]
  have hf := congr_arg im he
  simp only [conj_im] at hf
  apply Complex.ext; exact rfl
  rw [ofReal_im]; linarith

lemma squares (v : H) (u f : CC X) : Λ A v (star u*f)=inner ℂ (A u v) (A f v) := by
  rw [atState,map_mul,map_star]
  exact ContinuousLinearMap.adjoint_inner_right (A u) v (A f v)

theorem positive (v : H) (u : CR X) (hw : ∀ x, 0 ≤ u x) : 0 ≤ Λ₀ A v u := by
  let y : CR X := ⟨fun i => √(u i), Real.continuous_sqrt.comp u.continuous⟩
  let f := insert y
  have he : insert u=star f*f := by
    apply ContinuousMap.ext; intro i
    change ↑(u i)=star (↑(√(u i)):ℂ)*(↑(√(u i)):ℂ)
    rw [show star _= (↑(√(u i)):ℂ) from conj_ofReal _,← sq,← ofReal_pow,Real.sq_sqrt (hw i)]
  change 0 ≤ (Λ A v (insert u)).re
  rw [he,squares]; exact inner_self_nonneg (𝕜 := ℂ) (x := (A f v))

variable [MeasurableSpace X] [BorelSpace X] [T2Space X] [CompactSpace X]
omit [MeasurableSpace X] [BorelSpace X] [T2Space X] [CompactSpace X] in
def Lambda (v : H) : C_c(X,ℝ) →ₚ[ℝ] ℝ where
  toFun f := Λ₀ A v f.toContinuousMap
  map_add' x y := map_add (Λ₀ A v) ..
  map_smul' c x := map_smul (Λ₀ A v) ..
  monotone' x y h := by
    rw [← sub_nonneg,← map_sub]
    exact positive A v _ (fun i => sub_nonneg.mpr (h i))

def sees (v : H) : Measure X := RealRMK.rieszMeasure (Lambda A v)
instance fin (v : H) : IsFiniteMeasure (sees A v) := by unfold sees; infer_instance
instance regal (v : H) : Regular (sees A v) := by unfold sees; infer_instance

theorem pairings (v : H) (f : CC X) : (∫ x, f x ∂sees A v) = inner ℂ v (A f v) := by
  let μ := sees A v
  have he (y : CR X) : (∫ x, (insert y) x ∂μ)=Λ A v (insert y) := by
    rw [real]; simp_rw [insertion]; rw [integral_complex_ofReal]
    let j : C_c(X,ℝ) := { toContinuousMap := y, hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
    exact congrArg (fun p : ℝ => (p:ℂ)) (RealRMK.integral_rieszMeasure (Lambda A v) j)
  let hr : CR X := ⟨fun i => (f i).re,continuous_re.comp f.continuous⟩
  let hi : CR X := ⟨fun i => (f i).im,continuous_im.comp f.continuous⟩
  have ht : insert hr + I • insert hi=f := by
    apply ContinuousMap.ext; intro i; rw [ContinuousMap.add_apply,ContinuousMap.smul_apply]
    simp only [smul_eq_mul,insertion]; rw [mul_comm I]
    exact re_add_im _
  have hI (f : CC X) : Integrable ⇑f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← atState, ← ht,map_add,map_smul]
  simp_rw [ContinuousMap.add_apply,ContinuousMap.smul_apply]
  rw [integral_add (hI _) (show Integrable (fun i => I • insert hi i) μ from (hI (insert hi)).smul I), integral_smul,he,he]

lemma size (v : H) : (sees A v).real univ = ‖v‖^2 := by
  have he := pairings A v 1
  rw [map_one] at he
  simpa [show (1:H.Op) v=v from rfl,← Complex.ofReal_pow] using congr_arg re he -- re
end YM.Spectral.Rep
