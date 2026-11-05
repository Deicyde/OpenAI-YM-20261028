import Mathlib
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Receipts
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.ITERATION_NO_LOSS.Radius
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.Overlay
import YM.Next.MAXWELL.Det
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Progress.STATIONARY_SCENES.Frames
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Ward
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Collar
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle

/-! # Order and currencies literally compatible on the physical endpoint germ -/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology  Set WardBin.Lies
  YM.Pressure FreeResolvent Affine TestD Window Mark Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {H : Tube G S} {r s δ γ η Q g K x : ℝ} {M N : ℕ → ℝ}
  {q n : ℕ} {A : Stores S} {T : Forest S.ratio} {k : S.Choices} {V : Config G c} {ι : Type*} [Fintype ι]
  {F F' : Forest S.ratio → Config G c → Matrix ι ι ℝ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma Lie_congr {F H : Config G c → E} (h : SelectedOrderedKernels.over F V =ᶠ[𝓝 0] SelectedOrderedKernels.over H V)
    (hf : WardBin.Lies.Germ n F V) : WardBin.Lies.Germ n H V ∧ ∀ l : List (Directions G c), l.length ≤ n → leftDerivs F l V = leftDerivs H l V := by
  have hF := smooth_over.mpr hf
  have hH := hF.congr_of_eventuallyEq h.symm
  refine ⟨smooth_over.mp hH,fun l hl => ?_⟩
  rw [← List.ofFn_get l,expand_over _ (smooth_of_le hF hl),expand_over _ (smooth_of_le hH hl)]
  simp_rw [fun j => (h.iteratedFDeriv ℝ j).eq_of_nhds]

variable {D : Cost (Site c)} {a : ι → Site c} {b : Edge (Site c) → Site c} {F₁ F₂ : Config G c → Matrix ι ι ℝ}

lemma Book.congr (h : SelectedOrderedKernels.over F₁ V =ᶠ[𝓝 0] SelectedOrderedKernels.over F₂ V) (he : Book D a a b q δ γ M F₁ V) : Book D a a b q δ γ M F₂ V := by
  refine ⟨(Lie_congr h he.smooth).1,he.nonneg, fun j z hj => ?_⟩; rw [ordered,← (Lie_congr h he.smooth).2 _ (by simpa)]; exact he.bill j z hj
lemma ChangedBook.congr {v : Site c} (h : SelectedOrderedKernels.over F₁ V =ᶠ[𝓝 0] SelectedOrderedKernels.over F₂ V) (he : ChangedBook D a a b q δ η γ v M F₁ V) :
    ChangedBook D a a b q δ η γ v M F₂ V := by
  refine ⟨(Lie_congr h he.smooth).1,he.nonneg, fun j z hj => ?_⟩; rw [ordered,← (Lie_congr h he.smooth).2 _ (by simpa)]; exact he.hit j z hj

lemma NoHole.Paid.congr (h : ∀ T, SelectedOrderedKernels.over (F T) V =ᶠ[𝓝 0] SelectedOrderedKernels.over (F' T) V) (hh : NoHole.Paid S a q δ η γ M N F V) : NoHole.Paid S a q δ η γ M N F' V :=
  ⟨fun T => (hh.base T).congr (h T),fun T U v he => (hh.variation T U v he).congr (F₁:=F U-F T) ((h U).sub (h T))⟩

lemma NoHole.Receipt.congr (h : ∀ T, SelectedOrderedKernels.over (F T) V =ᶠ[𝓝 0] SelectedOrderedKernels.over (F' T) V) (he : NoHole.Receipt S a q s Q M N F V) :
    NoHole.Receipt S a q s Q M N F' V := by
  have h₁ T l hl := (Lie_congr (h T) (he.paid.base T).smooth).2 l hl
  have h₂ T j (hj : j ≤ q) (z : Pins G c j) : ordered (F' T) V z = ordered (F T) V z := (h₁ T _ (by rw [List.length_ofFn]; exact hj)).symm
  constructor
  · exact he.rate
  · exact he.paid.congr h
  · intro T U v hv j hj z
    simp_rw [h₂ _ j hj z]; exact he.tagBill _ _ _ hv j hj z
  · intro T x j hj W hW; simp_rw [h₂ T j hj]; exact he.star T x j hj W hW
  · intro T U v hv j hj; simp_rw [fun t => h₂ t j hj]; exact he.tagStar T U v hv j hj
  · intro T l hl; rw [← h₁ T l hl]; exact he.fields T l hl
  intro T U v hv l hl; rw [← h₁ U l hl, ← h₁ T l hl]; exact he.tagDirections T U v hv l hl

namespace Selected

end Selected
end YM.SelectedOrderedKernels
