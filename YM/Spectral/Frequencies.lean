import YM.Spectral.Projection
import YM.Distribution.Tests
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Tested support actually gives the projection answer

Spectrum criterion diagonal tests on dense range with signs/constants of E.
Don't conflate existence of the projections with the criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral
open MeasureTheory Measure Filter Set Function Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]

lemma picker (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (h : IsOpen s) : μ s=0 ↔
    ∀ f : Probe X, HasCompactSupport ⇑f → tsupport f ⊆ s → (∫ x, f x ∂μ)=0 := by
  constructor
  · intro hh f _ hf
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) (s := s) ?_ |>.symm.trans ?_
    · exact fun x hx => image_eq_zero_of_notMem_tsupport fun w => hx (hf w)
    simp [Measure.restrict_eq_zero.mpr hh]
  intro H
  suffices he : s ⊆ μ.supportᶜ from measure_mono_null he Measure.measure_compl_support
  intro x hx hμ
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (h.mem_nhds hx)
  let B : ContDiffBump x := ⟨r/4,r/2,by positivity,by linarith⟩
  let f : Probe X := (B.hasCompactSupport.comp_left (show Complex.ofReal 0=0 by norm_cast)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  have hb : ⇑f=Complex.ofReal ∘ B := rfl
  have ht : Function.support f = Function.support B := by rw [hb]; ext y; simp
  have hh := H f (hb ▸ B.hasCompactSupport.comp_left Complex.ofReal_zero) (by
    rw [tsupport,ht,← tsupport,B.tsupport_eq]; apply subset_trans _ hR
    exact Metric.closedBall_subset_ball (by change r/2<r; linarith))
  have hI : (∫ x, B x ∂μ)=0 := by
    apply Complex.ofReal_injective; rw [← integral_complex_ofReal, Complex.ofReal_zero]; exact hh
  have hp : 0 < ∫ x, B x ∂μ := (integral_pos_iff_support_of_nonneg (μ := μ) (f := B) (fun _ => B.nonneg)
    (B.continuous.integrable_of_hasCompactSupport B.hasCompactSupport)).2 ((Measure.mem_support_iff_forall x).1 hμ _ (by
      rw [B.support_eq]; exact Metric.ball_mem_nhds _ B.rOut_pos))
  linarith

lemma wave_integral (μ : Measure X) [IsFiniteMeasure μ] (f : Probe X) :
    (∫ x, charFun μ x * Probe.hat f x) = Probe.pref X • ∫ x, f x ∂μ := by
  simp_rw [charFun_apply, ← integral_mul_const]
  rw [integral_integral_swap]; swap
  · let F := fun p : X × X => plane p.2 p.1 * Probe.hat f p.1
    exact ((Probe.hat f).integrable.norm.comp_fst (ν := μ)).mono
      (show AEStronglyMeasurable F _ from (plane_cont.comp continuous_swap |>.mul
        ((Probe.hat f).continuous.comp continuous_fst)).aestronglyMeasurable)
      (show ∀ᵐ p ∂volume.prod μ, ‖F p‖ ≤ abs ‖Probe.hat f p.1‖ from ae_of_all _ fun _ => by simp [F])
  change (∫ y, (∫ x, plane y x * hat f x) ∂μ)=_
  have hf (y : X) : (∫ x, plane y x * hat f x) = pref X • f y := by
    simp_rw [plane_dot y]; rw [positiveFourier]
  simp_rw [hf]; rw [integral_smul]

variable {H : Hilbert}
namespace Orbit
variable (T : Orbit H X)

/-- P is the projection-valued momentum measure in THE radian convention.
Diagonal identity suffices, by polarization. -/
def Spectrum (P : PVM H X) : Prop := ∀ x : H, ∀ b : X,
    charFun (P.diagonal x) b = inner ℂ x (T.translation b x)

/-- Tested diagonal matrix elements. -/
def tests (C : Set X) (v : H) :=
  ∀ f : Probe X, HasCompactSupport ⇑f → tsupport f ⊆ Cᶜ →
    (∫ b, inner ℂ v (T.translation b v) * Probe.hat f b)=0

theorem suffices_tests (P : PVM H X) (h : T.Spectrum P) (s : Set X) (hs : IsClosed s) (v : H) :
    P.region sᶜ v=0 ↔ T.tests s v := by
  unfold tests
  unfold Spectrum at h
  simp_rw [← h, wave_integral,← P.null_pair hs.isOpen_compl.measurableSet, picker _ hs.isOpen_compl,
    smul_eq_zero_iff_right Probe.prepos.ne']

theorem carrier (P : PVM H X) (h : T.Spectrum P) (s : Set X) (hs : IsClosed s)
    (D : Set H) (hh : Dense D) : P.region sᶜ=0 ↔ ∀ x ∈ D, T.tests s x := by
  simp_rw [← suffices_tests T P h s hs]
  constructor
  · intro hp; simp [hp]
  intro hp
  ext1 x
  exact show x ∈ {x : H| P.region sᶜ x=0} from
    closure_minimal hp (isClosed_eq (P.region _).continuous continuous_const) (hh x)

end Orbit
end YM.Spectral
