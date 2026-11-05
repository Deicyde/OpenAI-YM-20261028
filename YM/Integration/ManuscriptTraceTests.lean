import YM.TraceExtension.Endpoint

/-!
# Tests of the centered stress trace

All readings use the centered stress trace of one Final in its selected
vacuum. The Euclidean time-axis asymptotic and the Minkowski Wightman and
Weyl countertests are recorded separately. The palette covers finite Wick
polynomials in elementary mass-shell kernels with finite differential
numerators. A Maxwell identification preserves the vacuum and translations
and takes values in the symmetric transverse waves. The last test is the
invariant-sector formulation with averaging of the electric Weyl tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptTraceTests

open Set Metric MeasureTheory Spec Boundary Mink TraceExtension
open TraceExtension.Photons
open scoped Topology InnerProductSpace

universe u v
variable {G : Gauge} {C : Family G} {q : Extraction.Order} {S : Table C.book}

/-- The two-point boundary countertest permits arbitrary left and right
polynomial fields, without a bound on their comparison grades. -/
def WickCountertests (F : Final C q S) : Prop :=
  ∀ (Color : Type u) (palette : Wick.Palette Color) (left right : Wick.PolyField Color),
    ∃ x y : Probe E4, HasCompactSupport ⇑(waveTest (productTest x y)) ∧
      F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest x y) ≠
        palette.wicks left right (waveTest (productTest x y))

/-- Compact spacetime tests of the relative-locality vacuum matrix identity. -/
def MaxwellCountertests (F : Final C q S) : Prop :=
  ∀ (n : ℕ) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient n), Comparison F U →
    ∃ (f : Test4) (h : TestList n), HasCompactSupport ⇑f ∧
      (∀ i, HasCompactSupport ⇑(h i)) ∧ (∀ i, Probe.bar (h i) = h i) ∧
      (∀ i, Fields.causal f (h i)) ∧
      inner ℂ (coherent (-h)) (signal F U f) ≠
        inner ℂ (signal F U (Probe.bar f)) (coherent h)

/-- Matrix elements averaged over transformations that preserve wave inner
products and fix the image. The trace test can be confined to an arbitrarily
small ball. The open Weyl-test region may have several components. -/
def InvariantCountertests (F : Final C q S) : Prop :=
  ∀ (n : ℕ) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient n), Comparison F U →
    ∀ (I : Type v) [MeasurableSpace I] (μ : Measure I) [IsProbabilityMeasure μ],
    ∀ (P : I → Ambient n → Ambient n),
      (∀ z x y, PhysicalWave x → PhysicalWave y →
        inner ℂ (P z x) (P z y) = inner ℂ x y) →
      (∀ z x, P z (U x) = U x) →
    ∀ r : ℝ, 0 < r →
      ∃ (Q W : Set E4), IsOpen Q ∧ IsOpen W ∧ closure Q ⊆ ball 0 r ∧
        (∀ x ∈ closure Q, ∀ y ∈ closure W, x-y ∈ spacelike) ∧
        ∃ (f : Test4) (h : TestList n), tsupport f ⊆ Q ∧ HasCompactSupport ⇑f ∧
          (∀ i, tsupport (h i) ⊆ W) ∧ (∀ i, HasCompactSupport ⇑(h i)) ∧
          (∀ i, Probe.bar (h i) = h i) ∧
          (∫ z, inner ℂ (P z (coherent (-h))) (signal F U f) ∂μ) ≠
            ∫ z, inner ℂ (signal F U (Probe.bar f)) (P z (coherent h)) ∂μ

/-- The exact trace and all three comparisons on a single Final. -/
structure Tests (F : Final C q S) (hG : G.Simple) : Prop where
  centered (f : Test4) :
    inner ℂ F.action.operators.vacuum (excitation F.action.operators (pinned F) f) = 0
  identified (f : Test4) :
    F.action.operators.field (pinned F) f =
      F.action.operators.field (S.pin 4 (stressTrace F.sector.energy)) f -
        (euclideanVEV S (selected F) (stressTrace F.sector.energy) * ∫ x, f x) •
          LinearMap.id (R := ℂ)
  shortDistance : EuclideanAsymptotic F (Trace.Verse.award G)
  positive : 0 < Trace.Verse.award G
  spectrum : ∃! μ, Trace.Target.HighEnergy F hG μ
  wick : WickCountertests.{u} F
  maxwell : MaxwellCountertests F
  invariant : InvariantCountertests.{v} F

theorem of_result (F : Final C q S) (hG : G.Simple) (H : Trace.Target.Result.{u} F hG) :
    Tests.{u,v} F hG := by
  classical
  refine ⟨H.centered, H.identity, H.shortDistance, H.positive, H.law, ?_, ?_, ?_⟩
  · intro Color palette left right
    by_contra! h
    exact H.exclude.wick_polynomial Color palette left right h
  · intro n U hU
    by_contra! h
    exact H.exclude.noMaxwellFock n U hU h
  · intro n U hU I _ μ _ P hP hfix r hr
    by_contra! h
    exact Photons.smell hU H.shortDistance H.positive μ P hP hfix r hr h

/-- A constructed calibrated Wilson family and its selected relativistic
reconstruction carrying the tests, on a refinement of
the initial order prescribed by the caller. -/
theorem exists_wilson_final (G : Gauge) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (p : Extraction.Order) :
    ∃ (C : Family G) (q : Extraction.Order) (S : Table C.book) (F : Final C (p.refine q) S),
      C.Makes ∧ Calibrated C ∧ C.path.levels.clock.kernel.penalty = ε ∧
        Extraction.Wcmain C ∧ Tests.{u,v} F hG := by
  obtain ⟨C, hC, hCalibration, hPenalty, hWilson, q, ⟨S, ⟨F⟩⟩, hTrace⟩ :=
    Trace.Target.main.{u} G hG ε hε p
  exact ⟨C, q, S, F, hC, hCalibration, hPenalty, hWilson, of_result F hG (hTrace S F)⟩

end YM.Integration.ManuscriptTraceTests

