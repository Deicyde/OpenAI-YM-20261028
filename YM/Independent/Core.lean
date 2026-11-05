import YM.EveryPhase.Extension
import YM.Integration.ManuscriptTraceTests
import YM.OPE.Orbits.Kernel

/-! The same Wilson table, phase selection and physical field quotients enter the
reconstruction, the centered trace countertests, and the finite-grade expansions. -/
set_option autoImplicit false
noncomputable section

namespace YM.Independent

open Filter MeasureTheory OPE OPE.Orbits
open scoped Topology BigOperators

universe u v
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

structure Core (hG : G.Simple) (F : Spec.Final C f S) (L : EveryPhase.Almanac F)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) : Prop where
  services : Services C f S
  reconstruction : EveryPhase.Completed F L
  trace : Integration.ManuscriptTraceTests.Tests.{u,v} F hG
  ope : Foundation F Q
  /-- Joint position tests with bounded total variation. The geometry, complex
  density, and (in the character version) varying character may follow the radius. -/
  joint (I J : Type) [Fintype I] [Fintype J] (d : I → ℕ) (e : J → ℕ)
      (a : Labels S d) (b : Labels S e) (M η c ε : ℝ) :
    0 ≤ M → 0 < η → 0 < c → 0 < ε → ∀ (D : ℕ) (K : Type) [MeasurableSpace K] (B : ℝ),
      ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (μ : Measure K) (w : K → ℂ) (p : K → Loc I J),
        AEMeasurable p μ → Integrable w μ → (∫ s, ‖w s‖ ∂μ) ≤ B →
        (∀ᵐ s ∂μ, w s ≠ 0 → p s ∈ FitsOn I J M η c r) →
        (∀ χ : K → F.α.space.X, AEMeasurable χ μ →
          JointEstimate F Q D a b (B * costRemainder D d ε r) μ w p (some ∘ χ)) ∧
        JointEstimate F Q D a b (B * costRemainder D d ε r) μ w p (fun _ => none)

namespace Core

theorem of_receipts (hG : G.Simple) (F : Spec.Final C f S) (L : EveryPhase.Almanac F)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (hL : EveryPhase.Completed F L) (hT : Trace.Target.Result.{u} F hG)
    (hS : Services C f S) (hQ : Foundation F Q) : Core.{u,v} hG F L Q := by
  refine ⟨hS, hL, Integration.ManuscriptTraceTests.of_result F hG hT, hQ, ?_⟩
  intro I J _ _ d e a b M η c ε hM hη hc hε D K _ B
  exact estimates_weighted (K := K) F Q hS a b hM hη hc hε D B

/-- The actual point correlation and its finite expansion at a single center.
`s = none` reads the unselected table, and `s = some χ` reads character χ.
The radius threshold precedes every allowed position and every viewer. -/
theorem point {hG : G.Simple} {F : Spec.Final C f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q)
    {I J : Type} [Fintype I] [Fintype J] {d : I → ℕ} {e : J → ℕ}
    (a : Labels S d) (b : Labels S e) {M η c ε : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) (D : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4) (y : J → E4),
      WithinRoom r M η x o → ClearOf o y c → ∀ s : Viewers F,
      ‖whole (spectator F s) x a y b -
        ∑ j : Fin (D + 1), ∑ i : Q.channels j.val, Q.coef j.val i x a o *
          whole (spectator F s) (sole o) (sole (Q.actor j.val i) : Labels S (fun _ : Unit => j.val)) y b‖
        ≤ r ^ ((D : ℝ) + 1 - weight d - ε) := by
  filter_upwards [H.ope.discrepancy I J d e a b M η c ε hM hη hc hε D] with r hr
  intro x o y hx hy s
  exact (hr x o y hx hy).2.2.2 s

end Core
end YM.Independent
