import YM.Org.Input
import YM.Spin.Floor
/-!
# Twists -- specialized to IR.H1+ ports. Conditional consumers are
proof missions, no assessment of this level of estimates. Uses POLAR ν with
centered flux V; cannot change K action afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Org
open Function Set Filter MeasureTheory Spec Table Spin Ward Climb OS
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
variable (V : DiffPlan S) (W : MaxwellData C) (I : IR (C:=C) S) (H : UV C F S V W I)

abbrev mill (c : ℝ) (U : ∀ d, Spin.change S d) := morph W.T.K (c⁻¹ • I.Y) U

structure Tab (S : Table C.book) (V : DiffPlan S) (W : MaxwellData C) (I : IR (C:=C) S) (H : UV C F S V W I) (c : ℝ)
    (U : ∀ d, Spin.change S d) (Y : S.Stress) : Prop where
  Γ : Crystal H.basis.kernel V I.J I.p I.Y c
  hU : ∀ d,realH H.basis.kernel.spin W.hT.spin (U d)
  pivot : Spin.Port (mill W I c U) H.basis.kernel.spin
  locality : Spec.Locals (⟨V,mill W I c U,Y⟩ : Spec.Algebra S) H.basis.kernel.spin

/-- Issue spin commission. Fracture further for WP resolution. NOTE
outputs conditionals not assumed in YU. May require G.Simple via dossier.
-/
structure Commission : Prop where
  shape : V.Inclusions S → V.Derivatives S → Shapes H.basis.kernel V I.J I.p I.Y
  scales : V.Inclusions S → V.Derivatives S → Shapes H.basis.kernel V I.J I.p I.Y → ∃ c : ℝ,
    Crystal H.basis.kernel V I.J I.p I.Y c
  lens : V.Inclusions S → V.Derivatives S → ∀ c, Crystal H.basis.kernel V I.J I.p I.Y c →
    (∀ n (x : Points n), x∈conf n → Still V (c⁻¹ • I.Y) x) → ∀ d, ∃ U w, Spin.Tilt W.T.K H.basis.kernel.spin W.hT.spin (c⁻¹ • I.Y) d U w
  group c U : V.Inclusions S → V.Derivatives S → Spin.Port (mill W I c U) H.basis.kernel.spin →
    (∀ n (x : Points n), x∈conf n → Still V (c⁻¹ • I.Y) x) →
    (mill W I c U).Laws V H.basis.kernel.spin ∧ (mill W I c U).Oriented S
  retune c U : V.Inclusions S → V.Derivatives S → Crystal H.basis.kernel V I.J I.p I.Y c →
    (mill W I c U).Laws V H.basis.kernel.spin → (mill W I c U).Oriented S →
    ∃ J : S.Stress, Conserved V H.basis.kernel.spin J ∧ Tensorial (mill W I c U) J ∧
      StressLaws S J V.deriv (c⁻¹ • I.Y)
  -- generates Lorentz
  generate (c U J) : Tab S V W I H c U J → wand V U W.vacuum

lemma Commission.picks (Z : Commission V W I H) (hv : V.Inclusions S) (hp : V.Derivatives S) :
    ∃ c U J, Tab S V W I H c U J ∧ ∃ K0 : Boundary.Spins S, K0.Descends (mill W I c U) H.basis.kernel.spin := by
  obtain ⟨c,Hc⟩ := Z.scales hv hp (Z.shape hv hp)
  obtain ⟨U,hu,ht,hp'⟩ := Climb.descends W.T W.lit _ V Hc hp (Z.lens hv hp c Hc)
  obtain ⟨he,hh⟩ := Z.group c U hv hp ht hp'
  obtain ⟨J,h1,h2,h3⟩ := Z.retune c U hv hp Hc he hh
  have hj : Tab S V W I H c U J := ⟨Hc,hu,ht, hv,hp,H.aligned,he,hh, Climb.comparison H.weak,h1,h2,h3⟩
  refine ⟨c,U,J,hj,Spin.reach V W.T U (c⁻¹ • I.Y) hu ?_ hv H.basis.kernel.laws.toSymmetric W.vacuum W.rolls (Z.generate c U J hj)⟩
  exact Spin.transmits U _ W.lit _ ht
end YM.Org
