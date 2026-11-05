import YM.Extra.WEAK_SCALING_ACTLAW.Dimension
import YM.Extra.WEAK_SCALING_ACTLAW.Orientation


/-!
# Common-field interface with explicit color normalization

`common`: final ActLaw route for the prescribed local J where W starts with
a calibrated free stress (or use W.T.J's free conserved/tensor/mean-free
properties via `Color.line_of_properties`). `prepare`: obtain the actual
conserved real line above the finite estimates to help selecting that J
prior to the RPrep flux obligations. The free rank inequalities here are
PROVED on the color-invariant Bianchi/Maxwell/test quotient. No assumption
on YM kernels of weight-five jets echoing those ranks. This doesn't infer the local
Ward equations from conservation or comparison alone!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Filter Function Set Table Org Climb Ward Extraction Spec
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Order} {V : DiffPlan S} (W : MaxwellData C) (s : Seed C f S)
variable {I : IR (C:=C) S}

/-- The Wstress of E evaluated on the exact linear radial curls and using
no within-slot Wick contractions (since a class in the Maxwell field table).
Inner product on physical colors, not unnormalized traces. Sum over both
orders i,j in δ_ab term and the factor **1/4**. -/
def canonical (C : Family G) : (Bel C.book).Stress := Cube.Types.stress (Color.pinned C.book)






lemma birth (hg : G.Simple) (he : Supply C f W.hT.spin) (hv : V.Inclusions S) (hd : V.Derivatives S) :
    ∃ J : S.Stress, J ≠ 0 ∧ Centered J ∧ Conserved V s.kernel.spin J ∧ RawTensor s.kernel.spin J := by
  obtain ⟨_,_,⟨X⟩⟩ := weak_curve s W he 1 5 1 le_rfl hv hd
  have h := Work.D06.answer s.cutoff s.kernel.smooth s.kernel.laws.toSymmetric s.generic V hd hv s.kernel.spin
  exact stress_birth s.kernel W.hT X (by omega) h (Dimension.space hg W.hT)

theorem prepare (hg : G.Simple) (he : Supply C f W.hT.spin) (hv : V.Inclusions S) (hd : V.Derivatives S)
    {τ : ℝ} (ht : τ ≠ 0) (hT : W.T.J = τ • canonical C) :
    ∃ J : S.Stress, J ≠ 0 ∧ Centered J ∧ Conserved V s.kernel.spin J ∧ RawTensor s.kernel.spin J ∧
      ∀ P : S.Stress, Centered P → Conserved V s.kernel.spin P → RawTensor s.kernel.spin P → ∃ c : ℝ, P=c • J :=
    before_flux W s he hv hd (Color.calibrated_line hg _ W.T W.hT W.lit.pales ht hT) (Dimension.space hg W.hT)


end YM.Extra.WeakScaling
