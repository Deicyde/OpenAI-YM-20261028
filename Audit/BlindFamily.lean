import ChallengeSpec

/-! Audit check (not part of the submission): the lattice-side clause `WilsonRegularity`
is satisfied by a Wilson family whose insertions never read the gauge field. The Haar
probability measure is taken as a parameter; its existence on a compact group is standard. -/
set_option autoImplicit false
noncomputable section
namespace AuditDemo
open YangMills MeasureTheory Filter

variable (g : GaugeGroup) (μ : Measure g.image) [hμ : IsProbabilityMeasure μ]
  (hH : μ.IsHaarMeasure)

/-- Insertions are the constant `h v`: independent of spacing, volume, site and links. -/
def blindFamily (Tok : Type) (h : Tok → ℂ) : WilsonFamily g where
  period p := ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  periodStrict a b hab := by show a + 1 < b + 1; omega
  denominatorStrict a b hab := by show a + 2 < b + 2; omega
  beta N _ := Real.log ((N + 2 : ℕ) : ℝ)
  haar := μ
  probability := hμ
  invariantHaar := hH
  Token := Tok
  insertion _ _ v _ _ := h v

theorem blind_regular (Tok : Type) (h : Tok → ℂ) :
    WilsonRegularity (blindFamily g μ hH Tok h) := by
  refine ⟨⟨1, one_pos, fun ε hε => Eventually.of_forall fun N p => ?_⟩,
    fun _ _ _ _ => continuous_const, fun _ _ _ _ _ _ => rfl,
    fun _ => ⟨∅, fun _ _ _ => by intro sites U V _; rfl⟩⟩
  have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
  have hd : (blindFamily g μ hH Tok h).beta N p /
      Real.log ((blindFamily g μ hH Tok h).mesh N)⁻¹ = 1 := by
    show Real.log ((N + 2 : ℕ) : ℝ) / Real.log ((((N + 2 : ℕ) : ℝ))⁻¹)⁻¹ = 1
    rw [inv_inv, div_self hpos.ne']
  rw [hd, sub_self, abs_zero]
  exact hε

end AuditDemo
