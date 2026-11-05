import YM.RG08.Bands.Crest
/-!
# Authentic clocked pulses. Covariance sign at each step; pricing inherited.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix Tree
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {X:Chain}{G:Gauge}{N i:ℕ}
lemma veil_s {F:Patch}{K:KernelChoices}{W:Repeated F.L}{Q:Train F.J} (h:F.Branches K G): Vily (veiled (conditionalCov G W K Q)):= by
  intro c; let f := c*F.L; let S:= linked F K c f rfl; let T:= W.forest S.ratio
  let H:=FreeResolvent.treeMatrix G S T (pink K.penalty Q)
  have he: H.PosDef:= forest_precision G K Q c f rfl h T
  have ht:= people F K W Q h (c:=c) (f:=f) rfl
  let U:= chargeS S T G
  rw [show (veiled (conditionalCov G W K Q)).acts c=U * H⁻¹ * Uᵀ from ht]
  change (U * H⁻¹ * Uᵀ)ᵀ = U * H⁻¹ * Uᵀ
  rw [transpose_mul,transpose_mul, transpose_transpose, show (H⁻¹)ᵀ=H⁻¹ by simpa using he.inv.isHermitian.eq]; rw [Matrix.mul_assoc]
lemma authentic (hp:X.Wake G)(ν:G.ColorIndex)(D':ChartRatio G)(i N:ℕ): Vily (veiled (dance X ν D' N i).cv):= veil_s (hp i)
end YM.RG08.Bands
