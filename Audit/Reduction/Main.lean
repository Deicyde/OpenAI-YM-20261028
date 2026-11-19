import Audit.Reduction.Regular
import Audit.Reduction.Trace
import Audit.Reduction.Haar
import Audit.Reduction.Law
import Audit.Reduction.Riemann
import Audit.Reduction.Converges
import Audit.Reduction.Recon
import Audit.Reduction.OPE

/-!
# The lattice clause of the public challenge is redundant

`wilson_clause_redundant`: any hierarchy, over any Wilson family, that satisfies the three
continuum clauses of `Hierarchy.Properties` (and gives correlation `0` to words containing the
zero vector in its selected phase) yields the full per-group statement of `JointExistence`
with a Wilson family whose insertions never read the gauge field.
-/

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set

theorem wilson_clause_redundant (g : GaugeGroup) {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (hR : T₀.Reconstructed) (hO : T₀.OperatorProductExpansion) (hT : T₀.TraceTest)
    (hZ : ZeroInvisible T₀) :
    ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p →
      ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) := by
  obtain ⟨μ, hμ, hH⟩ := exists_haar g
  refine ⟨blindFamily μ hH T₀.Field, blind_regular μ hH T₀.Field, fun p hp =>
    ⟨id, strictMono_id, reduced T₀ μ hH, ?_, reduced_reconstructed T₀ μ hH hR,
      reduced_ope T₀ μ hH hO hZ, reduced_trace T₀ μ hH hT⟩⟩
  exact blind_converges μ hH T₀.Field (hp.comp strictMono_id)
    (fun N p' _ v x => blind_finiteMoment μ hH T₀.Field N p' v x)
    (fun p' _ t ht => riemann_tendsto _ p' t ht)

/-- `JointExistence` follows from continuum data alone: no lattice content is needed. -/
theorem jointExistence_of_continuum
    (h : ∀ g : GaugeGroup, g.IsSimple → ∃ (C₀ : WilsonFamily g) (T₀ : Hierarchy C₀),
      T₀.Reconstructed ∧ T₀.OperatorProductExpansion ∧ T₀.TraceTest ∧ ZeroInvisible T₀) :
    JointExistence := by
  intro g hg
  obtain ⟨C₀, T₀, hR, hO, hT, hZ⟩ := h g hg
  exact wilson_clause_redundant g T₀ hR hO hT hZ

end YMAudit
