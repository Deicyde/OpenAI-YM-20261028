import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Full

/-! # Row-column price for the full kernels

Even when using the full topology the same tag cuts are enough; one
uniform delay. Here kernels written as if in a full space, for local
ratio tests incl multiple components. `cover_exact` checks agreement with
the covariance used in the committed integration (inactive Haar not
replaced by these tangents). These kernels need no genuine replacement of
the integration coordinates by a larger Gaussian law with tree modes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Full
open Function Filter Lattice RG Precision Pressure Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur
open Next.SectorChange.Completion
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x C Y s : ℝ}
variable (A : Stores S) (F : Forest S.ratio)



lemma deck_symm (T : Tube G S) (V : Config G c) (z : Coord G c) (k : S.Choices) :
    (deck x A F V k T z).IsSymm := by
  have he := (precision_symm x A F V k T z)
  let B := precision x A F V k T z
  have h : (wide B (1:Gaussian.Table (vacant A F x G))).IsSymm := by
    unfold Matrix.IsSymm wide; rw [Matrix.fromBlocks_transpose,
      show B.transpose=B from he]; simp only [Matrix.transpose_one,Matrix.transpose_zero]
  apply h.submatrix





structure FullEpoch (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (r t η γ C x : ℝ) : Prop where
  geometry : 120 ≤ radiusB x
  epoch : ∀ {c f : Side} (S : StepData c f), S.patch=P → 100*(1+radiusB x) ≤ c.val →
      ∀ (T : Tube G S), Pt.Funds S T →
        ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), A.flags=RG.flags (temp x) V →
          ∀ (k : S.Choices) (z : Coord G c), ‖z‖ ≤ r →
          Epoch (point S) (groupWindow G S x) x (deck x A F V k T) (coverKernel x A F V k T)
            z n t η γ C ∧ coverKernel x A F V k T z=board x A F G (sector x A F V k T z)



end YM.AnalyticBridge.NonflatCovarianceLocality.Full
