import YM.Extra.ITERATION_NO_LOSS.Columns
import YM.Next.FREE_KERNELS.Rack


/-!
# No new harmonic hypothesis on the retained worksheet

At regulator alias-zero the wire alias costs are actual
values and only the origin contributes.

Read on the same T used by the
Horizon and no post hoc change of rows when passing to the Iteration
program.

Note the distinction from an assumption on the quantum loop
or determinant (not proved!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933
open Function Filter Set Matrix Lattice RG Precision Bloch Laurent Metric Exterior
  Next.Free Extra.Iteration
open scoped Topology BigOperators ComplexConjugate

/-- On the actual cross kernels. No summing the per-residue costs over
all residues; use one requested residue at a time. -/
theorem harmonic_column {j t : ℕ} (P : Flight j t) (k : ℝ) (hk : 0 < k) (ht : 4 ≤ t) :
    Harmonic (P.duo k) := by
  have pay := (secure_both k hk P.legal ht).2
  have h0 : (0 : Momentum) ∈ baseCube := by
    simpa using (mon_mem P.L (0:Site P.L))
  have he (r : Site P.L) (b c : TypeFace 2) :
      ((∑' z, (P.duo k).T (r,b) c z : ℝ) : ℂ) = (toll P.L 2 • (1 : Matrix (TypeFace 2) (TypeFace 2) ℂ)) b c := by
    rw [Complex.ofReal_tsum]
    have H := pay.bankRead P.legal 2 (show [].length ≤ j-2 from Nat.zero_le _) P r h0 b c
    change (∑' z, mode 0 z • ((meshBook (Flight.wire k) 2 [] P (r,b) c z : ℝ):ℂ)) = _ at H
    simp only [mode_constant,one_smul] at H
    change (∑' z, ((meshBook (Flight.wire k) 2 [] P (r,b) c z : ℝ):ℂ)) = _
    rw [H]
    unfold spread
    rw [Finset.sum_eq_single (0 : Site P.L)]
    · rw [show aliasAt (0:Momentum) (0 : Site P.L)=0 from Flight.toe_zero P]
      simp [listChip]
    · intro i _ hi
      simp [Flight.wire_none P k hi]
    simp
  intro r s b c
  exact Complex.ofReal_injective ((he r b c).trans (he s b c).symm)

/-- Exact harmonic condition in `Iteration.planned`, already paid any
 time using `Present` for the *same* H. -/
theorem harmonic {G : Gauge} {a : Levels G} {H : Horizon a} {l} (hp : Present a H l) (N m : ℕ) (hm : m<N) :
    Harmonic (H.towers N m) := by
  intro r s b c
  rw [(hp.2 N m hm).2]
  exact harmonic_column (destination a N m) _ a.clock.kernel.penalty_pos (a.clock.adm m) r s b c
end YM.Further.PhysicalPeriodLimitF933
