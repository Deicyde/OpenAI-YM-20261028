import YM.FullVolume.Scalar
import YM.FullVolume.Fields.Cement
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function RG Lattice Wilson MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n:Side}{G: Gauge} (A:History G)
def till (A: Levels G)(m p:ℕ): ℝ:=
  let B := A.budget m
  let P := A.params m
  let F := A.clock.allowance m
  let T := A.clock.loopCap m
  let H := 2*A.clock.hatBeta m
  let v := B.threshold
  let E : ℝ := Fintype.card (Site (A.S.side m p))
  let k := E*((F + PathData.loopsPrice B H P.paths T)+ H*baseBudget P.clip P.paths v)
  Real.exp (-k-(Fintype.card (Edge (Site (A.S.side m p))):ℝ)*Module.finrank ℝ G.Mat*Real.log (16/v))
lemma tills (m p:ℕ):0<till A.levels m p:=Real.exp_pos _
lemma lingers (h : A.Selected) (m p N : ℕ) (hn:N ≥ m) :till A.levels m p ≤ stripped A N p m:= by

  let B := A.levels.budget m
  let P := A.levels.params m
  let F := A.levels.clock.allowance m
  let T := A.levels.clock.loopCap m
  let H := 2*A.levels.clock.hatBeta m
  let v := B.threshold
  have hV : 0<v := B.threshold_pos
  let E : ℝ := Fintype.card (Site (A.S.side m p))
  let k := E*((F + PathData.loopsPrice B H P.paths T)+ H*baseBudget P.clip P.paths v)
  let R := A.rep N p m
  have hp := h.represents N p m hn
  have hs : R.p = B := hp.vac
  have hx : 0≤R.beta := (div_nonneg ((zero_lt_one.trans (A.levels.fits.delayed _)).le) (by norm_num)).trans hp.band.1
  have hh : R.beta ≤ H := hp.band.2
  have hK : E * (R.exCost P.paths T F + R.beta * baseBudget R.clip P.paths v) ≤ k := by
    have hE : 0 ≤ E := Nat.cast_nonneg _
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hE
    · unfold Rep.exCost; rw [hs]; unfold PathData.loopsPrice
      have hh' := P.paths_pos; dsimp only [v] at hV
      gcongr
    change R.beta * baseBudget R.clip P.paths v ≤ _
    rw [show R.clip=P.clip from hp.clip]; apply mul_le_mul_of_nonneg_right hh
    unfold baseBudget; have h:=P.clip.quadratic_pos; positivity
  rw [stripped, ← A.partition_eq h N p m hn]
  change Real.exp (-k-(Fintype.card (Edge (Site (A.S.side m p))):ℝ)*Module.finrank ℝ G.Mat*Real.log (16/v)) ≤ _
  apply (le_trans ?_ (mul_le_mul_of_nonneg_left
    (R.denominator hp.good hx v hV (le_of_eq (congr_arg BudgetPoint.threshold hs.symm)) (A.nonnegative h N p m hn)) (Real.exp_pos (-R.scalar)).le))
  · rw [← Real.exp_add]; apply Real.exp_monotone
    change -k-_ ≤ _
    linarith only [hK]
theorem taps (h : A.Selected) (m p N: ℕ) (hk:m≤N): lack (A.rep N p m)=stripped A N p m:=(strips h hk).symm
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.lingers
