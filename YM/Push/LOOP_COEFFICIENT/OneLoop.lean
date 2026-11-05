import YM.Push.LOOP_COEFFICIENT.Coefficient
import YM.Push.LOOP_COEFFICIENT.Comparison
import YM.Push.LOOP_COEFFICIENT.Wick


/-!
# One-loop projection, cap and all paid periods (conditional one-step version)

This interface consumes inlet path/vertex/stationarity/free data and a
cofinal compatibility. Not `Kin.Planned`; includes no construction of the
minimizing branch or classical row/cubic/quartic output, not even a claim
that those objects satisfy the vertex bills used here without further proof.
The output width only uses η (independent of the input path width σ and
scale L); the input-size gain after pulling the loop paths uses the separate
phase-fitting condition at L. Constants in comparisons need separately to
have the appropriate pre-choice dependencies to iterate. No positivity claim
for determinants away from active analytic germs. All statements here are in
the unmasked Taylor convention of PCalc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Lattice Laurent RG Wilson Tree Precision Bid Exterior Bloch
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {L : Side} {R : LoopData G L} {W : PathData G} {H : Precision.Bed} {p : Clip} {P : ChartRatio G}
variable {η C σ D Λ M M' δ lo hi : ℝ}

lemma kinetic_period (H : Precision.Bed) (p : Momentum) (z : Cover) : kineticSymbol G H.metric (p+reciprocal z) = kineticSymbol G H.metric p := by rw [kineticSymbol,Row.periods,neg_add,← reciprocal_neg,symbol_period,symbol_period,kineticSymbol]

namespace LoopData
structure Along (R : LoopData G L) (W : PathData G) (p : Clip) (H : Precision.Bed) (P : ChartRatio G) where
  coarse : ℕ → Side
  fine : ℕ → Side
  sizes i : (fine i).val = (coarse i).val * L.val
  unbounded : Expands coarse
  S (i : ℕ) : StepData (coarse i) (fine i)
  F i : Forest (S i).ratio
  path i : fieldDir G (coarse i) 1 → AxisChart G (F i)
  uses i : R.Uses (g:=ratioStep sizes i) (S i) p W
  admits i : Admission (F i) (path i) p W (R.lift (g:=ratioStep sizes i)) P
  wardJ i : mean (S i) * R.lift (g:=ratioStep sizes i) = 1 - (S i).kernel.penalty⁻¹ • Precision.K (H.metric.acts (coarse i))
  sym i : (H.metric.acts (coarse i)).IsSymm
  sworn i : Sworn H (coarse i) G

variable (h : Along R W p H P) (hr : R.Regular η C) (hh : H.metric.strip η C) (hw : W.Bounds p σ D Λ) (hf : η/L.val ≤ σ)
include h hr hh hw hf


open scoped Matrix.Norms.L2Operator in
lemma Along.wick (a : G.ColorIndex) (h1 : H.metric.read 0=1) {B : ℝ} (hb : ∀ z ∈ Tube (η/2), Entries (R.residual W H a z) B) : Wick (R.residual W H a) (η/2) B 4 :=
    ⟨half_pos hr.joint.width, (hb 0 (Work.F07.realStrip _ (half_pos hr.joint.width) (star_zero _))).nonneg,
      fun p hp => (hr.target_diff hw hf hp).sub ((kinetic_diff hh hr.joint.width hp).const_smul ((R.alpha W a):ℂ)),
      fun z v hz => by unfold residual; simp only [Pi.sub_apply,Pi.smul_apply,hr.target_period R W hz v,kinetic_period H],hb,
      R.residual_four a (hg:=h.sizes) h.unbounded hr hh hw hf h.uses h.admits h.sym h.sworn h1⟩





abbrev unitColor (G : Gauge) (a : G.ColorIndex) : G.Color := EuclideanSpace.basisFun G.ColorIndex ℝ a


structure Scan (R : LoopData G L) (a : G.ColorIndex) (M M' η lo hi δ : ℝ) : Prop where
  cmp : ∃ Q : Normalization (JointType G L), Comparison R.base R.ref Q η M
  inner : 0<lo
  fits : lo*(L.val:ℝ)⁻¹ ≤ hi
  outer : hi < Real.pi
  side : 0<δ
  narrow : δ ≤ 1/8
  vector : ShellBill a R.vector (fun k t => vectorFlat k t (unitColor G a)) lo hi δ M' (L.val:ℝ)⁻¹
  ghost : ShellBill a R.ghost (fun k t => scalarFlat k t (unitColor G a)) lo hi δ M' (L.val:ℝ)⁻¹


end LoopData

open LoopData

end YM.Push.Loops
