import YM.Shift.Osc
import YM.Work.C07.Continue

/-!
# C07: temporal PDE on full joint Schwartz

Proof in Work/C07/Euclid (infinitesimal form), /Geometry (complex scaling parameter z
on the time components), /Integrate (tested identities at imaginary z), /Continue
(to z=1). Finally use continuity at fixed strict imaginary heights as a functional of f.
All statements relative to the supplied Waves on the *same* S, anchored to T.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C07
open Boundary Set Filter Function Table Analysis MeasureTheory Complex Bid
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} {Y : Waves S} {n : ℕ}

/-- Use existing contour estimates: `seeks` even finds a distribution at non-strict y. -/
lemma continuous_test (hB : Y.Bounds) (ha : Y.Along) (hl : Y.Lines) (hb : Y.Breathes)
    (y : Heights n) (hy : y ∈ east n) (q : Fin n → S.Union) : Continuous (Y.psi q y) := by
  obtain ⟨W,hW⟩ := Y.seeks hB ha hl hb y (bigger hy)
  haveI : (𝓝[east n] y).NeBot := awaits (bigger hy)
  have he (f : Joint n) : Y.psi q y f = W q f :=
    tendsto_nhds_unique (ha n q f y hy) (hW q f)
  rw [funext he]; exact (W q).continuous

lemma incline_cont (a : SpaceAxis) (y : Heights n) : Continuous (inclined a y) := by
  have h (i : Fin n) (b : Axis) : Continuous (realTerm i b) :=
    (LineDeriv.lineDerivOpCLM ℂ (Joint n) (Points.direction i b)).continuous
  unfold inclined; refine continuous_finsetSum _ fun i _ =>
    Continuous.add (Continuous.add ?_ ?_) ?_
  · exact (multiplier i a.castSucc).continuous.comp (h i timeAxis)
  · exact (multiplier i timeAxis).continuous.comp (h i a.castSucc)
  exact (h i a.castSucc).const_smul ((y i : ℂ)*I)

-- Interpretation checks not using the contour hypotheses.
-- Arity zero: both terms empty in effect (even for nonzero joint test).
example (v : Fin 0 → S.Tag) (R : Rotation S) (P : Waves S)
    (f : Joint 0) (a : SpaceAxis) (y : Heights 0) :
    (∑ i, P.psi (update (ink v) i (kick R a (v i))) y f) =
      P.psi (ink v) y (inclined a y f) := by
  simp [inclined, Waves.psi]

-- Single-slot y arbitrary (including negative), explicit spatial and temporal coefficients.
example (f : Joint 1) (y : Heights 1) (a : SpaceAxis) (p : Points 1) :
    inclined a y f p = (p 0 a.castSucc : ℂ) * fderiv ℝ f p (Points.direction 0 timeAxis) +
      ((time (p 0) : ℂ)+(y 0 : ℂ)*I) * fderiv ℝ f p (Points.direction 0 a.castSucc) := by
  simp [inclined, realTerm, multiplier_test, time, add_assoc, add_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem answer : YM.Bid.C07 := by
  intro G L S T R K h V _ hT _ hO hR _ Y hr hb hB hl ha n v a f y hy
  let A (u : Joint n) := ∑ i, Y.psi (update (ink v) i (kick R a (v i))) y u
  let B (u : Joint n) := Y.psi (ink v) y (inclined a y u)
  have hA : Continuous A :=
    continuous_finsetSum _ fun i _ => continuous_test hB ha hl hb y hy _
  have hX : Continuous B :=
    (continuous_test hB ha hl hb y hy _).comp (incline_cont a y)
  have he (k : ℕ) : A (Probe.cap k f) = B (Probe.cap k f) :=
    compact_boost hO hR hT.smooth hr hB a y hy v (Probe.cap k f) (Probe.finite_cap k)
  have hz : Tendsto (fun k : ℕ => A (Probe.cap k f)) atTop (𝓝 (A f)) :=
    (hA.tendsto f).comp (Probe.persistent f)
  simp_rw [he] at hz
  exact tendsto_nhds_unique hz ((hX.tendsto f).comp (Probe.persistent f))

end YM.Work.C07
