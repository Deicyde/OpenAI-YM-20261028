import YM.Push.LOOP_COEFFICIENT.Annulus
import YM.Push.LOOP_COEFFICIENT.ReadBounds
import YM.Push.LOOP_COEFFICIENT.SignatureLines

/-!
# Period-limit transverse mixed precision test, from the reference matrices

Sufficient vertex estimates at zero background only, with separate strip
and small-external-radius annular bills. They are **inputs**, to be attached
via Synced to the Hessian/gauge operators of the same step (and reduced
upstream); not an assumption on the coefficient extracted from any trace.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Complex Matrix Lattice Laurent Bloch MeasureTheory Measure Filter Metric Set
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {d : Type} [Fintype d] [DecidableEq d]

def laser (a : G.ColorIndex) (V : Vertex (Axes G) d d) (p q : Momentum) := bubbleTrace V (Pi.single (1,a) 1) (Pi.single (1,a) 1) p q

def bill (a : G.ColorIndex) (V : Vertex (Axes G) d d) (k : E4) (t : ℂ) : Reading d :=
  Reading.ofVertex V (radians k) (t • unitAxis 0) (Pi.single (1,a) 1)

abbrev VecVertex (G : Gauge) := Vertex (Axes G) (Axes G) (Axes G)
abbrev SiteVertex (G : Gauge) := Vertex (Axes G) G.ColorIndex G.ColorIndex

def fineKernel (V : VecVertex G) (W : SiteVertex G) := (1/2:ℂ) • logKernel V - logKernel W





variable {V : Vertex (Axes G) d d} {η C : ℝ} {a : G.ColorIndex}


lemma logKernel_analytic {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {V : Vertex a b b} (h : LogStrip V η C)
    {p : Momentum} (hp : p∈Tube (η/2)) : ContDiffAt ℂ ω (logKernel V) p := analyticMatrix (fun i j => boxMean_smooth ((Work.F07.stripOpen _).mem_nhds hp)
      (fun _ hs k => h.bubble_analytic (Pi.single i 1) (Pi.single j 1) hs (radians_strip k (half_pos h.width))))





variable {X : VecVertex G} {Y : SiteVertex G}





/-- Component tests and actual derivatives of ruled symbols. `M,lo,hi,δ`
are annular bills fixed pre-L; μ may shrink. The shifted flat inverse tested
independently at all external t incl zero. -/
structure ShellBill (a : G.ColorIndex) (X : Vertex (Axes G) d d) (R : E4 → ℂ → Reading d) (lo hi δ M μ : ℝ) : Prop where
  inner k : ‖k‖ ≤ lo*μ → ∀ t : ℂ, ‖t‖≤δ*μ →
    DifferentiableAt ℂ (fun t => laser a X (t • unitAxis 0) (radians k)) t ∧ (bill a X k t).Sized M μ
  annulus k : k∈crown (lo*μ) hi → ∀ t : ℂ, ‖t‖≤δ*‖k‖ →
    DifferentiableAt ℂ (fun t => laser a X (t • unitAxis 0) (radians k)) t ∧ (bill a X k t).Sized M ‖k‖ ∧
      (bill a X k t - R k t).Sized (M*relativeScale μ ‖k‖) ‖k‖
  outer k : k∈zone → hi < ‖k‖ → ∀ t : ℂ, ‖t‖≤δ →
    DifferentiableAt ℂ (fun t => laser a X (t • unitAxis 0) (radians k)) t ∧ (bill a X k t).Sized M 1

variable {lo hi δ M μ : ℝ}



















end YM.Push.Loops
