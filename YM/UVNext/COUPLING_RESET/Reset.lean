import YM.UVNext.COUPLING_RESET.Probe
import YM.UVNext.COUPLING_RESET.Root



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Recover the two scalars on a trial family of exact-format Wilson outputs

Compare the input response at **two physical configurations** on the output
lattice, one of them flat. Correct relative to a path-independent-in-beta
recipe at this level (but the activity payloads can include trial changes!).
Raw equality at OTHER fields costs something in addition to separation, e.g.
the response remainder bound `ShapeControl` below. Not testing after dropping
masks globally, Taylor truncating the output, or assuming no real flags at
integration. In use `H` here is the actual UNNORMALIZED transferred density
relative to coarse product probability Haar; multiplying by a common positive
constant moves only v and the overall multiplier, see `rescale_*` below.
Nothing says there is an intrinsic beta readout on a measure without committed
paths/activities. Accuracy of log-ratios beyond transport is a physical
hypothesis on the corresponding probes, not asserted from a partition bound.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport Lattice Wilson RG Activities Function Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side}

/-- Candidate data for one output level. Arguments of `terms` are curve
parameter and ADDITIVE coupling correction beyond `base` (`beta+alpha`
in a step). In particular may just ignore the second argument: cover the case
of activities supplied by independent remainder calculations. `Valid`, frozen
address comparison and jet norms are additional obligations on these *same*
data for a Program application. -/
structure Template (G : Gauge) (n : Side) where
  path : PathData G
  clip : Clip
  p : BudgetPoint
  terms : ℝ → ℝ → Activities G n

/-- Log-ratio, ignoring no terms when both readings positive. -/
def contrast (H : ℝ → Config G n → ℝ) (V : Config G n) x := Real.log (H x 1) - Real.log (H x V)
def scalar (H : ℝ → Config G n → ℝ) x := Real.log (H x 1) / sites n

namespace Template
variable (A : Template G n)

/-- Correction `d` for an unmarked evaluation, with explicit unnormalized
vacuum scalar `v`. The same `Rep` would be used to normalize insertions. -/
def trial (base : ℝ → ℝ) (x d v : ℝ) : Rep G n := ⟨A.path,A.clip,A.terms x d,A.p,base x+d,v⟩

def leg (V : Config G n) := kinetic A.path A.clip A.p V
def background (V : Config G n) := A.path.inChannels A.clip A.p 0 V
def add (V : Config G n) (x d : ℝ) := (A.terms x d).additive A.p V

def residual (H : ℝ → Config G n → ℝ) (V : Config G n) (base : ℝ → ℝ) x d :=
    (base x+d) * A.leg V + A.background V + A.add V x d - contrast H V x

def install (H : ℝ → Config G n → ℝ) (base d : ℝ → ℝ) x := A.trial base x (d x) (scalar H x)

def shape (base : ℝ → ℝ) (U : Config G n) (x d : ℝ) := Real.exp (-((base x+d)*A.leg U + A.background U + A.add U x d)) *
    (A.terms x d).gas A.p U

lemma eval_trial (base : ℝ → ℝ) (x d v : ℝ) (U : Config G n) : (A.trial base x d v).eval U =
    Real.exp (v*sites n) * A.shape base U x d := by
  simp only [trial,Rep.eval,Rep.exponent,channels_split U (base x + d),leg,shape,background,add,← mul_assoc,← Real.exp_add]
  congr 2; unfold sites; ring

lemma shape_one (base : ℝ → ℝ) {x d : ℝ} (he : ∀ i, (A.terms x d).E i 1 = 0) : A.shape base 1 x d = 1 := by
  simp [shape,leg,background,add,gas_one _ _ (flags_one _),kinetic_one,loop_one,additive_one he]

lemma trial_one (base : ℝ → ℝ) {x d v : ℝ} (he : ∀ i, (A.terms x d).E i 1 = 0) : (A.trial base x d v).eval 1 =
    Real.exp (v*sites n) := by rw [eval_trial,shape_one A base he,mul_one]

variable {H : ℝ → Config G n → ℝ} {V : Config G n} {base d : ℝ → ℝ} {s t : Set ℝ} {μ x : ℝ}

lemma scalar_eq {d v : ℝ} (he : ∀ i, (A.terms x d).E i 1 = 0) (hv : (A.trial base x d v).eval 1 = H x 1) :
    scalar H x = v := by rw [scalar,← hv, A.trial_one base he,Real.log_exp,mul_div_cancel_right₀ v (sites_pos n).ne']

lemma contrast_eq {d v : ℝ} (he : ∀ i, (A.terms x d).E i 1 = 0) (hV : flags A.p.threshold V = ∅)
    (hv : (A.trial base x d v).eval 1 = H x 1) (hv' : (A.trial base x d v).eval V = H x V) :
    contrast H V x = (base x + d)*A.leg V + A.background V + A.add V x d := by
  rw [contrast,← hv, ← hv', A.trial_one base he,eval_trial, shape,gas_one _ _ hV,mul_one,← Real.exp_add,
    Real.log_exp,Real.log_exp]; ring

lemma eval_install {x : ℝ} (hx : 0 < H x 1) (U : Config G n) :
    (A.install H base d x).eval U = H x 1 * A.shape base U x (d x) := by
  rw [install,eval_trial,scalar, div_mul_cancel₀ _ (sites_pos n).ne', Real.exp_log hx]

/-- Components produced by just the scalar equations. -/
lemma passes (hV : flags A.p.threshold V = ∅) (he : ∀ i, (A.terms x (d x)).E i 1 = 0)
    (h0 : 0 < H x 1) (h1 : 0 < H x V) (hz : A.residual H V base x (d x) = 0) :
    (A.install H base d x).eval 1 = H x 1 ∧ (A.install H base d x).eval V = H x V := by
  simp only [residual] at hz
  simp only [eval_install _ h0,shape_one A base he,mul_one,true_and]
  rw [shape,gas_one _ _ hV,mul_one,sub_eq_zero.mp hz,contrast, neg_sub, Real.exp_sub, Real.exp_log h1,Real.exp_log h0]
  field_simp



/-- Example extra shape income: dominate the relative-to-flat error by the
single tested defect, *including* everywhere the gas is not identically one.

No bounds required uniform in U or across the schedule here; this price of decay as the
trial approaches a root has to be earned separately, not asserted from two
tests. -/
def ShapeControl (A : Template G n) (s t : Set ℝ) (H : ℝ → Config G n → ℝ) (V : Config G n) (base : ℝ → ℝ) :=
  ∀ x∈s, ∀ U : Config G n, ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ t,
    |A.shape base U x a - H x U / H x 1| ≤ C * |A.residual H V base x a|

lemma realizes (hc : ShapeControl A s t H V base) (hz : Zeroes s t (A.residual H V base) d) (hx : x∈s)
    (he : 0 < H x 1) : (A.install H base d x).eval = H x := funext fun U => by
  obtain ⟨C,_,ht⟩ := hc x hx U
  have h₀ : A.shape base U x (d x) = H x U / H x 1 :=
    eq_of_abs_sub_nonpos (by simpa only [hz.sol x hx,abs_zero,mul_zero] using ht _ (hz.admissible hx))
  rw [A.eval_install he,h₀]
  field_simp

/-- Sufficient conditions on actual template readings (strong monotone
response includes the already committed path contribution, so do not ask for
monotonicity in incoming bare beta). Works even for activities computed from
scalar-independent estimates by ignoring the dial. -/
lemma response (hm : 0 < μ) (hb : ContinuousOn base s)
    (hh : ContinuousOn (contrast H V) s) (hdial : ∀ x ∈ s, ContinuousOn (A.add V x) t)
    (hinput : ∀ e ∈ t, ContinuousOn (fun x => A.add V x e) s)
    (hg : ∀ x∈s, ∀ a∈t, ∀ b∈t, a ≤ b → -(A.leg V - μ)*(b-a) ≤ A.add V x b - A.add V x a) :
    Response s t μ (A.residual H V base) :=
  { margin := hm
    gain := fun x hx a ha b hb h => by unfold residual; linarith [hg x hx a ha b hb h]
    dial := fun x hx => ContinuousOn.sub (ContinuousOn.add (ContinuousOn.add
      ((continuousOn_const.add continuousOn_id).mul continuousOn_const) continuousOn_const) (hdial x hx)) continuousOn_const
    transport := fun a ha => ((((hb.add continuousOn_const).mul continuousOn_const).add continuousOn_const).add (hinput a ha)).sub hh }


end Template

variable {H : ℝ → Config G n → ℝ} {V : Config G n} {s : Set ℝ} {x : ℝ} {Z : ℝ → ℝ}





lemma contrast_continuous (hpos : ∀ x∈s, 0 < H x 1 ∧ 0 < H x V) (h0 : ContinuousOn (fun x => H x 1) s)
    (hV : ContinuousOn (fun x => H x V) s) : ContinuousOn (contrast H V) s :=
  (h0.log fun x hx => (hpos x hx).1.ne').sub (hV.log fun x hx => (hpos x hx).2.ne')
end YM.UVNext.CouplingReset
