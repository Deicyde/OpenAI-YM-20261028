import YM.Marker.Truncated

/-!
# Marked occurrences interface

Complex sources. This level is relative to unnormalized Haar. Vacuum fixed,
not dividing marking by densities. Data in Prop typed QUERIES and footprint.
This Overlay format for proofs using extended populations doesn't include
by itself provenance for different 
source-marker *comparisons* or their analytic branches. Need those separately!
Simple exact identity equality across outputs of an alg still requires that
producers assemble THESE full physical functions. See
slots before reinterpreting identifications as `part x Singleton`. 

Empty padding: mark false by carrying zero coefficients with a MENTIONED
nonempty term. In the stopping-norm arguments we'll always have ≥one marker.
Even a permitted selection may represent only one coefficient; still record
all-origin multiplicity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Overlay
open Function Marker RG Lattice Wilson MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}

/-- raw family level -/
structure Bands (R : Census V) (P : Rep G n) where
  origins : V → Site n
  units : V → ℂ
  support : ℕ → Support n
  rays : ℕ → R.Mode
  H : ℕ → Config G n → ℂ
  marks : ℕ → ℕ → R.Mode
  entries : ℕ → ℕ → Config G n → ℂ

namespace Bands
variable {P : Rep G n} (a : Bands R P)

structure Active : Prop where
  proper i : (a.rays i).val.Nonempty
  pins i j : j∈ (a.rays i).val → a.origins j ∈ a.support i
  regular i : P.p.Regular (a.support i) (a.H i)
  occurs i j : (a.marks i j).val.Nonempty
  retained i j : a.entries i j ≠ 0 →
    ∀ s∈(a.marks i j).val,a.origins s∈ (P.activities.forced i).support
  inspects i j : UsesFinal P.p.threshold (P.activities.forced i).support (a.entries i j)
  keeps i j (x : Config G n) : a.entries i j x≠0 → (P.activities.forced i).eligible P.p.threshold x
  meas i j : Measurable (a.entries i j)
  invi i j : GaugeInvariant (a.entries i j)

/-- raw capacities (nonfactorial price chosen; any recovered versions from
factorial envelopes must pay accordingly). Units billed at evaluation only.
May increase coarse costs before reducing to this interface for end measure.
Exponents/supports fixed in trajectory here. -/
structure Radial (w : V → ℝ) (u c d b : ℝ) : Prop where
  pure i : 0<w i
  localU : ∀ i, w i * ‖a.units i‖ ≤ u
  factor : 0<b
  bulk : ∃ t : ℕ → ℝ, (∀ i,0≤t i ∧ ∀ x∈ (a.rays i).val,
      P.p.supBounds (a.origins x) (a.support i) (a.H i) (t i)) ∧
    ∀ i : V, SumBudget (fun j => if i∈ (a.rays j).val then Poly.toll w (a.rays j)*P.p.mass (a.support j) (t j) else 0) c
  hits : ∃ t : ℕ × ℕ → ℝ, (∀ i j, 0≤t (i,j) ∧ ∀ x, ‖a.entries i j x‖ ≤ t (i,j)) ∧
    ∀ i : V, SumBudget (fun k => if i∈ (a.marks k.1 k.2).val then
      Poly.toll w (a.marks k.1 k.2)*P.p.mass (P.activities.forced k.1).support (t k) else 0) (d*b)

/-- Physical exponent append. Not counting erased addresses as separate.
Keep vacuum outside. -/
def ray (i : ℕ) (U : Config G n) := Poly.send (a.rays i) (masked P.p.threshold (a.support i) (a.H i) U)
def extra (U : Config G n) := (∑ i : V, Poly.send (R.fire i) (a.units i))+∑' i,a.ray i U

def tagged (i j : ℕ) (U : Config G n) := Poly.send (a.marks i j) (a.entries i j U)
def each (i : ℕ) (U : Config G n) := Poly.send R.quiet (P.activities.K i U:ℂ) + ∑' j,a.tagged i j U

def packet (l : Finset ℕ) (U : Config G n) : Poly R := by
  classical
  exact if P.activities.admissible P.p U l then ∏ i∈l,a.each i U else 0

def cluster (U : Config G n) : Poly R := ∑' l,a.packet l U

def density (U : Config G n) : Poly R := (Real.exp (P.exponent U):ℂ) •
    (Poly.pass (a.extra U)*a.cluster U)

omit [Fintype V] in
@[fun_prop] lemma sends (i : R.Mode) : Continuous (Poly.send i) := by
  change Continuous (fun x : ℂ => (Pi.single i x : R.Mode → ℂ)); apply continuous_pi; intro y
  simp_rw [Pi.single_apply]; split <;> fun_prop

@[fun_prop] lemma extra_meas (h : a.Active) : Measurable a.extra := by
  unfold extra
  refine Measurable.add measurable_const (Measurable.tsum fun i => ?_)
  exact ((sends _).measurable).comp (masked_measurable _ _ _ (h.regular i).borel)

omit [Fintype V] in
lemma cluster_meas (h : a.Active) {δ w} (H : P.activities.Valid P.p δ w) : Measurable a.cluster := by
  unfold cluster; refine Measurable.tsum fun i => ?_
  unfold packet; refine Measurable.ite (P.activities.admissible_borel P.p i) (Finset.measurable_fun_prod _ fun j _ => ?_) measurable_const
  unfold each; refine Measurable.add ((sends _).measurable.comp (Complex.continuous_ofReal.measurable.comp (H.forced.meas j)))
    (Measurable.tsum fun k => ?_)
  exact (sends _).measurable.comp (h.meas j k)

lemma density_meas (h : a.Active) {σ C Λ δ w} (H : P.Lawful σ C Λ δ w) : Measurable a.density := by
  unfold density
  refine Measurable.smul (Complex.continuous_ofReal.measurable.comp (P.exponentEnv H).exp.meas)
    ((Poly.pass_cont.measurable.comp (a.extra_meas h)).mul (a.cluster_meas h H.labels))
end Bands
end YM.Overlay
