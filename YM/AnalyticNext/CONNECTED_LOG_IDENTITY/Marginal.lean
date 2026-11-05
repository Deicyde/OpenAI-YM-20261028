import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Merge
import YM.Next.BOUNDARY.Core
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Org.Theatre
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Work.A05
import YM.Work.A15
import YM.Work.B04

set_option warningAsError false

/-!
# Factor the integrals; two usable interfaces

- Arbitrary reference law even per whole spell; keep only the USED
  component arguments. No assumption of independence from footprints
  per se. Require a checked marginal input (push to block arguments =
  product of each isolated component's marginal), e.g. suitable for
  conditionals with block-diagonal covariances.
- Concrete product probability inputs grouped by physical address and
  home site. Here prove the marginal test from actual disjointness;
  even the isolated component cost can be evaluated as an ordinary
  whole-space product expectation, with *the very same* θ-site laws
  including on unused tags.

Doesn't tell how to earn per-component estimates from extensive
bounds. Does, for example, tell how to deduce full absolute-integral
convergence from appropriately reserved per-component estimates and
Trees.Ready without a circular fcrec invocation. .
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Marginal
open Lattice Wilson RG MeasureTheory Function Finset AbsoluteSums Trees
open scoped BigOperators Topology Classical ENNReal
variable {n : Side} {ι : Type*}



section Varying
variable {World : Finset ι → Type*} [∀ s, MeasurableSpace (World s)]
variable (X I : ι → Support n) (D : Support n) (test : ι → Finset ι → Prop) (μ : ∀ s,Measure (World s))
variable {Coord : Species X → Type*} [∀ i,MeasurableSpace (Coord i)] (M : ∀ i, Measure (Coord i)) [∀ i,SigmaFinite (M i)]
variable (atAddress : ∀ s, ∀ i : ↥(explode X s), World s → Coord i.val)
    (f : ∀ i, Coord i → ℝ) (total : ∀ s, World s → ℝ)

/-- Absolute estimates can be attempted per eligible component BEFORE
solving the global disintegration. Point & marginal producer obligations,
only need those where the spelling is allowed. They include the case
of the empty spelling where no flags. -/
structure Keep : Prop where
  block : ∀ s : Finset ι, s.biUnion I = D → internal X test s →
    MeasurePreserving (fun z : World s => fun i => atAddress s i z) (μ s)
      (Measure.pi (fun i : ↥(explode X s) => M i.val))
  compute : ∀ s : Finset ι, s.biUnion I = D → internal X test s → ∀ x,
    total s x = ∏ i : ↥(explode X s), f i.val (atAddress s i x)
  earned : ∀ p, internal X test p.val → ground X p ∩ D = owned X I p → Integrable (f p) (M p)





open  Ursell  


end Varying

section Letters
variable (X : ι → Support n)
    {τ : Type*} {α : τ → Type*} [∀ i, MeasurableSpace (α i)] [Fintype τ]
    (place : τ → Site n)

abbrev W := ∀ i,α i
-- Note include unused positions at the same home site
abbrev Here (P : Support n) := {i : τ // place i ∈ P}
abbrev Read (P : Support n) := ∀ i : Here place P,α i.val

/-- Evaluate on all words. Value of a letter can be computed on its
complete footprint; it may depend on the *view* of that letter in this
spell (which can answer eligibility and table lookups). -/
def over (w : ∀ i : ι, Finset ι → Read (α:=α) place (X i) → ℝ) (s : Finset ι) (t : W (α:=α)) :=
  ∏ i∈s,w i (view X s i) (fun j => t j.val)

/-- Isolated component density. Keep even query answers determined by
selections (restricting to this component gives the same answers). -/
def under (w : ∀ i : ι, Finset ι → Read (α:=α) place (X i) → ℝ)
    (p : Species X) (t : Read (α:=α) place (ground X p)) :=
  ∏ i : ↥p.val, w i.val (view X p.val i) (fun j => t ⟨j.val,species_ground X i.property j.property⟩)

def splitWorld (s : Finset ι) (t : W (α:=α)) (i : ↥(explode X s)) : Read (α:=α) place (ground X i.val) :=
  fun j => t j.val

omit [(i : τ) → MeasurableSpace (α i)] [Fintype τ] in
lemma read_inside (w : ∀ i : ι, Finset ι → Read (α:=α) place (X i) → ℝ)
    (p : Species X) (x : W (α:=α)) :
    (∏ i∈p.val,w i (view X p.val i) (fun j => x j.val)) = under X place w p (fun j => x j.val) := by
  unfold under; rw [← prod_subtype p.val (p:=(·∈p.val)) (fun _ => Iff.rfl)
    (fun i => w i (view X p.val i) (fun j => x j.val))]

omit [(i : τ) → MeasurableSpace (α i)] [Fintype τ] in
lemma located (w : ∀ i : ι, Finset ι → Read (α:=α) place (X i) → ℝ)
    (s : Finset ι) (x : W (α:=α)) :
    over X place w s x = ∏ i : ↥(explode X s), under X place w i.val (splitWorld X place s x i) := by
  unfold over splitWorld
  rw [per_component X s (fun i j => w i j (fun k => x k.val)), prod_subtype (explode X s) (p:=(·∈explode X s)) (fun _ => Iff.rfl)]
  apply prod_congr rfl; intro i hi
  exact read_inside X place w i.val x

variable (μ : ∀ i,Measure (α i)) [∀ i,IsProbabilityMeasure (μ i)]









omit [Fintype τ] in
lemma under_meas (w : ∀ i : ι, Finset ι → Read (α:=α) place (X i) → ℝ)
    (hm : ∀ i s, Measurable (w i s)) (p : Species X) : Measurable (under X place w p) := by
  unfold under; refine Finset.measurable_fun_prod _ fun i _ => (hm i.val _).comp
    (measurable_pi_lambda _ fun j => measurable_pi_apply _)

omit [Fintype τ] in
lemma over_meas (w : ∀ i : ι, Finset ι → Read (α:=α) place (X i) → ℝ) (hm : ∀ i s, Measurable (w i s))
    (s : Finset ι) : Measurable (over X place w s) := by
  unfold over; apply Finset.measurable_fun_prod; intro i _
  exact (hm i _).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)





end Letters
end YM.Push.LogIdentity.Marginal
