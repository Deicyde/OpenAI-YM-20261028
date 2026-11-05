import YM.Labels.Reference
import YM.RG.Masks
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Physical lattice section normalization

Fix one stencil and section per d,
independent of the tori.

Choose also actual parallel transport for computing
`Π_o`; we show there is no choice ambiguity, via `SolvesLink.unique`.

The ODE existence proof is in a separate module.

Radial substitution
uses exactly the jets of weight through d, as necessary through Taylor
order d.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Source
open Labels Lattice Wilson RG Function Set MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge}

/-- Polynomial radial potential of Taylor components through weight d (degree a-1). -/
def potential (d : ℕ) (J : Jet G) (i : Axis) (x : E4) : G.Color :=
  ∑ j ∈ Finset.range (d-1), (J j).value i x

def partConnection (d : ℕ) (J : Jet G) (h : ℝ) (l : Edge Cover) (t : ℝ) :=
  h • potential d J l.2 (h • (WithLp.toLp 2 (fun i => (l.1 i : ℝ)) + t • basis l.2))

/-- Use matrix transport along positive links, with the convention giving the
signs of `G.ad` later in the nonlinear curvature. -/
def SolvesLink (u : ℝ → G.El) (A : ℝ → G.Color) := u 0 = 1 ∧
    ∀ t, HasDerivAt (fun x => G.mat (u x)) (G.mat (u t) * G.colorMat (A t)) t

theorem SolvesLink.unique {u v : ℝ → G.El} {A} (h : SolvesLink u A) (e : SolvesLink v A) : u = v := by
  let w (t : ℝ) := G.mat (u t) * star (G.mat (v t))
  have he (t) : HasDerivAt w 0 t := by
    have hd := (h.2 t).mul (e.2 t).star
    simpa [w,G.colorMat_skew, Pi.mul_def, mul_assoc] using! hd
  have hs (t) : w t = 1 := calc
    w t = w 0 := is_const_of_deriv_eq_zero (fun x ↦ (he x).differentiableAt) (fun x ↦ (he x).deriv) t 0
    _ = 1 := by simp [w,h.1,e.1]
  funext t
  have hv := show u t * (v t)⁻¹ = 1 from G.mat_injective (by rw [G.mat_one,G.mat_mul,G.mat_inv]; exact hs t)
  exact mul_inv_eq_one.mp hv

/-- Ordinary analysis producer type. -/
structure Hol (G : Gauge) where
  flow (d : ℕ) (J : Jet G) (h : ℝ) (l : Edge Cover) : ℝ → G.El
  solves d J h l : SolvesLink (flow d J h l) (partConnection d J h l)

namespace Hol
variable (A : Hol G)

def links (d : ℕ) (J : Jet G) (h : ℝ) : CoverConfig G := fun l => A.flow d J h l 1

theorem flat (d : ℕ) (J : Jet G) : A.links d J 0 = 1 := by
  funext l
  have H : SolvesLink (1 : ℝ → G.El) (partConnection d J 0 l) := by
    refine ⟨rfl, fun t => ?_⟩
    simp [partConnection]
    exact hasDerivAt_const t 1
  rw [links, (A.solves d J 0 l).unique H]; rfl

/-- The unhatted lifted links at a torus placement o for `Pi_o`; use
only with nonwrapping stencil. Other link values don't enter. -/
def testLinks (d : ℕ) {n : Side} (o : Site n) (J : Jet G) (h : ℝ) : Config G n :=
    fun l => A.links d J h (Lattice.lift (l.1-o),l.2)

def PiVanish (d : ℕ) {n : Side} (o : Site n) (F : Config G n → ℂ) :=
    ∀ J : Jet G, let f := fun h => F (A.testLinks d o J h)
                 ContDiffAt ℝ (d : ℕ∞) f 0 ∧ ∀ k ≤ d, iteratedDeriv k f 0 = 0
end Hol

def scaleJet (J : Jet G) (t : ℝ) : Jet G := fun i => (t^(i+2)) • J i

/-- Read of log Taylor is matched component-wise, not a chosen Gram fit in the IR. -/
def Projects {d : ℕ} (H : Hol G) (p : Label G d) (F : CoverConfig G → ℂ) := ∀ J : Jet G,
    let f := fun h => F (H.links d J h)
    let g := fun h => read (scaleJet J h) p.val
    ContDiffAt ℝ (d : ℕ∞) f 0 ∧ ContDiffAt ℝ (d : ℕ∞) g 0 ∧
      ∀ k ≤ d, iteratedDeriv k f 0 = iteratedDeriv k g 0

/-- Polynomial cylinders on a fixed stencil (entry variables include conjugate). -/
abbrev UsedEdges (S : Finset Cover) := {x : Edge Cover // x.1 ∈ S ∧ x.1 + step x.2 ∈ S}
abbrev Index (G : Gauge) (S : Finset Cover) := UsedEdges S × Fin G.repDim × Fin G.repDim × Bool

def entry {S : Finset Cover} (U : CoverConfig G) (k : Index G S) :=
  let z := G.mat (U k.1.val) k.2.1 k.2.2.1
  if k.2.2.2 then star z else z

abbrev Formula (G : Gauge) (S : Finset Cover) := MvPolynomial (Index G S) ℂ

variable {d : ℕ} {F : Frame G d}

structure SectionData (F : Frame G d) where
  stencil : Finset Cover
  evalC : F.Coeff →ₗ[ℂ] Formula G stencil

namespace SectionData
variable (C : SectionData F)

def evaluate (c : F.Coeff) (U : CoverConfig G) := MvPolynomial.aeval (entry U) (C.evalC c)

def places {n : Side} (c : F.Coeff) (o : Site n) (U : Config G n) := C.evaluate c (expandAt o U)

def footprint {n : Side} (o : Site n) := C.stencil.image fun x => wrap n x + o

@[simp] theorem places_trans {n : Side} c (o b : Site n) U :
    C.places c o (translate b U) = C.places c (o+b) U := by
  rw [places, places, show expandAt o (translate b U) = expandAt (o+b) U by
    funext e
    simp only [expandAt, translate, add_assoc]]

theorem cylinder_local (c : F.Coeff) : LocalOn C.stencil (C.evaluate c) := by
  intro U V h
  unfold evaluate
  rw [show entry (S := C.stencil) U = entry V by
    funext k; unfold entry; rw [h _ k.1.property.1 k.1.property.2]]

theorem placed_local {n : Side} (o : Site n) (c : F.Coeff) : LocalOn (C.footprint o) (C.places c o) := by
  simpa only [footprint, Finset.coe_image, places, Function.comp_def] using! (LocalOn.expandAt (C.stencil : Set Cover)
    (C.evaluate c) (C.cylinder_local c) o)

theorem eval_linear : IsLinearMap ℂ C.evaluate := by
  constructor
  · intro a b; funext x
    simp [evaluate]
  · intro a b; funext x
    simp only [evaluate,map_smul,Pi.smul_apply]

/-- Stencil smoothness/canonical budgets at actual step cutoffs are separate. -/
structure Sound (H : Hol G) : Prop where
  anchored : 0 ∈ C.stencil
  stable (s : Signed) : C.stencil.image s.act = C.stencil
  gaugeInvariant (c) : GaugeInvariant (C.evaluate c)
  unit : C.evaluate F.e0 = 1
  Hpart (s : Signed) c U : C.evaluate c (pull s 0 U) = C.evaluate (F.act s.ortho c) U
  ordinary_real c U : C.evaluate (star c) U = star (C.evaluate c U)
  projects (c) : Projects H (F.coords.symm c) (C.evaluate c)

theorem placed_invariant {H : Hol G} (h : C.Sound H) {n} (o : Site n) (c : F.Coeff) :
    GaugeInvariant (C.places c o) := by
  intro k U
  rw [places, expandAt_gauge]; exact h.gaugeInvariant c _ _

theorem placed_signed {H : Hol G} (h : C.Sound H) {n : Side} (s : Signed) (o b : Site n)
    (c : F.Coeff) (U) : C.places c o (pull s b U) = C.places (F.act s.ortho c) (affine s b o) U := by
  rw [places, expandAt_pull, h.Hpart]
  rfl

theorem continuous_evaluate (c : F.Coeff) : Continuous (C.evaluate c) := by
  have he : Continuous fun U : CoverConfig G => (entry U : Index G C.stencil → ℂ) := by
    refine continuous_pi fun i ↦ ?_
    unfold entry
    cases i.2.2.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact (C.evalC c).continuous_eval.comp he

theorem continuous_places {n : Side} (c : F.Coeff) (o : Site n) : Continuous (C.places c o) :=
  (C.continuous_evaluate c).comp (show Continuous (expandAt o (K := G.El)) by unfold expandAt; fun_prop)
end SectionData
end YM.Source
