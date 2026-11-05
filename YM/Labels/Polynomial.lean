import YM.Labels.Jet
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Complex reference labels on actual radial jets

We choose independent real coordinates in each
radial jet space, including the constraint.

Field powers are ordinary
monomials in these coordinates; invariance is imposed on the *whole* polynomial.

We can use an unbounded product for evaluations since each polynomial has finite support.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Labels
open Function Set
open scoped BigOperators Topology

abbrev dim (G : Gauge) (j : ℕ) := Module.finrank ℝ (Taylor G j)

def axes (G : Gauge) (j : ℕ) : Module.Basis (Fin (dim G j)) ℝ (Taylor G j) := Module.finBasis ℝ _

abbrev Key (G : Gauge) := (i : ℕ) × Fin (dim G i)
abbrev Jet (G : Gauge) := (j : ℕ) → Taylor G j
abbrev Pol (G : Gauge) := MvPolynomial (Key G) ℂ

variable {G : Gauge}

def coord (A : Jet G) (v : Key G) : ℂ := (((axes G v.1).repr (A v.1)) v.2 : ℝ)

def read (A : Jet G) : Pol G →ₐ[ℂ] ℂ := MvPolynomial.aeval (coord A)

/-- No phantom labels even though evaluations are on the *real* jets. -/
theorem eval_ext (p q : Pol G) (h : ∀ A, read A p = read A q) : p = q := by
  let R (k : Key G) := Set.range (fun x : ℝ => (x : ℂ))
  have hr (k : Key G) : (R k).Infinite := Set.infinite_range_of_injective Complex.ofReal_injective
  apply MvPolynomial.funext_set R hr
  intro x hx
  choose y hy using fun k => show ∃ t : ℝ, (t : ℂ) = x k from hx k (Set.mem_univ k)
  let A (j : ℕ) := (axes G j).equivFun.symm (fun i => y ⟨j,i⟩)
  rw [show x = coord A by
    funext k
    change x k = (((axes G k.1).equivFun (A k.1) k.2 : ℝ) : ℂ)
    unfold A; rw [LinearEquiv.apply_symm_apply]; exact (hy k).symm]
  exact h A

def generation (k : Key G) : ℕ := k.1 + 2

def bidegree (k : Key G) : ℕ × ℕ := (generation k, 1)

def height (p : Key G →₀ ℕ) := Finsupp.weight generation p

def pureDegree (p : Pol G) (r f : ℕ) := MvPolynomial.IsWeightedHomogeneous bidegree p (r,f)

/-- Through engineering weight `d` (total, not per factor). -/
def limited (G : Gauge) (d : ℕ) : Submodule ℂ (Pol G) :=
  MvPolynomial.restrictSupport ℂ {b | height b ≤ d}

theorem cap_finite (G : Gauge) (d : ℕ) : Set.Finite {b : Key G →₀ ℕ | height b ≤ d} := by
  classical
  let A := {b : Key G →₀ ℕ | height b ≤ d}
  let P := (i : Fin (d+1)) × Fin (dim G i.val)
  let u (i : P) : Key G := ⟨i.1.val,i.2⟩
  have hu (i : Key G) (f : A) : f.val i * generation i ≤ d := calc
    _ ≤ height f.val := by
      by_cases h : f.val i = 0
      · simp [h]
      unfold height
      rw [Finsupp.weight_apply, Finsupp.sum]
      exact Finset.single_le_sum (f := fun x => f.val x • generation x)
        (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.mpr h)
    _ ≤ d := f.property
  have he (i) : 1 ≤ generation (G := G) i := by unfold generation; omega
  have hy (i) (f : A) : f.val i ≤ d :=
    (show f.val i ≤ f.val i * generation i by
      exact le_mul_of_one_le_right (Nat.zero_le _) (he i)).trans (hu i f)
  let e (f : A) (i : P) : Fin (d+1) := ⟨f.val (u i), Nat.lt_succ_of_le (hy _ _)⟩
  apply (Finite.of_injective (fun (f : A) => e f) ?_ : Finite A)
  intro b c h
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hv : i.1 < d+1
  · exact congr_arg Fin.val (congr_fun h ⟨⟨i.1,hv⟩,i.2⟩)
  have hz (a : A) : a.val i = 0 := by
    by_contra! wn
    have H := show generation i ≤ d from
      (le_mul_of_one_le_left (Nat.zero_le _) (show 1 ≤ a.val i by omega)).trans (hu i a)
    unfold generation at H; omega
  rw [hz, hz]

instance limited_finite (G : Gauge) (d : ℕ) : FiniteDimensional ℂ (limited G d) := by
  haveI : Finite {b : Key G →₀ ℕ | height b ≤ d} := cap_finite G d
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ {b : Key G →₀ ℕ | height b ≤ d})

/-- Ad on each jet, preserving the order. -/
def colored (u : G.El) (A : Jet G) : Jet G := fun i ↦ Taylor.paint u (A i)

def invariantSpace (G : Gauge) : Submodule ℂ (Pol G) where
  carrier := {p | ∀ A : Jet G, ∀ u, read (colored u A) p = read A p}
  zero_mem' := by simp
  smul_mem' z p h A u := by rw [map_smul, h A u, map_smul]
  add_mem' {p q} hp hq A u := by rw [map_add, hp A u, hq A u, map_add]

def localFields (G : Gauge) (d : ℕ) := limited G d ⊓ invariantSpace G

/-- Physical reference labels (before dynamical mixing and all-spectator quotient). -/
abbrev Label (G : Gauge) (d : ℕ) := ↥(localFields G d)

instance labels_finite (d : ℕ) : FiniteDimensional ℂ (Label G d) := by
  refine FiniteDimensional.of_injective
    (Submodule.inclusion (show localFields G d ≤ limited G d from inf_le_left))
    (Submodule.inclusion_injective _)

def raiseLabel (G : Gauge) {d e : ℕ} (h : d ≤ e) : Label G d →ₗ[ℂ] Label G e :=
  Submodule.inclusion (inf_le_inf_right _ <| MvPolynomial.restrictSupport_mono _ fun _ hk ↦ le_trans hk h)

def unit (G : Gauge) (d : ℕ) : Label G d := ⟨1, by
  constructor
  · change 1 ∈ limited G d
    rw [limited, MvPolynomial.mem_restrictSupport_iff]
    simp [Set.singleton_subset_iff, height]
  intro A u; simp ⟩

end YM.Labels
