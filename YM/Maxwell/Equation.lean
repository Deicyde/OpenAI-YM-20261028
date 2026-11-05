import YM.Maxwell.Shell
import YM.Labels.Action

/-!
# Free equation variables before the separated quotient

Invariant polynomials from radial real jets, by actual linear substitution
to closed curvature and Maxwell shell. No dynamic labels used in these
polynomials. This realizes imposing linear equations by evaluation on
on-shell jet variables (as a linear constraint, including inside monomials).
Does not assume an equation-ideal/detection theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Function Set
open scoped TensorProduct

variable {G : Gauge}

abbrev legDim (G : Gauge) (j : ℕ) := Module.finrank ℝ (Shell G j)
abbrev Slot (G : Gauge) := (i : ℕ) × Fin (legDim G i)
abbrev TaylorTower (G : Gauge) := (i : ℕ) → Shell G i
abbrev WickPol (G : Gauge) := MvPolynomial (Slot G) ℂ

def frame (G : Gauge) (j : ℕ) : Module.Basis (Fin (legDim G j)) ℝ (Shell G j) :=
  Module.finBasis ℝ _

def coord (A : TaylorTower G) (i : Slot G) : ℝ := (frame G i.1).repr (A i.1) i.2

def probe (A : TaylorTower G) : WickPol G →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun i => (coord A i : ℂ)

theorem equalPol (p q : WickPol G) (He : ∀ A, probe A p = probe A q) : p = q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun x : ℝ => (x : ℂ))) fun _ =>
    infinite_range_of_injective Complex.ofReal_injective
  intro x hx
  choose y hy using fun k => hx k (mem_univ k)
  let A (j) := (frame G j).equivFun.symm (fun i => y ⟨j,i⟩)
  rw [show x = fun i => (coord A i : ℂ) by
    funext i
    change x i = (((frame G _).equivFun (A _) i.2 : ℝ) : ℂ)
    unfold A; rw [LinearEquiv.apply_symm_apply]; exact (hy i).symm]
  exact He A

/-- The actual substitution of the constrained jets in label coordinates. -/
def reduceEq : Labels.Pol G →ₐ[ℂ] WickPol G :=
  MvPolynomial.aeval fun i : Labels.Key G => ∑ j : Fin (legDim G i.1),
    MvPolynomial.C (((Labels.axes G i.1).repr (gaugeJet (frame G i.1 j)) i.2 : ℝ) : ℂ) *
      MvPolynomial.X ⟨i.1,j⟩

theorem jet_eval (X : TaylorTower G) : (probe X).comp reduceEq = Labels.read (fun i => gaugeJet (X i)) := by
  ext i
  simp only [AlgHom.comp_apply, reduceEq,MvPolynomial.aeval_X, map_sum, map_mul, probe, Labels.read,
    MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  unfold coord Labels.coord
  change ∑ j : Fin (legDim G i.1), _ * (((frame G i.1).repr (X i.1) j : ℝ) : ℂ) =
    ((((Labels.axes G i.1).repr (gaugeJet (X i.1))) i.2 : ℝ) : ℂ)
  conv_rhs => rw [← (frame G i.1).sum_repr (X i.1)]
  simp only [map_smul, map_sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul]; apply Finset.sum_congr rfl; intro j _; rw [mul_comm]

theorem jet_value (X : TaylorTower G) (p : Labels.Pol G) : probe X (reduceEq p) =
    Labels.read (fun i => gaugeJet (X i)) p := DFunLike.congr_fun (jet_eval X) p

def observable (G : Gauge) (d : ℕ) : Labels.Label G d →ₗ[ℂ] WickPol G :=
  reduceEq.toLinearMap.comp (Labels.localFields G d).subtype

/-- the subspace set to zero by imposing Maxwell equations in labels.
No assumption here that there are no further separated nulls or that this is
any particular presentation by invariant contractions. -/
def equationIdeal (G : Gauge) (d : ℕ) := LinearMap.ker (observable G d)

theorem ideal_meaning {d : ℕ} {A : Labels.Label G d} : A ∈ equationIdeal G d ↔
    ∀ X : TaylorTower G, Labels.read (fun i => gaugeJet (X i)) A.val = 0 := by
  change reduceEq A.val = 0 ↔ _
  constructor
  · intro h X; rw [← jet_value X, h, map_zero]
  intro h; exact equalPol _ _ (by intro X; rw [jet_value, h,map_zero])

/-- Linear symbol for one leg, which need not be invariant. -/
def symbol (j : ℕ) (lam : Shell G j →ₗ[ℝ] ℝ) : WickPol G :=
  ∑ i, MvPolynomial.C ((lam (frame G j i) : ℝ) : ℂ) * MvPolynomial.X ⟨j,i⟩

theorem symbol_test (X : TaylorTower G) (j : ℕ) (lam : Shell G j →ₗ[ℝ] ℝ) :
    probe X (symbol j lam) = (lam (X j) : ℂ) := by
  conv_rhs => rw [← (frame G j).sum_repr (X j)]
  simp only [map_sum,map_smul, smul_eq_mul,symbol,probe,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, map_mul, coord,Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def coordinateLeg (i : Slot G) : Shell G i.1 →ₗ[ℝ] ℝ := (frame G i.1).coord i.2

theorem symbol_coordinate (i : Slot G) : symbol i.1 (coordinateLeg i) = MvPolynomial.X i :=
  equalPol _ _ (by intro A; rw [symbol_test,probe,MvPolynomial.aeval_X]; rfl)
end YM.Maxwell
