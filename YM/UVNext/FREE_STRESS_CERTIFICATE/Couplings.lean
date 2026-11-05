import YM.Maxwell.Bilinear
import YM.UVNext.FREE_STRESS_CERTIFICATE.Components


/-! Polynomial labels for bilinear curl invariants, on the same unrenormalized
radial jets used by `Register`, with actual shell substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Labels Tensor Maxwell Function MvPolynomial
open scoped RealInnerProductSpace
variable {G : Gauge} {j l d : ℕ}

def mono (p : Place j) (i : G.ColorIndex) : Pol G :=
  ∑ k, C (((component p (axes G j k) i) : ℝ) : ℂ) * X ⟨j,k⟩

theorem eval_mono (p : Place j) (i : G.ColorIndex) (A : Jet G) :
    Labels.read A (mono p i) = ((component p (A j) i : ℝ) : ℂ) := by
  unfold mono
  rw [map_sum]
  conv_rhs => rw [← (axes G j).sum_repr (A j)]
  simp only [Labels.read, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    map_sum, map_smul, WithLp.ofLp_sum,Finset.sum_apply, PiLp.smul_apply, Labels.coord, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..

theorem graded_mono (p : Place j) (i : G.ColorIndex) :
    MvPolynomial.IsWeightedHomogeneous generation (mono p i) (j+2) :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun (k : Fin (Labels.dim G j)) _ => (MvPolynomial.isWeightedHomogeneous_X ℂ generation (⟨j,k⟩ : Key G)).C_mul _)

def tape (p : Place j) (q : Place l) : Pol G :=
  ∑ i : G.ColorIndex, mono p i * mono q i

theorem color_dot (x y : G.Color) : inner ℝ x y = ∑ c : G.ColorIndex, x c * y c := by
  rw [real_inner_comm y x, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]; rfl

theorem eval_tape (p : Place j) (q : Place l) (A : Jet G) :
    Labels.read A (tape p q) = (inner ℝ (component p (A j)) (component q (A l)) : ℂ) := by
  simp only [tape, map_sum, map_mul, eval_mono, color_dot, Complex.ofReal_sum,Complex.ofReal_mul]

theorem graded_tape (p : Place j) (q : Place l) : MvPolynomial.IsWeightedHomogeneous generation
    (tape (G:=G) p q) (j+l+4) := by
  rw [show j+l+4=j+2+(l+2) by omega]
  exact MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun i _ => (graded_mono p i).mul (graded_mono q i))

theorem adjoint_is_inner (x y : G.Color) (u : G.El) :
    inner ℝ (G.adjoint u x) (G.adjoint u y) = inner ℝ x y := by
  have h := norm_add_sq_real (G.adjoint u x) (G.adjoint u y)
  rw [← map_add] at h
  simp only [G.norm_adjoint, norm_add_sq_real x y] at h
  linarith

def bond (p : Place j) (q : Place l) (h : j+l+4 ≤ d) : Label G d := ⟨tape p q,
  by
    constructor
    · change tape p q ∈ limited G d
      refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr ?_
      intro b hb
      change Finsupp.weight generation b ≤ d
      rw [graded_tape p q (MvPolynomial.mem_support_iff.mp hb)]
      exact h
    intro A u
    simp_rw [eval_tape,colored,component_paint, adjoint_is_inner]⟩

@[simp] theorem bond_real (p : Place j) (q : Place l) (h : j+l+4 ≤ d) :
    realBar (bond (G:=G) p q h) = bond p q h := by
  apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (Labels.conjPol (tape p q)) = _
  change _ = Labels.read A (tape p q)
  simp [Labels.conj_value, eval_tape]

def curlProbe (p : Place j) (i : G.ColorIndex) : Maxwell.Probe G j :=
  Maxwell.constrain (Maxwell.fromF G (YM.basis ∘ p.2) i p.1.1 p.1.2)

theorem actual_shell (p : Place j) (i : G.ColorIndex) :
    Maxwell.reduceEq (mono p i) = Maxwell.symbol j (curlProbe p i) := by
  apply Maxwell.equalPol; intro A
  rw [Maxwell.jet_value, eval_mono, Maxwell.symbol_test]
  change (↑(Maxwell.takeCurl (Maxwell.gaugeJet (A j)) p.1.1 p.1.2 (YM.basis ∘ p.2) i):ℂ) = _
  rw [Maxwell.match_leg]; rfl

theorem shell_bond (p : Place j) (q : Place l) (h : j+l+4 ≤ d) :
    Maxwell.observable G d (bond p q h) = ∑ i : G.ColorIndex,
      Maxwell.symbol j (curlProbe p i) * Maxwell.symbol l (curlProbe q i) := by
  change Maxwell.reduceEq (tape p q) = _
  simp [tape, map_mul, actual_shell]

-- Ordinary derivative names through orders zero and one (no factorial factors here).
abbrev initialPlace (a b : Axis) : Place 0 := ((a,b),Fin.elim0)
abbrev gradientPlace (a b k : Axis) : Place 1 := ((a,b),fun _ => k)

def ff (G : Gauge) (d : ℕ) (h : 4 ≤ d) (a b c e : Axis) : Label G d := bond (initialPlace a b) (initialPlace c e) h
def fq (G : Gauge) (d : ℕ) (h : 5 ≤ d) (a b c e r : Axis) : Label G d := bond (initialPlace a b) (gradientPlace c e r) h

def flipPlace (p : Place j) : Place j := ((p.1.2,p.1.1),p.2)

theorem component_skew (p : Place j) (A : Taylor G j) :
    component (flipPlace p) A = - component p A := by
  simp [component,flipPlace,Maxwell.takeCurl,smul_sub]

theorem bond_left (p : Place j) (q : Place l) (h : j+l+4 ≤ d) :
    bond (G:=G) (flipPlace p) q h = - bond p q h := by
  apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (tape (flipPlace p) q) = Labels.read A (- tape p q)
  simp [eval_tape,component_skew]

theorem bond_right (p : Place j) (q : Place l) (h : j+l+4 ≤ d) :
    bond (G:=G) p (flipPlace q) h = - bond p q h := by
  apply Subtype.ext; apply Labels.eval_ext; intro A
  change Labels.read A (tape p (flipPlace q)) = Labels.read A (- tape p q)
  simp [eval_tape,component_skew]

theorem ff_swap (h : 4 ≤ d) (a b c e : Axis) : ff G d h a b c e = ff G d h c e a b := by
  apply Subtype.ext
  change tape _ _ = tape (G:=G) _ _
  apply Finset.sum_congr rfl; intro i _; rw [mul_comm]

end YM.UVNext.FreeStress
