import YM.WilsonBulk.Heat.Caption
import YM.WilsonBulk.Series.Saturation
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Logarithmic heat equation and dress by expedition density

Time is polynomial at fixed e, even after dressing (prove by composition into
power series algebra over polynomial coeff). Finite-dimensional polynomial
operational version convenient with the formal horizon. Clock/time derivative
KEEP parameters. No contour derivatives evaluated outside generators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical Topology ENNReal BigOperators
open Function Finset Equiv
open MvPolynomial (C pderiv)
variable {α : Type} {n k d e : ℕ} {G : Page α 2} [Fintype α]
abbrev KTime (α : Type) := Polynomial (Formula α)
-- polynomial carrying real coefficients in x at timestep.
def sundial (α : Type) : Derivation ℝ (KTime α) (KTime α) := Polynomial.derivative'.restrictScalars ℝ
set_option backward.isDefEq.respectTransparency false in
def wall (D : Derivation ℝ (Formula α) (Formula α)) : Derivation ℝ (KTime α) (KTime α) :=
    PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

omit [Fintype α] in
lemma wall_price (p : KTime α) (D : Derivation ℝ (Formula α) (Formula α)) (i) : (wall D p).coeff i = D (p.coeff i) := rfl
omit [Fintype α] in
lemma sun_price (p : KTime α) (i : ℕ) : (sundial α p).coeff i = ((i+1:ℕ):ℝ) • p.coeff (i+1) := by
  change (Polynomial.derivative p).coeff i=_; rw [Polynomial.coeff_derivative,Nat.cast_smul_eq_nsmul,nsmul_eq_mul, Nat.cast_succ,mul_comm]

def magnitude (G : Page α 2) (I : Record α) (e : ℕ) := ∑ d∈spend e,Polynomial.monomial d (capsule e (immerse G I false d e))
variable (G)
lemma tick {I : Record α} (h : FrameBound I) (hf : Free I) (e d : ℕ) :
    Polynomial.coeff (magnitude G I e) d = capsule e (immerse G I false d e) := by
  unfold magnitude; simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]; rw [sum_eq_single d]; swap
  · intro a ha he; simp [he]
  swap
  · intro hD
    have he : 3*e<d:= Nat.lt_of_succ_le (Nat.le_of_not_gt (mem_range.not.mp hD))
    have hU : ∀ n, immerse G I false d e n=0:=fun n=> immerse_time G false h hf d e n (by omega)
    unfold capsule; simp_rw [hU]; simp
  simp
-- package as log series (init assembled)
def vat (G : Page α 2) (I : Record α) := PowerSeries.mk (magnitude G I)
lemma vat_price {I : Record α} (h : FrameBound I) (hf : Free I) (t e : ℕ) :
    Polynomial.coeff (PowerSeries.coeff e (vat G I)) t=capsule e (immerse G I false t e) := by rw [vat, PowerSeries.coeff_mk,tick G h hf]
lemma vat_flat {I : Record α} (hf : Free I) : PowerSeries.constantCoeff (vat G I)=0 := by
  unfold vat; rw [PowerSeries.constantCoeff_mk]; unfold magnitude capsule; have h₁ d n:= immerse_free G false hf d n; simp_rw [h₁]; simp

def lapTime (G : Page α 2) : KTime α→ₗ[ℝ]KTime α :=
   ∑ x,∑ y,(G (two x y)/2) • ((wall (pderiv y)).toLinearMap.comp (wall (pderiv x)).toLinearMap)
lemma lapTime_price (p : KTime α) (i : ℕ) : (lapTime G p).coeff i= laplace G (p.coeff i) := by
  simp only [lapTime,laplace_eval, LinearMap.sum_apply, LinearMap.smul_apply,LinearMap.comp_apply,Polynomial.finsetSum_coeff, Polynomial.coeff_smul]; rfl
abbrev Woven (α : Type) := PowerSeries (KTime α)
def competition (p q : Woven α) : Woven α :=
    ∑ x,∑ y,(G (two x y)/2) • (parallelD (wall (pderiv x)) p * parallelD (wall (pderiv y)) q)
abbrev pullTime (p : Woven α) (e d : ℕ) := Polynomial.coeff (PowerSeries.coeff e p) d
lemma competition_price (p q : Woven α) (e d : ℕ) :
    pullTime (competition G p q) e d = ∑ i : Split e,∑ j : Split d, airing G (pullTime p (l i) (l j)) (pullTime q (r i) (r j)) := by
  unfold pullTime competition airing
  simp only [map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_mul, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, Polynomial.coeff_mul,parallel_D,wall_price,Finset.smul_sum]
  -- antidiag typed and swap
  let f := fun x y i j d t=>(G (two x y)/2) • (pderiv x (pullTime p i d) * pderiv y (pullTime q j t))
  change (∑ x:α,∑ y:α,∑ i∈antidiagonal e,∑ j∈antidiagonal d,f x y i.1 i.2 j.1 j.2)=
     ∑ i : Split e,∑ j : Split d,∑ x:α,∑ y:α,f x y (l i) (r i) (l j) (r j)
  simp_rw [← diagonals (f _ _ _ _) d]
  have ht x y : ∑ i∈antidiagonal e,∑ j : Split d,f x y i.1 i.2 (l j) (r j) = ∑ i:Split e, ∑ j: Split d,f x y (l i) (r i) (l j) (r j) := (diagonals (fun a b=> ∑ j:Split d,f x y a b (l j) (r j)) e).symm
  simp_rw [ht]
  conv_lhs =>
     arg 2; intro x; rw [permute_three]
  rw [permute_three];
lemma pde {I : Record α} (h : Based I) (hf : Free I) (hr : FrameBound I) :
    let u := vat G I; parallelD (sundial α) u=parallel (lapTime G) u + competition G u u := by
  intro u; ext1 e; ext1 d; change pullTime _ e d=pullTime _ e d
  unfold pullTime
  rw [map_add,Polynomial.coeff_add,coeff_parallel,parallel_D]; conv_rhs => arg 2; change pullTime _ _ _
  rw [competition_price, sun_price, lapTime_price]; unfold pullTime u
  simp_rw [vat_price G hr hf]; exact equation G h hr d e
lemma homogenize (v : Woven α) : parallel (lapTime G) v=∑ x,∑ y,(G (two x y)/2) • (parallelD (wall (pderiv y)) (parallelD (wall (pderiv x)) v)) := by
  ext1 n; simp only [coeff_parallel,map_sum,PowerSeries.coeff_smul,parallel_D,lapTime, LinearMap.sum_apply, LinearMap.smul_apply,LinearMap.comp_apply]; rfl
lemma paired_D {A : Type} [CommRing A] [Algebra ℝ A] (a b : Derivation ℝ A A) (p : ℝ) {u : PowerSeries A}
    (hu : PowerSeries.constantCoeff u=0) :
    p • parallelD b (parallelD a (tide u))= tide u*(p • parallelD b (parallelD a u))+ tide u * (p • (parallelD a u * parallelD b u)) := by
  rw [differentiating a hu,D_leib,differentiating b hu,mul_smul_comm,mul_smul_comm,← smul_add]; congr 1; ring

lemma dresses {u : Woven α} (hu : PowerSeries.constantCoeff u=0) : parallel (lapTime G) (tide u) = tide u*(parallel (lapTime G) u+competition G u u) := by
  -- use explicit identity before summand
  have hh (x y : α) :
    let a : Derivation ℝ (Woven α) (Woven α):= parallelD (wall (pderiv x)); let b: Derivation ℝ (Woven α) (Woven α):= parallelD (wall (pderiv y))
    let p := G (two x y)/2; p • (b (a (tide u))) = tide u*(p • (b (a u))) + tide u* (p • (a u * b u)) := by
    exact paired_D (wall (pderiv x)) (wall (pderiv y)) (G (two x y)/2) hu
  rw [homogenize, homogenize, competition, mul_add]; simp_rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl fun x _=>sum_congr rfl fun y _=> hh ..
lemma gaussian_pde {I : Record α} (h : Based I) (hf : Free I) (hr : FrameBound I) (e : ℕ) :
   let x := PowerSeries.coeff e (tide (vat G I)); sundial α x= lapTime G x := by
  intro x; rw [show sundial α x=(PowerSeries.coeff _ _) from (parallel_D _ _ _).symm, ← (show PowerSeries.coeff _ _=lapTime G x from coeff_parallel _ _ _)]
  rw [dresses G (vat_flat G hf), differentiating _ (vat_flat G hf), pde G h hf hr]
end YM.WilsonBulk.Sheet
