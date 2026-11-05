import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Lift derivations coefficientwise. Time uses polynomials in one extra variable, then
coupling uses PowerSeries (applied only coefficientwise).
-/
noncomputable section
namespace YM.RG08.Cloud
open Finset PowerSeries
open scoped PowerSeries BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type*}[CommRing R][Algebra ℝ R][CommRing S][Algebra ℝ S]

def flight (D:Derivation ℝ R R): Derivation ℝ (PowerSeries R) (PowerSeries R) where
 toFun f:=mk (fun e=> D (coeff e f))
 map_add' _ _ := by ext e; simp only [coeff_mk,map_add]
 map_smul' a f:= by ext e; change coeff e (mk _) = coeff e (a • (mk _ : PowerSeries R)); simp only [coeff_smul,coeff_mk];exact D.map_smul _ _
 map_one_eq_zero':=by ext e;dsimp; simp only [coeff_mk,coeff_one,apply_ite,Derivation.map_one_eq_zero,map_zero,ite_self]
 leibniz' x y := by
  ext e;dsimp
  simp only [smul_eq_mul,coeff_mk,coeff_mul,map_sum,map_add,coeff_mk,Derivation.leibniz,Finset.sum_add_distrib]
  congr 1
  -- reindex via coeff_mul of ? using swap diag
  exact Finset.Nat.sum_antidiagonal_swap (f:=fun z=>coeff z.1 y*D (coeff z.2 x))

theorem flight_apply (D:Derivation ℝ R R)(f:R⟦X⟧)(e):coeff e (flight D f)=D (coeff e f):=coeff_mk e (fun j=>D (coeff j f))

def current (D:Derivation ℝ R R): Derivation ℝ (Polynomial R) (Polynomial R):= PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs
lemma amps (D:Derivation ℝ R R)(f:Polynomial R)(e): (current D f).coeff e = D (f.coeff e):=rfl

def pendulum (R:Type*)[CommRing R][Algebra ℝ R] : Derivation ℝ (Polynomial R) (Polynomial R):= Polynomial.derivative'.restrictScalars ℝ
lemma beat (f:Polynomial R)(e:ℕ) : (pendulum R f).coeff e= (e+1:ℝ) • (f.coeff (e+1)):= by
 change (Polynomial.derivative f).coeff e=_
 rw [Polynomial.coeff_derivative, Algebra.smul_def,mul_comm,_root_.map_add,_root_.map_natCast,map_one]

end YM.RG08.Cloud
