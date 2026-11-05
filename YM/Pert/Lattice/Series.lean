import YM.Pert.Lattice.Tamed
import YM.Pert.Lattice.GaugeFix
import YM.Pert.Lattice.Representatives
import Mathlib.RingTheory.PowerSeries.Inverse
/-! Raw all-orders connected or ordinary diagrams before operator mixing and coupling inversion, at *finite* regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Filter MeasureTheory
open scoped BigOperators
abbrev JetArray (D : Type*) := D → PowerSeries ℂ
variable {D : Type*} [NormedAddCommGroup D]
local notation "coef" => (PowerSeries.coeff (R:=ℂ))
def Ready (φ : JetArray D) := ∀ m, Tame (fun x => coef m (φ x))
lemma Ready.constant (f : PowerSeries ℂ) : Ready (fun _ : D => f) := fun _ => Tame.constant _
lemma Ready.add {f g : JetArray D} (h : Ready f) (j : Ready g) : Ready (f+g) := by intro i; simp only [Pi.add_apply,map_add]; exact (h i).add (j i)
lemma Ready.mul {f g : JetArray D} (h : Ready f) (j : Ready g) : Ready (f*g) := by
  intro i; simp_rw [Pi.mul_apply,PowerSeries.coeff_mul]
  convert! (Tame.sum (s:=Finset.antidiagonal i) (fun p _ => (h p.1).mul (j p.2))) using 1
  ext x; simp only [Finset.sum_apply,Pi.mul_apply,Pi.pow_apply]
lemma Ready.pow {f : JetArray D} (h : Ready f) (m : ℕ) : Ready (f^m) := by
  induction m with
  | zero => exact pow_zero f ▸ Ready.constant _
  | succ m ih => rw [pow_succ]; exact ih.mul h
lemma Ready.sum {I : Type*} {s : Finset I} {f : I → JetArray D} (h : ∀ i∈s, Ready (f i)) : Ready (∑ i∈s, f i) := by
  intro m; simp_rw [Finset.sum_apply,map_sum]
  convert! (Tame.sum (s:=s) fun i hi => h i hi m) using 1
  ext x; simp only [Finset.sum_apply,Pi.mul_apply,Pi.pow_apply]
lemma Ready.prod {I : Type*} {s : Finset I} {f : I → JetArray D} (h : ∀ i∈s, Ready (f i)) : Ready (∏ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact Ready.constant _
  | insert a s hs ih => rw [Finset.prod_insert hs]; exact (h _ (Finset.mem_insert_self a s)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
lemma Ready.maker {f : D → ℕ → ℂ} (h : ∀ i, Tame (fun x => f x i)) : Ready (fun x => PowerSeries.mk (f x)) := by
  intro i; simp_rw [PowerSeries.coeff_mk]; exact h i

/-- Exponential of an interaction series based at zero. Use *only* with zero constant coefficient. Finite coefficient definition, no sum at nonformal coupling. -/
def expR (p : JetArray D) : JetArray D :=
  fun x => PowerSeries.mk (fun e => ∑ l ∈ Finset.range (e+1), ((l.factorial : ℂ))⁻¹ * coef e (p x ^ l))
lemma Ready.exp {p : JetArray D} (hp : Ready p) : Ready (expR p) := by
  unfold expR; refine Ready.maker (fun i => ?_)
  convert! (Tame.sum (s:=Finset.range (i+1)) fun l hm => (Tame.constant ((l.factorial:ℂ)⁻¹)).mul (hp.pow l i)) using 1
  ext x; simp only [Finset.sum_apply,Pi.mul_apply,Pi.pow_apply]
@[simp] lemma exp_zero (p : JetArray D) (x:D) : coef 0 (expR p x)=1 := by simp [expR]

variable {G : Gauge} {n : Side}
def scaleJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Potential G n → E) (m : ℕ) (x : Coords G n) : E :=
  (m.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ m f 0 (fun _ => expand G n x)
lemma tame_scaleJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Potential G n → E) (m) : Tame (scaleJet f m) :=
  (by exact (Tame.jet (expand G n).toContinuousLinearMap (iteratedFDeriv ℝ m f 0)).scalar_const ((m.factorial:ℝ)⁻¹))
lemma scaleJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Potential G n → E) : scaleJet f 0 = fun _ => f 0 := by
  ext x; simp [scaleJet]
lemma scaleJet_two (x : Coords G n) : scaleJet (action G n) 2 x = form (expand G n x) (expand G n x)/2 := by
  have h : (fun _ : Fin 2 => expand G n x)=![expand G n x,expand G n x] := funext (fun i => by fin_cases i <;> simp)
  simp only [scaleJet,h,jets_action.2.2,Nat.factorial_succ,Nat.reduceSubDiff,Nat.factorial]; norm_cast; simp; ring

def unmarked (G : Gauge) (n : Side) : JetArray (Coords G n) :=
  fun x => PowerSeries.mk (fun i => ↑(scaleJet (fun u => Jacob u * FP u) i x))
def actionR (G : Gauge) (n : Side) : JetArray (Coords G n) :=
  fun x => PowerSeries.mk (fun i => if i=0 then 0 else ↑(-scaleJet (action G n) (i+2) x))
def weight (G : Gauge) (n : Side) : JetArray (Coords G n) := expR (actionR G n) * unmarked G n
lemma unmarked_ready : Ready (unmarked G n) := Ready.maker (fun i => (tame_scaleJet (fun u => Jacob u*FP u) i).ofReal)
lemma actionR_ready : Ready (actionR G n) := by
  refine Ready.maker (fun i => ?_); by_cases h : i=0
  · simp only [h, ↓reduceIte]; exact Tame.constant _
  simp only [if_neg h]; convert! ((tame_scaleJet (action G n) (i+2)).scalar_const (-1) |>.ofReal) using 1
  ext; dsimp; simp
lemma weight_ready : Ready (weight G n) := Ready.mul actionR_ready.exp unmarked_ready

@[simp] lemma weight_flat (x : Coords G n) : coef 0 (weight G n x)=1 := by
  unfold weight; rw [Pi.mul_apply, PowerSeries.coeff_mul]; simp [unmarked,scaleJet_zero]

/-- Wick expectation using covariance from the actual Hessian (link log variables are rescaled). -/
def expect (f : JetArray (Coords G n)) : PowerSeries ℂ := PowerSeries.mk (fun i => ∫ x : Coords G n, coef i (f x) ∂data G n)
lemma expect_add {f g : JetArray (Coords G n)} (hf : Ready f) (hg : Ready g) : expect (f+g) = expect f + expect g := by
  ext1 i; simp only [expect, PowerSeries.coeff_mk,map_add,Pi.add_apply]; exact integral_add (hf i).integrable (hg i).integrable
lemma expect_zero : expect (G:=G) (n:=n) 0=0 := by ext1 i; simp [expect,Pi.zero_apply]
lemma expect_shift (z : PowerSeries ℂ) {f : JetArray (Coords G n)} (hf : Ready f) : expect ((fun _ => z) * f) = z * expect f := by
  ext1 i; simp only [expect,PowerSeries.coeff_mk,PowerSeries.coeff_mul,Pi.mul_apply]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  exact fun i _ => (hf i.2).integrable.const_mul _

def vacuum (G : Gauge) (n : Side) := expect (weight G n)
def normalize (f : JetArray (Coords G n)) := expect (weight G n * f) * (vacuum G n)⁻¹
lemma vacuum_flat : coef 0 (vacuum G n) = 1 := by simp [expect,vacuum]
lemma normalized_unit : normalize (G:=G) (n:=n) 1=1 := by
  rw [normalize,mul_one, ← vacuum]; apply PowerSeries.mul_inv_cancel _
  have he := vacuum_flat (G:=G) (n:=n); rw [PowerSeries.coeff_zero_eq_constantCoeff] at he; exact he.trans_ne one_ne_zero
lemma normalize_add {f g : JetArray (Coords G n)} (hf : Ready f) (hg : Ready g) : normalize (f+g) = normalize f + normalize g := by
  simp only [normalize,mul_add,expect_add (weight_ready.mul hf) (weight_ready.mul hg),add_mul]
lemma normalize_shift (z : PowerSeries ℂ) {f : JetArray (Coords G n)} (hf : Ready f) : normalize ((fun _ => z) * f) = z * normalize f := by
  unfold normalize; rw [mul_left_comm, expect_shift z (weight_ready.mul hf),mul_assoc]
end YM.Pert.Orb
