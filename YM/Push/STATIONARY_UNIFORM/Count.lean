import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Corona.Fill
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07


/-! # Volume-uniform exponential sum envelopes
Using torus max-distance, charges include multiplicity of coordinates at
literal sites. No ℝ monotonicity upper claims on analytic fiber norms here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric
open Lattice
open scoped Topology ContDiff BigOperators Classical

variable {n : Side}

def Decay (α : ℝ) (i j : Site n) := Real.exp (-α*separation i j)
lemma decay_pos (α : ℝ) (i j : Site n) : 0<Decay α i j := Real.exp_pos _
lemma decay_comm (α : ℝ) (i j : Site n) : Decay α i j=Decay α j i := by unfold Decay; rw [separation_comm]
lemma decay_step {α : ℝ} (h : 0≤α) (i j k : Site n) : Decay α i j*Decay α j k ≤ Decay α i k := by
  unfold Decay; rw [← Real.exp_add,Real.exp_le_exp]
  have he : (separation i k:ℝ) ≤ (separation i j:ℝ)+separation j k := by exact_mod_cast separation_triangle i j k
  nlinarith
lemma decay_le {α : ℝ} (h : 0≤α) (i j : Site n) : Decay α i j ≤ 1 := by
  apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (by positivity)

def countCost (α : ℝ) := Real.exp (α*2) * (Nat.factorial 6:ℝ) / α^6 * 2^4
lemma count_pos {α : ℝ} (h : 0 < α) : 0 < countCost α := by unfold countCost; positivity

private lemma harmonic (N : ℕ) : ∑ i ∈ Finset.range N, (1:ℝ) / ((i+1:ℝ)*(i+2:ℝ)) = 1-1/(N+1:ℝ) := by
  induction N with
  | zero => simp
  | succ i ih => rw [Finset.sum_range_succ, ih, Nat.cast_add,Nat.cast_one]; field_simp; ring

lemma decay_count {α : ℝ} (h : 0<α) (x : Site n) : ∑ i, Decay α x i ≤ countCost α := by
  let d (i : Site n) := separation x i
  let s (k : ℕ) := Finset.univ.filter fun i => d i=k
  have hc (k : ℕ) : (s k).card ≤ (k+k+1)^4 := by
    have he : s k ⊆ halo k {x} := fun i hi => halo_spec.mpr
      ⟨x,Finset.mem_singleton_self _, ((Finset.mem_filter.mp hi).2).le⟩
    apply (Finset.card_le_card he).trans; simpa using Corona.halo_size ({x}:Support n) k
  have hk (k : ℕ) : ∑ i∈s k, Decay α x i ≤ countCost α*((1:ℝ) / ((k+1:ℝ)*(k+2:ℝ))) := by
    let a : ℝ := k
    have ha : 0≤a:=by unfold a; positivity
    have hj : Real.exp (-α*a) ≤ Real.exp (α*2) * ((Nat.factorial 6:ℝ) / (α*(a+2))^6) := by
      rw [show -α*a=α*2+ -(α*(a+2)) by ring, Real.exp_add,Real.exp_neg]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have H := one_div_le_one_div_of_le (show 0 < (α*(a+2))^6/(Nat.factorial 6:ℝ) by positivity)
        (Real.pow_div_factorial_le_exp _ (by positivity) _)
      simpa using H
    calc
      _ = ∑ _i∈s k, Real.exp (-α*a) := Finset.sum_congr rfl fun i hi => by
        change Real.exp (-α*d i)=_
        rw [(Finset.mem_filter.mp hi).2]
      _ ≤ (2*(a+2))^4 * (Real.exp (α*2) * ((Nat.factorial 6:ℝ) / (α*(a+2))^6)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul _ hj (Real.exp_pos _).le (by positivity)
        calc
          _ ≤ (a+a+1)^4 := by unfold a; exact_mod_cast hc k
          _ ≤ _ := by gcongr; linarith
      _ = countCost α * (1/((a+2)*(a+2))) := by unfold countCost; field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (count_pos h).le
        refine one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right ?_ (by positivity)); change a+1 ≤ a+2; linarith
  let M := Finset.univ.sup d + 1
  have hR : ∀ i∈(Finset.univ:Finset (Site n)), d i ∈ Finset.range M := fun i hi => Finset.mem_range.mpr
    (lt_of_le_of_lt (Finset.le_sup (f:=d) hi) (Nat.lt_succ_self _))
  rw [← Finset.sum_fiberwise_of_maps_to hR]; apply (Finset.sum_le_sum fun k _ => hk k).trans
  rw [← Finset.mul_sum,harmonic]; exact mul_le_of_le_one_right (count_pos h).le (sub_le_self _ (by positivity))

def Multiplicity {ι : Type*} [Fintype ι] (a : ι → Site n) (K : ℕ) : Prop :=
  ∀ x : Site n, (Finset.univ.filter fun i => a i=x).card ≤ K

lemma Multiplicity.injective {ι : Type*} [Fintype ι] {a : ι → Site n} (h : Injective a) : Multiplicity a 1 := fun _ =>
  Finset.card_le_one.mpr fun _ hi _ hj => h ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

lemma Multiplicity.comp {ι κ : Type*} [Fintype ι] [Fintype κ] {a : ι → Site n} {K} (h : Multiplicity a K)
    {f : κ → ι} (hf : Injective f) : Multiplicity (a ∘ f) K := fun x => le_trans (Finset.card_le_card_of_injOn f (fun _ hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩) hf.injOn) (h x)

lemma Multiplicity.count {ι : Type*} [Fintype ι] (a : ι → Site n) {K} (ha : Multiplicity a K)
    {α : ℝ} (h : 0 < α) (x : Site n) : ∑ i, Decay α x (a i) ≤ K*countCost α := by
  rw [← Finset.sum_fiberwise _ a]
  calc
    _ ≤ ∑ y, (K:ℝ)*Decay α x y := Finset.sum_le_sum fun y _ => by
      let s := Finset.univ.filter fun i => a i=y
      calc
        _ = ∑ _i∈s, Decay α x y := Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
        _ ≤ _ := by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast ha y) (decay_pos ..).le
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (decay_count h x) (by positivity)
end YM.Push.Uniform
