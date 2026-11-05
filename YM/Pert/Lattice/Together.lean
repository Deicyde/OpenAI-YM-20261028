import YM.Pert.Lattice.Series
/-! Finite-demand identity; operations on formal Wilson integrands commute with passing to any smaller order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Filter MeasureTheory
open scoped BigOperators
variable {D : Type*}
local notation "coef" => (PowerSeries.coeff (R:=ℂ))
def Together (k : ℕ) (f g : JetArray D) := ∀ m≤k, ∀ x, coef m (f x) = coef m (g x)
def stopsAt (k : ℕ) (f : JetArray D) (x : D) : PowerSeries ℂ := PowerSeries.mk (fun i => if i≤k then coef i (f x) else 0)
variable {k q : ℕ} {f f' g g' : JetArray D}
lemma Together.mono (h : Together q f f') (hk : k≤q) : Together k f f' := fun m hm => h m (hm.trans hk)
lemma Together.symm (h : Together q f f') : Together q f' f := fun m hm x => (h m hm x).symm
lemma Together.same (f : JetArray D) : Together k f f := fun _ _ _ => rfl
lemma Together.trans (h : Together q f f') (g : Together q f' g') : Together q f g' := fun m hm x => (h m hm x).trans (g m hm x)
lemma Together.add (h : Together k f f') (j : Together k g g') : Together k (f+g) (f'+g') := by
  intro i hi x; simp only [Pi.add_apply,map_add, h i hi, j i hi]
lemma Together.mul (h : Together k f f') (j : Together k g g') : Together k (f*g) (f'*g') := by
  intro i hi x; simp only [Pi.mul_apply,PowerSeries.coeff_mul]; refine Finset.sum_congr rfl fun ⟨u,v⟩ huv => ?_
  change _ * _ = _ * _; simp only [Finset.mem_antidiagonal] at huv
  simp only [h u (by omega) x, j v (by omega) x]
lemma Together.pow (h : Together k f f') (j : ℕ) : Together k (f^j) (f'^j) := by
  induction j with
  | zero => exact same _
  | succ j ih => simpa only [pow_succ] using ih.mul h
lemma compact_same : Together k (stopsAt k f) f := fun i hi x => by simp [stopsAt, PowerSeries.coeff_mk,hi]
lemma compact_identity {j q : ℕ} (h : j≤q) (f : JetArray D) : Together j (stopsAt q f) (stopsAt j f) := (Together.mono compact_same h).trans compact_same.symm
lemma Together.equals {f g : JetArray D} (h : Together k f g) : stopsAt k f=stopsAt k g := by
  ext1 x; ext1 i; by_cases hi : i≤k <;> simp only [stopsAt, PowerSeries.coeff_mk, hi, if_true, if_false]
  exact h i hi _
lemma Together.sum {I : Type*} {s : Finset I} {f g : I → JetArray D} (h : ∀ i∈s,Together k (f i) (g i)) : Together k (∑ i∈s,f i) (∑ i∈s,g i) := by
  intro m hm x; simp only [Finset.sum_apply,map_sum]; exact Finset.sum_congr rfl (fun i hi => h i hi _ hm _)
lemma Together.exp (h : Together k f f') : Together k (expR f) (expR f') := by
  intro m hm x; unfold expR; simp only [PowerSeries.coeff_mk]; refine Finset.sum_congr rfl (fun i hi => congrArg (((i.factorial : ℂ)⁻¹) * ·) ?_)
  simpa using h.pow i m hm x
lemma Together.inv' (h : Together k f f') : Together k f⁻¹ f'⁻¹ := by
  intro m
  induction m using Nat.strongRecOn with
  | ind i ih =>
    intro hi x
    simp only [Pi.inv_apply]
    have hz (v : D) : PowerSeries.constantCoeff (f v) = PowerSeries.constantCoeff (f' v) := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h 0 (Nat.zero_le _) v
    rw [PowerSeries.coeff_inv, PowerSeries.coeff_inv,hz x]
    congr 2; refine Finset.sum_congr rfl fun ⟨a,b⟩ hab => ?_; have he := Finset.mem_antidiagonal.mp hab
    rw [h a (by simp only at he; omega)]; split_ifs with ht; swap; · rfl
    rw [show coef b (f x)⁻¹ = coef b (f' x)⁻¹ from ih b ht (by omega) x]

variable {G : Gauge} {n : Side}
lemma Together.average {f f' : JetArray (Coords G n)} (h : Together k f f') : Together k (fun _ : Unit => expect f) (fun _ : Unit => expect f') := by
  intro i hi u; unfold expect; simp_rw [PowerSeries.coeff_mk, h i hi]
lemma Together.average_at {f f' : JetArray (Coords G n)} (h : Together k f f') : Together k (fun _ : Unit => normalize f) (fun _ : Unit => normalize f') := ((Together.same _ |>.mul h).average.mul (Together.same _))

def partialNormalize (weight mark : JetArray (Coords G n)) : PowerSeries ℂ := expect (weight*mark) * (expect weight)⁻¹
/-- Compute all retained coefficients only using vertices (Haar and FP) through k,
and link action Taylor coefficients `k+2`. Inverting a *common* denominator. -/
lemma finite_agreement (f : JetArray (Coords G n)) :
    Together k (fun _ : Unit => partialNormalize (expR (stopsAt k (actionR G n)) * stopsAt k (unmarked G n)) (stopsAt k f)) (fun _ => normalize f) := by
  have hw := ((compact_same (f:= actionR G n) (k:=k)).exp.mul (compact_same (f:=unmarked G n)))
  exact (hw.mul (compact_same (f:=f))).average.mul (hw.average.inv')
end YM.Pert.Orb
