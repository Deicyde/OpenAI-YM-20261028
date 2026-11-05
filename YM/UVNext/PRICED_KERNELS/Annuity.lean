import YM.Axis.Matrix
import YM.Next.FREE_KERNELS.Traffic
import YM.Work.B04
import YM.Work.C01


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Packaging absolute kernel costs at an anchored site

For linear pricing associated to the actual Φ rows & root-fixed tree
stationary direction. See `Trees`. All applications in physical
*counting* spaces, real scalar cochains; subsequent consumers can use
with color part estimates. Include lifts and true metric distance, e.g.
weights already periodized OVER residues via `row_sprawl`, not forgetting
that fine column pay factor is L^4. We don't distinguish orientations in
the cost here; that's not permission to average channels or symmetries
when reading a formula. Exact formulas in subsequent applications.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Precision Pressure Laurent Exterior Bloch Matrix
open Next.Free
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {n : Side} {ι κ ν : Type*}

def gained (s : ℝ) (x y : Site n) := Real.exp (s*(separation x y : ℝ))
lemma gained_pos (s : ℝ) (x y : Site n) : 0 < gained s x y := Real.exp_pos _
lemma gained_triangle {s : ℝ} (hs : 0 ≤ s) (x y z : Site n) : gained s x z ≤ gained s x y * gained s y z := by
  unfold gained; rw [← Real.exp_add,← mul_add]; apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hs; exact_mod_cast separation_triangle x y z
lemma gained_mono {s t : ℝ} (h : s ≤ t) (x y : Site n) : gained s x y ≤ gained t x y := by unfold gained; gcongr

lemma gained_comm (s : ℝ) (x y : Site n) : gained s x y=gained s y x := congr_arg (fun m : ℕ => Real.exp (s*m)) (separation_comm x y)

abbrev Foot (n : Side) (ι : Type*) := ι → Site n

def Annuity [Fintype κ] (p : Foot n ι) (q : Foot n κ) (A : Matrix ι κ ℝ) (s C : ℝ) :=
    ∀ i, (∑ j, gained s (p i) (q j) * |A i j|) ≤ C

namespace Annuity
variable [Fintype κ] {A B : Matrix ι κ ℝ} {p : Foot n ι} {q : Foot n κ} {s t C D v : ℝ}

lemma cut (h : Annuity p q A t C) (he : s ≤ t) (hc : C ≤ D) : Annuity p q A s D := fun i =>
    le_trans (Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right (gained_mono he _ _) (abs_nonneg _)) ((h i).trans hc)

lemma plus (h : Annuity p q A s C) (he : Annuity p q B s D) : Annuity p q (A+B) s (C+D) := by
  intro i
  refine le_trans (Finset.sum_le_sum (g:=fun j => gained s (p i) (q j) * (|A i j|+|B i j|)) (fun j _ => ?_)) ?_
  · exact mul_le_mul_of_nonneg_left (abs_add_le ..) (gained_pos ..).le
  simp_rw [mul_add,Finset.sum_add_distrib]; exact add_le_add (h i) (he i)
lemma negative (h : Annuity p q A s C) : Annuity p q (-A) s C := fun i => by simp; exact h i
lemma minus (h : Annuity p q A s C) (he : Annuity p q B s D) : Annuity p q (A-B) s (C+D) := by rw [sub_eq_add_neg]; exact h.plus he.negative


lemma times [Fintype ν] {r : Foot n ν} {Q : Matrix κ ν ℝ}
    (h : Annuity p q A s C) (hk : Annuity q r Q s D) (hp : 0 ≤ s) (hd : 0 ≤ D) : Annuity p r (A*Q) s (C*D) := by
  intro i; let F (j) := gained s (p i) (q j)*|A i j|
  have he x : gained s (p i) (r x) * |(A*Q) i x| ≤ ∑ j : κ, F j*(gained s (q j) (r x)*|Q j x|) := by
    rw [Matrix.mul_apply]; refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (gained_pos ..).le) ?_
    rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]; refine (mul_le_mul_of_nonneg_right (gained_triangle hp _ (q j) _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq ?_; unfold F; ring
  have hh j : 0 ≤ F j := mul_nonneg (gained_pos ..).le (abs_nonneg _)
  refine le_trans (Finset.sum_le_sum fun x _ => he x) ?_
  rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum (g:=fun j => F j*D) fun j _ => mul_le_mul_of_nonneg_left (hk j) (hh j)) ?_
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h i) hd



lemma earned (h : ∀ i (v : κ → ℝ), (∀ j,|v j| ≤ gained s (p i) (q j)) → |(A*ᵥv) i| ≤ C) :
    Annuity p q A s C := by
  intro i
  let t j := gained s (p i) (q j)
  let x (j) := if 0 ≤ A i j then t j else -t j
  have hp j : 0 ≤ t j := (gained_pos ..).le
  have hw j : |x j| ≤ t j := by unfold x; split_ifs <;> simp only [abs_neg, abs_of_nonneg (hp j), le_refl]
  refine le_trans ?_ (h _ x hw)
  refine le_trans ?_ (le_abs_self _)
  change _ ≤ ∑ j, A i j*x j
  refine Finset.sum_le_sum fun j _ => ?_
  unfold x; split_ifs with hh
  · exact le_of_eq (by rw [abs_of_nonneg hh,mul_comm])
  exact le_of_eq (by rw [abs_of_neg (lt_of_not_ge hh)]; unfold t; ring)
end Annuity

def site (n : Side) (ι : Type*) : Foot n (Bloch.Co n ι) := Prod.fst
def parent {c f : Side} (g : Ratio c f) (ι : Type*) : Foot f (Bloch.Co c ι) := fun i => g.embed i.1

namespace Annuity

section single
variable [Fintype κ] {R : Row ι κ} {η C : ℝ}
lemma paid_site (h : R.strip η C) (he : 0 ≤ η) (n : Side) : Annuity (site n _) (site n _) (R.acts n) η (Fintype.card κ * C) :=
    row_sprawl he h n
lemma paid_parent {c f : Side} (g : Ratio c f) (h : R.strip η C) (he : 0 ≤ η) : Annuity (parent g _) (parent g _)
    (R.acts c) (η/g.count.val) (Fintype.card κ * C) := by
  have hp (i) := (paid_site h he c) i
  intro i; refine le_trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (hp i)
  apply Real.exp_le_exp.mpr
  unfold parent
  let n : ℝ := g.count.val; let m : ℝ := separation i.1 j.1
  have hL : 0 < n := side_pos _
  have hs : (separation (g.embed i.1) (g.embed j.1):ℝ) ≤ n*m := by unfold n m; exact_mod_cast scaled_root g i.1 j.1
  refine le_trans (mul_le_mul_of_nonneg_left hs (div_nonneg he hL.le)) ?_
  change η/n*(n*m) ≤ η*m; exact le_of_eq (by field_simp)
end single

section cross
variable {c f : Side} {g : Ratio c f} {R : Cross g.count ι κ} {η C : ℝ}
private lemma applied (g : Ratio c f) (η : ℝ) (x : Bloch.Co f ι) (j : Bloch.Co c κ) :
    gained (η/g.count.val) (site f ι x) (parent g κ j)=crossW g η x.1 j.1 := by unfold gained site parent crossW; congr 1; ring

lemma paid_cross [Fintype κ] (h : R.strip η C) (he : 0 ≤ η) :
    Annuity (site f _) (parent g _) (installed g R) (η/g.count.val) (Real.exp η*(Fintype.card κ*C)) := by
  intro i; simp_rw [applied]; exact cross_sprawl g he h i
lemma paid_cross_reverse [Fintype ι] (h : R.strip η C) (he : 0 ≤ η) :
    Annuity (parent g _) (site f _) (installed g R).transpose (η/g.count.val) (Real.exp η*(g.count.val^4*(Fintype.card ι*C))) := by
  intro i; simp_rw [gained_comm _ (parent _ _ _),applied]
  exact crossColumns g he h i
end cross
end Annuity
end YM.UVNext.PricedKernels
