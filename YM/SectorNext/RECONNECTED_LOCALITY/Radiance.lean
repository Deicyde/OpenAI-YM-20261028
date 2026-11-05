import YM.PREC.Stacks

set_option warningAsError false

/-! # Absolute physical entry service

Start of a quantitative tool to help BUY the covariance port; kernels
on real counting coordinates including all padding. Own bill for going from
upper entry / decay at fixed-L to Schur (don't multiply by volume).
Keep numerical range and locality completely separate from these supplies. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Ice
open Finset Matrix
open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- d may collapse whole color and residue fibres (or use actual midpoint scale).
Use reals so both are available. -/
structure Radar (I : Type*) where
  d : I → I → ℝ
  down i j : 0 ≤ d i j
  same i : d i i=0
  back i j : d i j=d j i
  chain i j k : d i k≤d i j+d j k

variable {g : Radar I} {r t s k m a : ℝ} {A B : Matrix I I ℝ}

def ray (g : Radar I) (r : ℝ) (i j : I) := Real.exp (r*g.d i j)

def bill (g : Radar I) (r : ℝ) (A : Matrix I I ℝ) (i j : I) := |A i j| * ray g r i j

def Deck (g : Radar I) (A : Matrix I I ℝ) (r k : ℝ) :=
    (∀ i,∑ j,bill g r A i j≤k) ∧ ∀ j,∑ i,bill g r A i j≤k

omit [Fintype I] in
lemma ray_pos (g : Radar I) (r : ℝ) (i j : I) : 0<ray g r i j := Real.exp_pos _

omit [Fintype I] in
lemma ray_nonneg (g : Radar I) (r : ℝ) (i j : I) : 0≤ray g r i j := (ray_pos ..).le

omit [Fintype I] in
@[simp] lemma ray_zero (g : Radar I) (i j : I) : ray g 0 i j=1 := by simp [ray]

omit [Fintype I] in
@[simp] lemma ray_self (g : Radar I) (r : ℝ) (i : I) : ray g r i i=1 := by simp [ray,g.same]

omit [Fintype I] in
lemma ray_symm (i j : I) : ray g r i j=ray g r j i := by rw [ray,ray,g.back i]

omit [Fintype I] in
lemma ray_mono (hr : r ≤ t) (i j : I) : ray g r i j ≤ ray g t i j := Real.exp_le_exp.mpr (by gcongr; exact g.down ..)

omit [Fintype I] in
lemma ray_add (r t : ℝ) (i j : I) : ray g (r+t) i j = ray g r i j * ray g t i j := by
  unfold ray; rw [add_mul,Real.exp_add]

omit [Fintype I] in
lemma ray_triangle (hr : 0 ≤ r) (i j l : I) : ray g r i l ≤ ray g r i j * ray g r j l := by
  unfold ray; rw [← Real.exp_add,←mul_add]; exact Real.exp_le_exp.mpr (by gcongr; exact g.chain ..)

omit [Fintype I] in
lemma bill_nonneg (g : Radar I) (r : ℝ) (A : Matrix I I ℝ) (i j : I) : 0≤bill g r A i j :=
  mul_nonneg (abs_nonneg _) (ray_nonneg ..)

omit [Fintype I] in
@[simp] lemma bill_zero (g : Radar I) (A : Matrix I I ℝ) (i j : I) : bill g 0 A i j = |A i j| := by simp [bill]

omit [Fintype I] in
lemma bill_mono (hr : r ≤ t) (i j : I) : bill g r A i j ≤ bill g t A i j := by
  unfold bill; exact mul_le_mul_of_nonneg_left (ray_mono hr i j) (abs_nonneg _)

omit [Fintype I] in
lemma bill_transpose (i j : I) : bill g r A.transpose i j = bill g r A j i := by rw [bill,bill,transpose_apply,ray_symm i]

namespace Deck
lemma press (h : Deck g A r k) (hp : ∀ i j,bill g t B i j≤a*bill g r A i j) (ha : 0≤a) : Deck g B t (a*k) := by
  constructor <;> intro i
  · exact (sum_le_sum (fun j _ => hp i j)).trans (by rw [←mul_sum]; gcongr; exact h.1 i)
  exact (sum_le_sum (fun j _ => hp j i)).trans (by rw [←mul_sum]; gcongr; exact h.2 i)

lemma mono (h : Deck g A r k) (hr : t≤r) (hm : k≤m) : Deck g A t m := by
  have he := press (B:=A) (t:=t) (a:=1) h (by intro i j; rw [one_mul]; exact bill_mono hr i j) zero_le_one
  rw [one_mul] at he; exact ⟨fun i => (he.1 i).trans hm, fun i => (he.2 i).trans hm⟩

lemma transpose (h : Deck g A r k) : Deck g A.transpose r k := by
  unfold Deck; simp_rw [bill_transpose]; exact ⟨h.2,h.1⟩





private lemma oneRow (h : Deck g A r k) (he : Deck g B r m) (hr : 0≤r) (hm : 0≤m) (i : I) :
    ∑ j,bill g r (A*B) i j≤k*m := by
  have hl j : bill g r (A*B) i j≤∑ l,bill g r A i l * bill g r B l j := by
    unfold bill; rw [mul_apply]
    apply (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs ..) (ray_nonneg ..)).trans
    rw [sum_mul]; refine sum_le_sum (fun l _ => ?_)
    rw [abs_mul,mul_mul_mul_comm |A i l|]
    exact mul_le_mul_of_nonneg_left (ray_triangle hr ..) (by positivity)
  refine (sum_le_sum (fun j _ => hl j)).trans ?_
  rw [sum_comm]; simp_rw [←mul_sum]
  refine (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (he.1 j) (bill_nonneg ..))).trans ?_
  rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (h.1 i) hm

lemma mul (h : Deck g A r k) (he : Deck g B r m) (hr : 0≤r) (hk : 0≤k) (hm : 0≤m) : Deck g (A*B) r (k*m) := by
  refine ⟨oneRow h he hr hm,?_⟩
  intro i; have hb:=oneRow he.transpose h.transpose hr hk i
  simpa only [← transpose_mul,bill_transpose,mul_comm m] using hb

lemma each (h : Deck g A r k) (i j : I) : bill g r A i j ≤ k :=
  (single_le_sum (f:=fun j => bill g r A i j) (fun _ _ => bill_nonneg ..) (mem_univ j)).trans (h.1 i)
end Deck

/-- Quadratic accounting only: squared Hilbert, NEVER normalized by volume. -/
def fuel (x : I → ℝ) := x ⬝ᵥ x

lemma fuel_nonneg (x : I→ℝ) : 0≤fuel x := sum_nonneg (fun i _ => mul_self_nonneg (x i))









/-- Symmetry not needed for lower accrual/isUnit. -/
def Buoy (A : Matrix I I ℝ) (δ : ℝ) := ∀ x : I→ℝ,δ*fuel x≤x ⬝ᵥ (A *ᵥ x)





end Ice
end YM.SectorNext.Reconnect
