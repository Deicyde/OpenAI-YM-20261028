import YM.Marker.Truncated
import YM.Pressure.Seeds

/-! # Pressure rain construction

Actual complex squarefree polynomials. Exponential at any fixed degree cutoff (lower sets).
Preserve marker estimates through EACH cost test. Norm is not submultiplicative by fiat!
Use the pinned weighted price. Do not assume complex perturbation theorem on mass or alph.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GridRenewal.Rain
open Function Finset Filter RG Marker Wilson Lattice 
open scoped Topology BigOperators Classical
variable {V : Type*} [DecidableEq V] {R : Census V} {ι β : Type*}

local instance : IsTopologicalSemiring (Poly R) where

lemma price_sums {f : ι → Poly R} (w : V → ℝ) (h : Summable f) : Summable (fun i => Poly.price w (f i)) := by
  have he (j : R.Mode) : Summable (fun i => (f i).part j) := ((Poly.get j).hasSum h.hasSum).summable
  exact summable_sum (fun i _ => (he i).norm.mul_left _)
lemma hybrid {f : ι → Poly R} {g : β→Poly R} (h : Summable f) (he : Summable g) :
    Summable (fun i : ι × β => f i.1*g i.2) := by
  let w := fun _ : V=> (1:ℝ)
  have hh : Summable (fun i : ι × β => Poly.price w (f i.1)*Poly.price w (g i.2)) :=
    summable_mul_of_summable_norm (f:=fun i:ι => Poly.price w (f i)) (g:=fun i:β=> Poly.price w (g i)) ((price_sums w h).norm) ((price_sums w he).norm)
  exact (Poly.budgeted (fun _ => zero_lt_one) hh (fun i=>Poly.multiplication (fun _ => zero_lt_one) ..)).1


def term (p : Poly R) (i : ℕ) := (i.factorial:ℂ)⁻¹ • p^i

def slide (x : ℝ) (i : ℕ) := x^i / (i.factorial:ℝ)

lemma meter (x : ℝ) : HasSum (slide x) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

lemma pays {w : V → ℝ} (h : ∀ i,0<w i) (p : Poly R) (i : ℕ) : Poly.price w (term p i) ≤ slide (Poly.price w p) i := by
  rw [term,Poly.adapted, norm_inv,Complex.norm_natCast,slide, ← inv_mul_eq_div]
  exact mul_le_mul_of_nonneg_left (Poly.powers h ..) (by positivity)
lemma slides (p : Poly R) : Summable (term p) :=
    (Poly.budgeted (fun _ : V => zero_lt_one) (meter _).summable (pays (fun _=>zero_lt_one) p)).1

def cyclone (x : Poly R) := ∑' i : ℕ, term x i

lemma plus (x y : Poly R) : cyclone (x+y)=cyclone x*cyclone y := by
  unfold cyclone
  rw [(slides x).tsum_mul_tsum_eq_tsum_sum_antidiagonal (slides y) (hybrid (slides x) (slides y))]
  refine tsum_congr (fun i=>?_)
  rw [term,(Commute.all x y).add_pow', Finset.smul_sum]; apply sum_congr rfl; intro j hj
  unfold term; rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_mul_smul_comm, ← Finset.mem_antidiagonal.mp hj,
    Nat.cast_add_choose, Finset.mem_antidiagonal.mp hj]
  field_simp [i.factorial_ne_zero]


abbrev bead (R : Census V) := Poly.bead R
lemma beacon (x : ℂ) : bead R x=x • (1:Poly R) := by rw [← Poly.product_bead]; simp [bead]
@[fun_prop] lemma lit (R : Census V) : Continuous (bead R) := by
  rw [show (bead R : ℂ → Poly R)=_ from funext fun x => beacon x]; fun_prop
lemma clear (x : ℂ) : cyclone (bead R x) = bead R (Complex.exp x) := by
  have hh := lit R
  have ht : HasSum (fun i : ℕ => x^i / (i.factorial:ℂ)) (Complex.exp x) := by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  refine ((ht.map (bead R) hh).congr_fun ?_).tsum_eq
  intro i; simp only [Function.comp_apply]; rw [term,←Poly.product_bead,←map_pow]
  exact (map_mul ..).symm.trans (by unfold bead; rw [mul_comm,← div_eq_mul_inv])

@[simp] lemma flare : cyclone (0:Poly R)=1 := by simpa only [map_zero,Complex.exp_zero,map_one] using clear (R:=R) 0




variable [Fintype V]
lemma passes (x : Poly R) (h : x.part R.quiet=0) : cyclone x= Poly.pass x := by
  unfold cyclone Poly.pass; refine tsum_eq_sum ?_; intro i hi
  rw [term, Poly.stops x h _ (show _ from Nat.lt_of_succ_le (not_lt.mp (mt Finset.mem_range.mpr hi))),smul_zero]

omit [Fintype V] in
def fresh (x : Poly R) := x-bead R (x.part R.quiet)
omit [Fintype V] in
lemma unwritten (x : Poly R) : (fresh x).part R.quiet=0 := by
  change x.part R.quiet - (Poly.send R.quiet (x.part R.quiet)).part R.quiet = 0; simp only [Poly.part_send]; simp

lemma power (x : Poly R) : cyclone x = bead R (Complex.exp (x.part R.quiet))* Poly.pass (fresh x) := by
  nth_rw 1 [show x=bead R (x.part R.quiet)+fresh x from by unfold fresh; abel]; rw [plus,clear,passes (fresh x) (unwritten _)]

@[fun_prop] lemma breath : Continuous (cyclone (V:=V) (R:=R)) := by
  have h := lit R
  rw [show cyclone=(fun x:Poly R => _) from funext (fun x => power x)]
  refine (h.comp (Complex.continuous_exp.comp (Poly.part_cont R.quiet))).mul (Poly.pass_cont.comp ?_)
  exact continuous_id.sub (h.comp (Poly.part_cont R.quiet))


omit [Fintype V] in
lemma roaring (v : Finset ι) (f : ι → Poly R) : cyclone (∑ i∈v,f i)=∏ i∈v,cyclone (f i) := by
  induction v using Finset.induction with
  | empty => simp [flare]
  | insert i v hi ih => rw [sum_insert hi,prod_insert hi,plus,ih]

end YM.GridRenewal.Rain
