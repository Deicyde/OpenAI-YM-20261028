import YM.Next.SCHEDULE.Melt
import YM.Push.PRICE_COMPILER.Authors
import YM.UVNext.PRICED_KERNELS.Annuity


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# A uniform counting inverse price for real positive precision rows

Weighted-gap proof at a *fixed step*. Can use with the Stamp/Permit's
Θ-independent η & row bounds (which we supply for actual forest Hessians
in `Gaps` independently of period). Deliver costs after L wherever hypotheses
priced then, and still before coupling delay. No appeal to taking L
small or increasing β to fund a pre-L cost. In particular if the admissible
η depends on L this does NOT consume N-independent budgets at a prior
selection demanding pre-L widths. Strict positive widths supplied nevertheless
at EACH j,L, independent of torus size and tree. There is NO field-dependent
hypothesis (e.g. coercivity on arbitrary off-real strips) hidden here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG Laurent Exterior Bloch Matrix Tree
open Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {ι : Type*} [Fintype ι] {n : Side}

/-- Diagonal reweighting is controlled by an exponential *distance*
cost times a small scalar, no self-coupling cost. -/
lemma perturb {s u a b d : ℝ} (hu : 0 ≤ u) (hs : u<s) (hd : 0 ≤ d) (he : |a-b| ≤ d) :
    |1 - Real.exp (u*a)/Real.exp (u*b)| ≤ (u/(s-u)) * Real.exp (s*d) := by
  let x := u*d
  have hx : 0 ≤ x := mul_nonneg hu hd
  rw [← Real.exp_sub, ← mul_sub]
  have hh : -(Real.exp x-1) ≤ (1:ℝ)-Real.exp (u*(a-b)) := by
    have hm := Real.exp_monotone (mul_le_mul_of_nonneg_left ((le_abs_self _).trans he) hu)
    change Real.exp _ ≤ Real.exp x at hm
    linarith
  have hv : (1:ℝ)-Real.exp (u*(a-b)) ≤ Real.exp x-1 := by
    have hm : -x ≤ u*(a-b) := by rw [show -x=u*(-d) by unfold x; ring]; exact mul_le_mul_of_nonneg_left (abs_le.mp he).1 hu
    have hi := Real.exp_monotone hm
    have hl := Real.add_one_le_exp x; have hL := Real.add_one_le_exp (-x)
    linarith
  refine (abs_le.mpr ⟨hh,hv⟩).trans ?_
  -- exp x - 1 <= x exp x
  have hg : Real.exp x * Real.exp (-x)=1 := by rw [← Real.exp_add]; simp
  have hy := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  have ht : s*d=(s-u)*d+x := by unfold x; ring
  rw [hg] at hy
  rw [ht, Real.exp_add, ← mul_assoc]
  refine le_trans (?_ : _ ≤ x * Real.exp x) (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos x).le)
  · linarith only [hy]
  unfold x; rw [div_eq_mul_inv,mul_assoc]; apply mul_le_mul_of_nonneg_left _ hu
  rw [mul_comm (s-u)⁻¹,← div_eq_mul_inv]
  apply (le_div_iff₀ (sub_pos.mpr hs)).mpr
  rw [mul_comm]; linarith [Real.add_one_le_exp ((s-u)*d)]

omit [Fintype ι] in
lemma gained_tilt (v : Foot n ι) (i j k : ι) (s u : ℝ) (hu : 0 ≤ u) (hs : u<s) :
    |1 - gained u (v k) (v i) / gained u (v k) (v j)| ≤ (u/(s-u)) * gained s (v i) (v j) := by
  refine perturb hu hs (Nat.cast_nonneg _) ?_
  rw [abs_le]
  constructor
  · have ht := separation_triangle (v k) (v i) (v j)
    have hh : (separation (v k) (v j):ℝ) ≤ separation (v k) (v i)+ (separation (v i) (v j):ℝ) := by exact_mod_cast ht
    linarith
  · have ht := separation_triangle (v k) (v j) (v i); rw [separation_comm (v j) (v i)] at ht
    have hh : (separation (v k) (v i):ℝ) ≤ separation (v k) (v j)+ (separation (v i) (v j):ℝ) := by exact_mod_cast ht
    linarith

 -- goal x i sum not reassembled

/-- Coercivity needed (real) as on the actual Frame Hessian. -/
def Firm (A : Matrix ι ι ℝ) (η : ℝ) := ∀ x : ι → ℝ, η * (∑ i, (x i)^2) ≤ dotProduct x (A*ᵥx)

variable [DecidableEq ι]
omit [DecidableEq ι] in
lemma Firm.positive {A : Matrix ι ι ℝ} {η : ℝ} (h : Firm A η) (hp : 0 < η) (he : A.IsSymm) : A.PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.IsSymm] using he
  intro x hx
  rw [star_trivial]
  apply lt_of_lt_of_le (mul_pos hp ?_) (h x)
  obtain ⟨i,hh⟩ : ∃ i, x i ≠ 0 := by contrapose! hx; exact funext hx
  exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i,Finset.mem_univ i, (sq_pos_iff).mpr hh⟩

def cautious (s η C : ℝ) := min (s/2) (s*η/(4*C))






 -- check lemma


end YM.UVNext.PricedKernels
