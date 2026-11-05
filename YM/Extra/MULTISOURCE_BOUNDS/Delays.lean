import YM.Extra.MULTISOURCE_BOUNDS.Singleton

/-!
# Numerical reserve tests for marker histories (stage prices)

Each post-L bound is for ONE fixed finite stage's data but simultaneously all
later values of the entrance parameter and all volumes. Combination (both
sides and adjacent plateaus) in Schedule. `Tariff` powers must be chosen with
genuine sufficient dynamics estimates when using the scheme, not inferred
from `Prepared`. The mixed raw step can be tested at radii smaller by the
post-L factor *before* the L^d rescaling of each name, and cost that factor
*again* as a multiplier outside (but after dividing forced weights). This is
different from multiplying a support-reserve loss into the inductive input
at every step. No other power-counting/exponent sufficiency claim here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Set Function Filter Lattice RG RG.Supply Source Wilson Overlay Marker Labels Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge}
abbrev Sections (L : Frames G) := ∀ d, SectionData (L.level d)
variable {L : Frames G} (T : Sections L)

/-- Pre-L choices. `inflate j`: extra support exponents to pay through
projection up to fine exponent + inflate (can increase to price neighbors
and extra uses). `markers`: max count per site counting all possible
simultaneous names on one request. halo quoted in coarse balls, per fine
location, even on winding supports. -/
structure Scope where
  expand : ℕ → ℕ
  inflate : ℕ → ℝ
  markers : ℕ → ℕ
  positive i : 0 ≤ inflate i
  markers_pos i : 0 < markers i

/-- Post-L, before delay. A polynomial in **hatted beta** on fine side,
allowed because its log is o(B), not a grant to pay unrelated costs in g
powers. Constants frozen by stage (independent of N,p,cover-size, V, number
of prior steps, etc). -/
structure Tariff where
  factor : ℕ → ℝ
  power : ℕ → ℕ
  factor_ge i : 1 ≤ factor i

def ceiling (L : Frames G) (i : ℕ) : ℕ := (Finset.range (i+1)).sup (strength L)

def fee (t : Tariff) (i : ℕ) (x : ℝ) := t.factor i * x ^ t.power i

def steep (F : Frames G) (P : Stage) (R : Side) (t : Tariff) (i : ℕ) (x : ℝ) :=
    ((P.columns^2 * (R.val:ℝ)^i) * (fee t i x)^2) * x^(ceiling F i + 2)

def smallK (x : ℝ) : ℝ := Real.sqrt (Real.exp (-(Real.exp ((Real.log (Real.log x))^2) ^ ((1:ℝ)/5))))

structure Ample (P : Stage) (μ i : ℕ) (x : ℝ) : Prop where
  large : 8 ≤ Stock.scaleB x
  perturb : Vac.Numbers.Hat x ≤ 1/4
  vacuum : smallK x ≤ (Vac.Numbers.Hat x)^6
  singletons : (1+Real.exp P.supportExponent)*Vac.Numbers.Hat x ≤ 1
  contact : (1+μ*siteFactor (Stock.scaleB x))*((Stock.scaleB x+Stock.scaleB x+1:ℕ):ℝ)^4 * Vac.Numbers.Hat x ≤ 1
  atlas d : d ≤ i → BasisCost.extent (T d) ≤ Stock.scaleB x ∧
    Real.exp (P.supportExponent+2) * BasisCost.price (T d) * Vac.Numbers.Hat x ≤ 1

lemma hat_eq {x : ℝ} (hx : 0<x) : Vac.Numbers.Hat x = Real.exp (-(Real.log x/2)) := by
  unfold Vac.Numbers.Hat
  rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring

lemma hat_affords (C : ℝ) (k : ℕ) : ∀ᶠ x : ℝ in atTop, C * (Real.log x / 2)^k * Vac.Numbers.Hat x ≤ 1 := by
  have he : Tendsto (fun x => (1/2:ℝ)*Real.log x) atTop atTop := Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
  have ht := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp he).const_mul C)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ)] with x hx hg
  change C * ((1/2 * Real.log x)^k * _) ≤ 1 at hx
  rw [hat_eq hg,show Real.log x/2=1/2*Real.log x by ring, mul_assoc]; exact hx

lemma vacuum_affords : ∀ᶠ x : ℝ in atTop, smallK x ≤ (Vac.Numbers.Hat x)^6 := by
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 10,
    Real.tendsto_log_atTop.eventually_ge_atTop 6,eventually_gt_atTop (0:ℝ)] with x hx hx' hx''
  have hL : 0<Real.log x := lt_of_lt_of_le (by norm_num) hx'
  let y := Real.log (Real.log x)
  have he : 2*y ≤ y^2 * ((1:ℝ)/5) := by change 10 ≤ y at hx; nlinarith
  have hh : 6*Real.log x ≤ Real.exp (y^2) ^ ((1:ℝ)/5) := by
    apply le_trans _ ((Real.exp_monotone he).trans_eq (Real.exp_mul ..))
    rw [show 2*y=y+y by ring,Real.exp_add,show Real.exp y=Real.log x from Real.exp_log hL]; nlinarith
  unfold smallK; rw [hat_eq hx'',← Real.exp_nat_mul]; apply (Real.sqrt_le_iff ..).mpr
  refine ⟨(Real.exp_pos _).le,?_⟩; rw [← Real.exp_nat_mul,Real.exp_le_exp]; push_cast; linarith only [hh]

lemma scaleB_large (k : ℕ) : ∀ᶠ x : ℝ in atTop, k ≤ Stock.scaleB x := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (k:ℝ))] with x hx
  apply (Nat.cast_le (α:=ℝ)).mp (le_trans ?_ (Nat.le_ceil _))
  have h := max_le_iff.mp hx; nlinarith

lemma site_affords (μ : ℕ) : ∀ᶠ x : ℝ in atTop,
    (1+μ*siteFactor (Stock.scaleB x))*((Stock.scaleB x+Stock.scaleB x+1:ℕ):ℝ)^4 * Vac.Numbers.Hat x ≤ 1 := by
  let C := (1+(μ:ℝ)*Real.exp 1* (178:ℝ)^4) * 11^4
  filter_upwards [hat_affords C 16,Real.tendsto_log_atTop.eventually_ge_atTop 2] with x hx hy
  let y := Real.log x / 2
  have h : 1 ≤ y := by unfold y; linarith
  have he : (Stock.scaleB x:ℝ) ≤ 5 * y^2 := by
    have := Nat.ceil_lt_add_one (sq_nonneg (Real.log x)); unfold Stock.scaleB y; nlinarith
  apply le_trans _ hx
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  push_cast
  calc
    _ ≤ (1+(μ:ℝ)*(Real.exp 1*(178*y^2)^4))*(11*y^2)^4 := by unfold siteFactor; gcongr (_+_*(_*(?_)^4))*(?_)^4 <;> nlinarith
    _ ≤ (y^8+μ*(Real.exp 1*(178*y^2)^4))*(11*y^2)^4 := by gcongr; exact one_le_pow₀ h
    _ = C*y^16 := by unfold C; ring

lemma ample_late (P : Stage) (μ i : ℕ) : ∀ᶠ x in atTop, Ample T P μ i x := by
  have he d (_ : d∈Finset.range (i+1)) := (scaleB_large (BasisCost.extent (T d))).and
      (hat_affords (Real.exp (P.supportExponent+2) * BasisCost.price (T d)) 0)
  filter_upwards [(eventually_all_finset _).mpr he,scaleB_large 8,hat_affords 4 0,vacuum_affords,
    hat_affords (1+Real.exp P.supportExponent) 0,site_affords μ] with x ha hb hh hx hyr ht
  norm_num only [pow_zero,mul_one] at ha hh hyr
  exact ⟨hb,by linarith,hx,hyr,ht,fun d hd => ha _ (mem_range.mpr (by omega))⟩

lemma steep_ge (P : Stage) (R : Side) (t : Tariff) (i : ℕ) {x : ℝ} (hx : 1≤x) : 1 ≤ steep L P R t i x := by
  have hR : (1:ℝ) ≤ R.val := by exact_mod_cast R.property
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ P.columns_ge) (one_le_pow₀ hR))
    (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (t.factor_ge _) (one_le_pow₀ hx)))) (one_le_pow₀ hx)

lemma steep_late (P : Stage) (R : Side) (t : Tariff) (i μ : ℕ) (hμ : 0<μ) (b : ℝ) :
    ∀ᶠ x : ℝ in atTop, steep L P R t i (x+b) ≤ Real.exp ((Stock.scaleB x:ℝ)/(64*μ)) := by
  let n := t.power i * 2 + (ceiling L i + 2)
  let A := P.columns^2 * (R.val : ℝ)^i * (t.factor i)^2
  have hA : 0 ≤ A := by unfold A; positivity
  have he x : steep L P R t i x = A*x^n := by unfold steep A n fee; simp only [pow_add,pow_mul]; ring
  filter_upwards [eventually_ge_atTop (A*(2:ℝ)^n), eventually_ge_atTop |b|,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (64*(μ:ℝ)*(n+1:ℕ))] with x ha hx hx' hv
  have hμ' : (0:ℝ)<μ := Nat.cast_pos.mpr hμ
  rw [he]
  calc
    _ ≤ A*(2*x)^n := by gcongr <;> grind
    _ = (A*(2:ℝ)^n)*x^n := by rw [mul_pow,← mul_assoc]
    _ ≤ x^(n+1) := by rw [pow_succ,mul_comm (x^n)]; gcongr
    _ = Real.exp ((n+1:ℕ)*Real.log x) := by rw [Real.exp_nat_mul,Real.exp_log hx']
    _ ≤ Real.exp ((Stock.scaleB x:ℝ)/(64*μ)) := by
      refine Real.exp_monotone ((le_div_iff₀ (by positivity)).mpr (le_trans ?_ (Nat.le_ceil _)))
      have ht : 0 ≤ Real.log x := le_trans (by positivity) hv
      nlinarith only [hv,ht,mul_le_mul_of_nonneg_right hv ht]

end YM.Extra.Multi
