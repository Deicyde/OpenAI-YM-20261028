import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Stein

/-!
# Finite-dimensional domination for authentication

Not uniform-in-volume through any implicit constants here. See the later
trace estimate for uniform moment costs. A weighted quadratic majorant U
may consume small amounts of precision across *the whole* selected list.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory ProbabilityTheory Filter Function Finset Set
open YM.Multi.Vacuum.Gauss
open scoped Topology BigOperators

variable {J : Type} [Fintype J]

def size (x : Row J) := 1+squares x
lemma size_one (x : Row J) : 1 ≤ size x := le_add_of_nonneg_right (squares_nn x)
lemma size_nn (x : Row J) : 0 ≤ size x := zero_le_one.trans (size_one x)

/-- Exponential currency on a standard-coordinate volume. Do not use its
integral bound as a price. -/
lemma volume_pay {δ : ℝ} (he : δ < 1/4) (k : ℕ) :
    Integrable (fun x : Row J => size x ^ k * Real.exp (δ * squares x)) (standard J) := by
  -- choose epsilon so that k copies pay up to e^(1/4 ||x||²)
  let ε := (1/4-δ)/((k:ℝ)+1)
  have hε : 0 < ε := by unfold ε; positivity
  let C := ε⁻¹ * Real.exp ε
  have hC : 0 < C := by unfold C; positivity
  have hi : Integrable (fun x : Row J => Real.exp ((1/4:ℝ)*squares x)) (standard J) := by
    convert (thermal (t:=fun _ : J => (1/4:ℝ)) (by intro; norm_num) fun _ => le_rfl).1 using 1
    ext x; simp only [squares,pay,Finset.mul_sum]
  apply (hi.const_mul (C^k)).mono' (by apply Continuous.aestronglyMeasurable; unfold size squares; fun_prop)
  filter_upwards with x
  have hs := size_nn x
  rw [Real.norm_of_nonneg (by positivity)]
  have hw : size x ≤ C*Real.exp (ε*squares x) := by
    unfold C
    rw [mul_assoc, ← Real.exp_add, inv_mul_eq_div, le_div_iff₀ hε]
    have ht := Real.add_one_le_exp (ε + ε*squares x); unfold size; linarith
  have h : k*ε + δ ≤ 1/4 := by unfold ε; field_simp; nlinarith
  calc
    _ ≤ (C*Real.exp (ε*squares x)) ^ k * Real.exp (δ*squares x) := by gcongr
    _ ≤ C^k* Real.exp (1/4*squares x) := by
      rw [mul_pow,← Real.exp_nat_mul,mul_assoc,← Real.exp_add,← mul_assoc _ ε,← add_mul]
      gcongr; exact squares_nn x

section growth
variable {E : Type*} {S : Type*}

/-- Uniform up to one of the per-parameter exponents. -/
def Growth [Norm E] (s : Set S) (U : S → Row J → ℝ) (F : S → Row J → E) :=
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t∈s, ∀ x, ‖F t x‖ ≤ C * size x ^ k * Real.exp (U t x)

def ExpPays (s : Set S) (U : S → Row J → ℝ) :=
    ∃ δ : ℝ, δ < 1/4 ∧ ∀ t∈s, ∀ x, U t x ≤ δ * squares x

namespace Growth
variable {s : Set S} {U W : S → Row J → ℝ} {F H : S → Row J → E}

lemma enlarge [Norm E] (h : Growth s U F) (hh : ∀ t∈s, ∀ x,U t x ≤ W t x) : Growth s W F := by
  obtain ⟨k,C,hc,h⟩ := h
  refine ⟨k,C,hc,fun t ht x => (h t ht x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_monotone (hh t ht x)) (mul_nonneg hc (pow_nonneg (size_nn _) _))

lemma plain [Norm E] {C : ℝ} (hC : 0 ≤ C) (h : ∀ t∈s,∀ x,‖F t x‖ ≤ C*Real.exp (U t x)) : Growth s U F :=
  ⟨0,C,hC,fun t ht x => by rw [pow_zero, mul_one]; exact h t ht x⟩

lemma constants [Norm E] {C : ℝ} (v : S → E) (hC : 0 ≤ C) (h : ∀ t∈s,‖v t‖ ≤ C) :
    Growth s (fun _ (_ : Row J) => 0) (fun t _ => v t) := plain hC fun t ht x => by
  rw [Real.exp_zero,mul_one]; exact h t ht

lemma sum_two [NormedAddCommGroup E] (h : Growth s U F) (hh : Growth s U H) :
    Growth s U (fun t x => F t x + H t x) := by
  obtain ⟨k,C,hc,h⟩ := h; obtain ⟨l,D,hd,hh⟩ := hh
  refine ⟨max k l,C+D,add_nonneg hc hd,fun t ht x => ?_⟩
  apply le_trans ((norm_add_le ..).trans (add_le_add (h t ht x) (hh t ht x)))
  have hx := size_one x
  simp only [add_mul]
  gcongr
  · exact le_max_left ..
  exact le_max_right ..



lemma real_mul [NormedAddCommGroup E] [NormedSpace ℝ E] {v : S → Row J → ℝ} (hv : Growth s (fun _ _ => 0) v)
    (h : Growth s U F) : Growth s U (fun t x => v t x • F t x) := by
  obtain ⟨k,C,hc,h⟩ := h; obtain ⟨l,D,hd,hv⟩ := hv
  simp_rw [Real.exp_zero,mul_one] at hv
  refine ⟨l+k,D*C,mul_nonneg hd hc,fun t ht x => ?_⟩
  rw [norm_smul]
  apply le_trans (mul_le_mul (hv t ht x) (h t ht x) (norm_nonneg _) ((norm_nonneg _).trans (hv t ht x)))
  rw [pow_add]; exact le_of_eq (by ring)

lemma sum_many [NormedAddCommGroup E] {A : Type*} (a : Finset A) (v : A → S → Row J → E)
    (h : ∀ i∈a,Growth s U (v i)) : Growth s U (fun t x => ∑ i∈a,v i t x) := by
  classical
  induction a using Finset.induction_on with
  | empty => simp only [sum_empty]; exact plain (C:=0) le_rfl fun _ _ _ => by simp
  | insert i a hi ih =>
    simp only [sum_insert hi]; exact (h i (mem_insert_self ..)).sum_two
      (ih fun j hj => h j (mem_insert_of_mem hj))



lemma lines {q : S → Row J} {M : ℝ} (hm : 0 ≤ M) (h : ∀ t∈s,squares (q t)≤M) :
    Growth s (fun _ _ => 0) (fun t x => crossed (q t) x) := by
  refine ⟨1,1+M,by positivity,fun t ht x => ?_⟩
  rw [Real.exp_zero,pow_one,mul_one,Real.norm_eq_abs]
  have hu := squares_nn x
  have hx := (csq (q t) x).trans (mul_le_mul_of_nonneg_right (h t ht) hu)
  unfold size; rw [← sq_abs] at hx; nlinarith

lemma dominating [Norm E] (h : Growth s U F) (hu : ExpPays s U) :
    ∃ g : Row J → ℝ, Integrable g (standard J) ∧ ∀ t∈s,∀ x,‖F t x‖ ≤ g x := by
  obtain ⟨δ,hd,hh⟩ := hu
  obtain ⟨k,C,hc,h⟩ := h.enlarge hh
  refine ⟨_,(volume_pay hd k).const_mul C, fun t ht x => ?_⟩
  simpa only [mul_assoc] using h t ht x

lemma integrable [NormedAddCommGroup E] {y : S} (h : Growth s U F) (hu : ExpPays s U) (hy : y ∈ s)
    (he : Continuous (F y)) : Integrable (F y) (standard J) := by
  obtain ⟨b,hb,hh⟩ := h.dominating hu
  exact hb.mono' he.aestronglyMeasurable (Filter.Eventually.of_forall (hh y hy))

lemma continuity [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace S] [FirstCountableTopology S]
    (h : Growth s U F) (hu : ExpPays s U)
    (hm : ∀ t∈s, Continuous (F t)) (hd : ∀ x, ContinuousOn (fun t => F t x) s) :
    ContinuousOn (fun t => ∫ x,F t x ∂standard J) s := by
  obtain ⟨b,hb,hh⟩ := h.dominating hu
  exact continuousOn_of_dominated (fun t ht => (hm t ht).aestronglyMeasurable)
    (fun t ht => Filter.Eventually.of_forall (hh t ht)) hb (Filter.Eventually.of_forall hd)

lemma derivative [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : ℝ → Row J → ℝ} {F F' : ℝ → Row J → E} {y : ℝ} {s : Set ℝ} (h : Growth s U F)
    (hv : Growth s U F') (hu : ExpPays s U) (hs : s ∈ nhds y)
    (hm : ∀ t∈s, Continuous (F t)) (hh : Continuous (F' y))
    (hd : ∀ x, ∀ t ∈ s, HasDerivAt (fun t => F t x) (F' t x) t) :
    HasDerivAt (fun t => ∫ x,F t x ∂standard J) (∫ x,F' y x ∂standard J) y := by
  have hy := mem_of_mem_nhds hs
  obtain ⟨b,hb,ht⟩ := hv.dominating hu
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs ?_
    (h.integrable hu hy (hm y hy)) hh.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t he => ht t he x) hb (Filter.Eventually.of_forall hd)).2
  filter_upwards [hs] with t ht
  exact (hm t ht).aestronglyMeasurable
end Growth
end growth
end YM.Primitives.GCC
