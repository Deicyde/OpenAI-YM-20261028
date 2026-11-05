import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Growth

/-!
# Shared exponential moment bill for all selections

For the later terminal moments on MANY replica fields. Bounding using the
auxiliary entire volume exponent would add an artificial factor exponential
in number of coordinates. Bound instead by the true weighted trace. Keep the
same row-sum gap for future Gaussian bridge steps: the cross entries can lose
mass in the bridge but not gain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
namespace Quadratic
open MeasureTheory Function Filter Finset Set
open YM.Multi.Vacuum.Gauss
open scoped Topology BigOperators

variable {ι J : Type} [Fintype J] (s : Finset ι) (q : ι → Row J) (w : ι → ℝ)

def exponent (x : Row J) := ∑ i∈s,w i * crossed (q i) x ^ 2

def trace := ∑ i∈s,w i * squares (q i)

/-- Hypothesis only on the physical input covariance entries that receive
weights. For convenience take one fixed numerical margin. -/
structure Ready : Prop where
  pos i (hi : i∈s) : 0 ≤ w i
  bill i (hi : i∈s) : ∑ j∈s,w j * |crossed (q i) (q j)| ≤ 1/8

def pull (x : Row J) : Row J := fun j => ∑ i∈s,w i* crossed (q i) x * q i j

lemma nn (h : Ready s q w) (x : Row J) : 0 ≤ exponent s q w x :=
  sum_nonneg fun i hi => mul_nonneg (h.pos i hi) (sq_nonneg _)

lemma plane_pull (x y : Row J) : crossed (pull s q w x) y =
    ∑ i∈s, w i* crossed (q i) x * crossed (q i) y := by
  change ∑ i, _ * y i=_
  unfold pull; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; refine sum_congr rfl fun i _ => ?_
  generalize w i * crossed (q i) x=c
  unfold crossed; rw [Finset.mul_sum]; simp_rw [mul_assoc]

lemma pull_pays (h : Ready s q w) (x : Row J) : squares (pull s q w x) ≤ 1/8*exponent s q w x := by
  let y i := crossed (q i) x
  let c i j := crossed (q i) (q j)
  let L i j := w i * y i ^ 2 * (w j * |c i j|)
  have he (i : ι) (hi : i∈s) (j : ι) (hj : j∈s) :
      2*(w i*y i * (w j*y j * c j i)) ≤ L i j+L j i := by
    have hi := h.pos i hi; have hj := h.pos j hj
    have ht : 2*y i*(y j*c j i) ≤ (y i^2+y j^2)*|c j i| := by
      by_cases hh : 0 ≤ c j i
      · rw [abs_of_nonneg hh]; nlinarith [mul_nonneg hh (sq_nonneg (y i-y j))]
      rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hh))]; nlinarith [mul_nonpos_of_nonpos_of_nonneg
        (le_of_lt (lt_of_not_ge hh)) (sq_nonneg (y i+y j))]
    unfold L; rw [show c i j=c j i from crossed_comm ..]
    calc
      _ = w i*w j*(2*y i*(y j*c j i)) := by ring
      _ ≤ w i*w j*((y i^2+y j^2)*|c j i|) := mul_le_mul_of_nonneg_left ht (mul_nonneg hi hj)
      _ = _ := by ring
  have hb i (hi : i∈s) : ∑ j∈s,L i j ≤ w i*y i^2*(1/8) := by
    unfold L; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h.bill i hi)
      (mul_nonneg (h.pos i hi) (sq_nonneg _))
  have hh := sum_le_sum hb
  rw [exponent]
  rw [← crossed_self, plane_pull]
  have hr i : crossed (q i) (pull s q w x) = ∑ j∈s,w j*y j * c j i := by rw [crossed_comm,plane_pull]
  simp_rw [hr,Finset.mul_sum]
  have hx : ∑ i∈s,∑ j∈s,(2*(w i*y i * (w j*y j * c j i))) ≤ ∑ i∈s,∑ j∈s,(L i j+L j i) :=
    sum_le_sum fun i hi => sum_le_sum fun j hj => he i hi j hj
  simp_rw [← mul_sum,sum_add_distrib] at hx
  rw [sum_comm (f:=fun i j => L j i)] at hx
  rw [← sum_mul] at hh
  change ∑ i∈s, ∑ j∈s, w i*y i*_ ≤ _
  change _ ≤ ∑ i∈s,(1/8)*(w i*y i^2)
  simp_rw [← mul_sum]; linarith

lemma ready_pays (h : Ready s q w) (x : Row J) : exponent s q w x ≤ 1/8*squares x := by
  have he : crossed (pull s q w x) x = exponent s q w x := by
    rw [plane_pull,exponent]; simp_rw [pow_two,mul_assoc]
  have ha := (csq (pull s q w x) x).trans (mul_le_mul_of_nonneg_right (pull_pays s q w h x) (squares_nn x))
  rw [he] at ha
  have hh := squares_nn x; nlinarith

-- For the cost of integrating *uniformly*.

def exponentGrad (x : Row J) := (2:ℝ) • plane (pull s q w x)
lemma has_exponentGrad (x : Row J) : HasFDerivAt (exponent s q w) (exponentGrad s q w x) x := by
  convert! HasFDerivAt.sum (u:=s) (fun i _ => ((crossed_deriv (q i) x).pow 2).const_mul (w i)) using 1
  · ext y; simp only [exponent,Finset.sum_apply]
  unfold exponentGrad
  ext v
  simp [plane_read,plane_pull,Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_; ring
lemma exponent_cont : Continuous (exponent s q w) :=
  (show Differentiable ℝ (exponent s q w) from fun x => (has_exponentGrad s q w x).differentiableAt).continuous

section
variable (h : Ready s q w)

private def heat (t : ℝ) (x : Row J) := Real.exp (t * exponent s q w x)
private lemma heat_cont (t : ℝ) : Continuous (heat s q w t) :=
  Real.continuous_exp.comp (continuous_const.mul (exponent_cont ..))

include h in
private lemma heat_growth :
    let S : Set ℝ := Set.Ioo (-1) (3/2)
    let U (t : ℝ) x := t * exponent s q w x
    ExpPays S U ∧ Growth S (fun _ (_ : Row J) => 0) (fun (_ : ℝ) => exponent s q w) ∧ Growth S U (heat s q w) := by
  intro S U
  refine ⟨⟨3/16,by norm_num,?_⟩, ?_, Growth.plain (C:=1) zero_le_one ?_⟩
  · intro t ht x
    calc
      U t x ≤ 3/2*exponent s q w x := mul_le_mul_of_nonneg_right (le_of_lt ht.2) (nn s q w h x)
      _ ≤ 3/16*squares x := by linarith [ready_pays s q w h x]
  · refine ⟨1,1,zero_le_one,fun _ _ x => ?_⟩
    rw [Real.norm_of_nonneg (nn s q w h _), Real.exp_zero,mul_one, one_mul, pow_one]
    unfold size; linarith [ready_pays s q w h x,squares_nn x]
  intro t ht x; unfold heat U; rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]

private def hot (t : ℝ) (x : Row J) := exponent s q w x * heat s q w t x

include h in
private lemma heat_deriv (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    Integrable (heat s q w t) (standard J) ∧ Integrable (hot s q w t) (standard J) ∧
    HasDerivAt (fun u => ∫ x,heat s q w u x ∂standard J) (∫ x, hot s q w t x ∂standard J) t := by
  obtain ⟨he,hf,hg⟩ := heat_growth s q w h
  have h0 : (-1:ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
  have h1 : t < 3/2 := lt_of_le_of_lt ht.2 (by norm_num)
  have hh (t : ℝ) : Continuous (hot s q w t) := (exponent_cont ..).mul (heat_cont ..)
  have hi := hf.real_mul hg
  refine ⟨hg.integrable he ⟨h0,h1⟩ (heat_cont ..), hi.integrable he ⟨h0,h1⟩ (hh t),
      hg.derivative hi he (IsOpen.mem_nhds isOpen_Ioo ⟨h0,h1⟩) (fun t _ => heat_cont ..) (hh t) ?_⟩
  intro x v hv
  convert! ((hasDerivAt_id v).mul_const (exponent s q w x)).exp using 1
  change _ * _ = Real.exp _ * _
  rw [one_mul,mul_comm]; rfl

private def rise (t : ℝ) (i : ι) (x : Row J) :=
  (squares (q i) + 2*t*(crossed (q i) x * crossed (pull s q w x) (q i))) * heat s q w t x

include h in
private lemma heat_stein (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) (i : ι) :
    Integrable (rise s q w t i) (standard J) ∧
    Integrable (fun x => crossed (q i) x ^ 2 * heat s q w t x) (standard J) ∧
    (∫ x,crossed (q i) x ^ 2 * heat s q w t x ∂standard J) = ∫ x,rise s q w t i x ∂standard J := by
  let S : Set ℝ := Set.Ioo (-1) (3/2)
  let X := crossed (q i)
  obtain ⟨he,hf,hg⟩ := heat_growth s q w h
  let U (t : ℝ) x := t * exponent s q w x
  let L : ℝ → Row J → ℝ := fun _ _ => 0
  have hp j : Growth S L (fun (_ : ℝ) => crossed (q j)) := Growth.lines (squares_nn _) fun _ _ => le_rfl
  have hg' : Growth S U (fun t x => X x * heat s q w t x) := (hp i).real_mul hg
  have H₀ := (hp i).real_mul hg'
  have h0 : (-1:ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
  have h1 : t < 3/2 := lt_of_le_of_lt ht.2 (by norm_num)
  let g x := X x * heat s q w t x
  have hm' (x) := (((has_exponentGrad s q w x).const_mul t).exp)
  have hm x := (crossed_deriv (q i) x).mul (hm' x)
  have hd : Differentiable ℝ g := fun x => (hm x).differentiableAt
  have Hdg x : fderiv ℝ g x (q i) = rise s q w t i x := by
    rw [show fderiv ℝ g x=_ from (hm x).fderiv]
    simp [rise,heat,exponentGrad,smul_apply,plane_read,crossed_self]
    ring
  have hI0 : Integrable g (standard J) := hg'.integrable he ⟨h0,h1⟩ hd.continuous
  have hI1 : Integrable (fun x => X x • g x) (standard J) :=
    H₀.integrable he ⟨h0,h1⟩ ((crossed_cont ..).smul hd.continuous)
  have hconst (c : ℝ) : Growth S L (fun (_ : ℝ) (_ : Row J) => c) := Growth.constants _ (norm_nonneg _) fun _ _ => le_rfl
  have hi : Growth S L (fun (_ : ℝ) x => crossed (pull s q w x) (q i)) := by
    simp only [plane_pull, show ∀ j x,w j * crossed (q j) x * crossed (q j) (q i)=
      (w j*crossed (q j) (q i)) • crossed (q j) x from fun _ _ => by rw [smul_eq_mul,mul_right_comm]]
    exact Growth.sum_many _ _ fun j _ => (hconst _).real_mul (hp j)
  have hy : Growth S L (fun t _ => 2*t) := Growth.constants _ (C:=4) (by positivity) fun t h => by
    rw [Real.norm_eq_abs,abs_le]; constructor <;> linarith [h.1,h.2]
  have hI2 : Integrable (rise s q w t i) (standard J) := by
    have h' := ((hconst (squares (q i))).sum_two (hy.real_mul ((hp i).real_mul hi))).real_mul hg
    apply h'.integrable he ⟨h0,h1⟩
    change Continuous (rise s q w t i)
    unfold rise heat exponent pull squares crossed; fun_prop
  have hs (x : Row J) : X x • g x=crossed (q i) x ^ 2 * heat s q w t x := by
    unfold g X; rw [smul_eq_mul, ← mul_assoc, pow_two]
  have H := weighted_stein (q i) g hd hI0 hI1 (by simp_rw [Hdg]; exact hI2)
  rw [show (fun x => crossed (q i) x • g x) = _ from funext hs] at H
  simp_rw [Hdg] at H
  simp_rw [hs] at hI1
  exact ⟨hI2,hI1,H⟩

include h in
private theorem heat_bill (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    (∫ x,hot s q w t x ∂standard J) ≤ (2*trace s q w) * ∫ x,heat s q w t x ∂standard J := by
  let F := heat s q w t; let G := hot s q w t; let T := trace s q w
  let M := standard J
  obtain ⟨ha,hb,-⟩ := heat_deriv s q w h t ht
  have he (x) : (G x) = ∑ i∈s,w i * (crossed (q i) x ^ 2 * F x) := by
    unfold G F hot exponent; rw [Finset.sum_mul]; simp_rw [mul_assoc]
  have ht' i (hi : i∈s) := heat_stein s q w h t ht i
  have hi (x) : ∑ i∈s, w i * rise s q w t i x = T*F x + (2*t*squares (pull s q w x))*F x := by
    unfold rise; rw [← crossed_self (pull s q w x),plane_pull]
    unfold T F trace; simp only [Finset.mul_sum,Finset.sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [crossed_comm (pull s q w x)]; ring
  have hf x : ∑ i∈s,w i*rise s q w t i x ≤ T*F x + 1/2*G x := by
    rw [hi]
    have hh := pull_pays s q w h x
    have hp := nn s q w h x
    apply add_le_add_right
    change _ ≤ 1/2*(exponent s q w x * F x)
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    nlinarith only [hp,ht.2, mul_le_mul_of_nonneg_left hh ht.1, mul_le_mul_of_nonneg_right ht.2 hp]
  have hx : (∫ x,G x ∂M) ≤ T*(∫ x,F x ∂M)+1/2*(∫ x,G x ∂M) := by
    calc
      _ = ∑ i∈s, w i*∫ x,rise s q w t i x ∂M := by
        rw [funext he,integral_finsetSum]
        · apply sum_congr rfl; intro i hl; rw [integral_const_mul]; exact congr_arg (w i * ·) (ht' i hl).2.2
        exact fun i hi => (ht' i hi).2.1.const_mul _
      _ ≤ ∫ x,T*F x+1/2*G x ∂M := by
        have hh : ∀ i ∈ s, Integrable (fun x => w i*rise s q w t i x) M := fun i hi => (ht' i hi).1.const_mul _
        apply le_trans (b := ∫ x, (∑ i∈s,w i*rise s q w t i x) ∂M) _ (integral_mono (integrable_finsetSum _ hh)
          ((ha.const_mul T).add (hb.const_mul _)) hf)
        rw [integral_finsetSum _ hh]; simp_rw [integral_const_mul]; exact le_rfl
      _ = _ := by rw [integral_add (ha.const_mul _) (hb.const_mul _),integral_const_mul,integral_const_mul]
  change (∫ x,G x ∂M) ≤ (2*T) * ∫ x,F x ∂M
  linarith

/-- Joint ordinary exponential moment payment, counting trace on the
actual list of uses with their small weights `w`, not number of dimensions. -/
theorem authentic (h : Ready s q w) :
    Integrable (fun x => Real.exp (exponent s q w x)) (standard J) ∧
    (∫ x,Real.exp (exponent s q w x) ∂standard J) ≤ Real.exp (2*trace s q w) := by
  refine ⟨?_,?_⟩
  · have he : heat s q w 1=fun x => Real.exp (exponent s q w x) := by funext x; simp only [heat,one_mul]
    rw [← he]
    exact (heat_deriv s q w h 1 (by constructor <;> norm_num)).1
  let M := standard J
  let T := 2*trace s q w
  let f t := Real.exp (-T*t) * ∫ x,heat s q w t x ∂M
  let g t := Real.exp (-T*t) * ((∫ x,hot s q w t x ∂M)-T*∫ x,heat s q w t x ∂M)
  have he (t) (ht : t∈Set.Icc (0:ℝ) 1) : HasDerivAt f (g t) t := by
    have h1 := (((hasDerivAt_id t).const_mul (-T)).exp).mul (heat_deriv s q w h t ht).2.2
    convert! h1 using 1; unfold g M; dsimp only [id_eq]; ring
  have ht : AntitoneOn f (Set.Icc (0:ℝ) 1) := antitoneOn_of_deriv_nonpos (convex_Icc ..)
    (fun t ht => (he t ht).continuousAt.continuousWithinAt)
    (fun t ht => (he t (interior_subset ht)).differentiableAt.differentiableWithinAt) (fun t ht => by
      rw [(he t (interior_subset ht)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (heat_bill s q w h t (interior_subset ht))))
  have hh := ht (a:=0) (b:=1) (by constructor <;> norm_num) (by constructor <;> norm_num) zero_le_one
  unfold f heat at hh; simp only [mul_one, Real.exp_neg, mul_zero, zero_mul, Real.exp_zero,
    one_mul,integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one] at hh
  change _ ≤ Real.exp T
  rw [inv_mul_eq_div, div_le_iff₀ (Real.exp_pos T),one_mul] at hh
  exact hh

end
end Quadratic
end YM.Primitives.GCC
