import YM.Further.THRESHOLD_SOURCE_RESTART.ClusterDisk
import YM.Further.THRESHOLD_SOURCE_RESTART.ClusterPower


/-!
# Evaluating the finite-alphabet marked log series

Even with unmarked components repeating arbitrarily. Verify by ODE,
as in `YM.Push.ABSOLUTE_SUMS` for scalars. Radius-margin hypothesis
suffices for the derivatives through to t=1. (The vertices here will be
UNforced components incl those with no markers, nothing asserted about
positivity/normalization of any forced coefficient.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Clusters
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi Repeated
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {α V : Type*} [Fintype V] [DecidableEq V] {n : Side}
variable (X : α → Support n) (W : α → Marks.Algebra V)

section Ode
variable [Fintype α]
-- as in ClusterPower
local instance : NormedSpace ℝ (Marks.Algebra V) := inferInstanceAs (NormedSpace ℝ ((Marks.all V).Mode→ℂ))
local instance : IsScalarTower ℝ ℂ (Marks.Algebra V) := inferInstanceAs (IsScalarTower ℝ ℂ ((Marks.all V).Mode→ℂ))
local instance : IsTopologicalSemiring (Marks.Algebra V) := {}

private lemma pulse (t : ℝ) (x : Marks.Algebra V) (i : ℕ) :
    HasDerivAt (fun s : ℝ => ((s^i:ℝ):ℂ) • x) ((↑((i:ℝ)*t^(i-1)):ℂ) • x) t :=
  (hasDerivAt_pow i t).ofReal_comp.smul_const x

private lemma finite_products {F G : ℕ → Marks.Algebra V} (h : Summable fun i => ‖F i‖) (l : Finset ℕ)
    (he : ∀ i,i∉l → G i=0) : Summable fun i : ℕ×ℕ => F i.1*G i.2 := by
  apply Summable.of_norm
  let f i j := ‖F i*G j‖
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  have hh j : Summable (fun i => f i j) := by
    let X := LinearMap.toContinuousLinearMap (Algebra.lmul ℂ _ (G j))
    refine (h.mul_left ‖X‖).of_nonneg_of_le (fun i => norm_nonneg _) fun i => ?_
    unfold f; rw [mul_comm]; exact X.le_opNorm _
  have hz i j (ht : j∉l) : f i j=0 := by unfold f; rw [he _ ht,mul_zero,norm_zero]
  refine ⟨fun i => summable_of_ne_finset_zero (hz i),?_⟩
  apply (summable_sum (s:=l) (f:=fun i j => f j i) (fun i _ => hh i)).congr
  exact fun i => (tsum_eq_sum (hz i)).symm

private lemma charge_ode (C : ℝ) (hp : ∀ m, ‖pSum X W m‖ ≤ C*(1/2:ℝ)^m) :
    electric (∑' m,pSum X W m) = ∑ s, formed X W s := by
  let s : ℝ := 3/2
  have hs : 0 ≤ s := by unfold s; norm_num
  let S := Ioo (-s) s
  let F i (x : ℝ) := ((x^(i+1):ℝ):ℂ) • pSum X W i
  let D (i : ℕ) (x : ℝ) := (↑(((i:ℝ)+1)*x^i):ℂ) • pSum X W i
  let y (i : ℕ) := C*((i:ℝ)+1)*(s/2)^i
  have h (x : ℝ) (hx : x∈S) (i : ℕ) : ‖D i x‖≤ y i := by
    have he : |x|≤s := abs_le.mpr ⟨hx.1.le,hx.2.le⟩
    unfold D; rw [norm_smul, Complex.norm_real,Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤↑i+1),abs_pow]
    calc
      _ ≤ (((i:ℝ)+1)*s^i)*(C*(1/2)^i) := by gcongr; exact hp i
      _ = y i := by unfold y; rw [show s/2=s*(1/2) by ring,mul_pow]; ring
  have hy : Summable y := by
    have he : ‖s/2‖ < 1 := by unfold s; norm_num
    apply ((Summable.add (summable_pow_mul_geometric_of_norm_lt_one 1 he) (summable_geometric_of_norm_lt_one he)).mul_left C).congr
    intro i; unfold y; ring
  let f x := ∑' i,F i x
  let d x := ∑' i,D i x
  have h0 : (0:ℝ)∈S := by simp [s,S]
  have h1 : (1:ℝ)∈S := by unfold S s; norm_num
  have ho : IsOpen S := isOpen_Ioo
  have hv := (convex_Ioo (-s) s).isPreconnected
  have hf x (hx : x∈S) : HasDerivAt f (d x) x := by
    refine hasDerivAt_tsum_of_isPreconnected hy ho hv (fun i x h => ?_) (fun i x hx => h x hx i) h0 ?_ hx
    · have H := pulse x (pSum X W i) (i+1)
      simpa only [F,D,Nat.add_sub_cancel, Nat.cast_add,Nat.cast_one] using H
    simp only [F,pow_succ,mul_zero,Complex.ofReal_zero,zero_smul]; exact summable_zero

  let k := Fintype.card α
  let A i (x : ℝ) := (↑(x^i):ℂ) • cSum X W i
  let H x := ∑ i∈Finset.range (k+1), A i x
  let E (i : ℕ) (x : ℝ) := (↑(((i:ℝ)+1)*x^i):ℂ) • cSum X W (i+1)
  have hd x : HasDerivAt H (∑ i∈Finset.range k,E i x) x := by
    convert! HasDerivAt.fun_sum (u:=Finset.range (k+1)) (A:=A) (A':=fun i=> (↑((i:ℝ)*x^(i-1)):ℂ) • cSum X W i)
      (fun i _=> pulse x _ i) using 1
    rw [Finset.sum_range_succ']; simp [E]
  have he (x : ℝ) (i) (hi : i∉Finset.range (k+1)) : A i x=0 := by
    have he : k+1 ≤ i := Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h))
    unfold A; rw [run_out _ _ _ he,smul_zero]
  have hm x (hx : x∈S) : d x * H x = ∑ i∈Finset.range k,E i x := by
    have hh : Summable (fun i => ‖D i x‖) := hy.of_nonneg_of_le (fun i => norm_nonneg _) (h x hx)
    have ha : Summable fun i => A i x := summable_of_ne_finset_zero (he x)
    have HT : Summable (fun i : ℕ×ℕ => D i.1 x * A i.2 x) := finite_products (F:=fun i => D i x) (G:=fun i=>A i x) hh _ (he x)
    have HE := hh.of_norm.tsum_mul_tsum_eq_tsum_sum_range ha HT
    rw [show H x=∑' i,A i x from (tsum_eq_sum (he x)).symm]; change (∑' i,D i x) * _=_; rw [HE]
    have h (i) : ∑ j∈Finset.range (i+1), D j x * A (i-j) x= E i x := by
      have hz : E i x=(↑(x^i):ℂ) • (((i+1:ℕ):ℂ) • cSum X W (i+1)) := by unfold E; rw [smul_smul]; congr 1; push_cast; ring
      rw [hz, row_cost, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro j hj
      unfold D A; rw [smul_mul_smul_comm, Algebra.smul_mul_assoc,smul_smul]; congr 1
      rw [show x^i=x^j*x^(i-j) by rw [←pow_add]; congr; have hh := Finset.mem_range.mp hj; omega]
      push_cast; ring
    simp_rw [h]; apply tsum_eq_sum; intro i hi
    unfold E; rw [run_out _ _ _ (by change k < i+1; exact Nat.lt_succ_of_le (Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h)))),smul_zero]

  let Y x := H x * electric (-f x)
  have hz x (hx : x∈S) : HasDerivAt Y 0 x := by
    rw [show (0:Marks.Algebra V)=(∑ i∈Finset.range k,E i x)*electric (-f x) + H x * (electric (-f x)*(-d x)) by rw [← hm x hx]; ring]
    exact current_product (hd _) (express_deriv (f:=fun v => -f v) (hf x hx).neg)
  have heq := ho.is_const_of_deriv_eq_zero hv (fun x hx => (hz x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hz x hx).deriv) h1 h0
  have hh : Y 0=1 := by
    unfold Y f F H A; rw [Finset.sum_range_succ']; simp [no_power,unity]
  change Y 1 = Y 0 at heq
  rw [hh] at heq
  change H 1 * electric (-f 1)=1 at heq
  have he' := congr_arg (· * electric (f 1)) heq
  rw [mul_assoc,power_cancel,mul_one,one_mul,show H 1= _ from ?_, show f 1 = ∑' m,pSum X W m by simp [f,F]] at he'
  · exact he'.symm
  unfold H
  simpa only [A,one_pow,Complex.ofReal_one,one_smul] using disk X W

omit [Fintype α] in
lemma governed (i) : ‖ink X (fun i => (2:ℂ) • W i) i‖=(2:ℝ)^(i.1+1)* ‖ink X W i‖ := by
  have H : ink X (fun i => (2:ℂ) • W i) i = (2:ℂ)^(i.1+1) • ink X W i := by
    unfold ink; rw [← Finset.smul_prod Finset.univ (2:ℂ) (fun j => W (i.2 j)), smul_comm _ _ (∏ j, W (i.2 j)),
      Finset.card_univ, Fintype.card_fin]
  rw [H,norm_smul,norm_pow,Complex.norm_two]

omit [Fintype α] in
lemma tighten (H : Summable fun i => ‖ink X (fun i => (2:ℂ) • W i) i‖) :
    Summable fun i => ‖ink X W i‖ := H.of_nonneg_of_le (fun _ => norm_nonneg _) fun i =>
  (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_two))).trans_eq (governed X W i).symm

theorem authorized (H : Summable fun i => ‖ink X (fun i => (2:ℂ) • W i) i‖) :
    electric (∑' i,ink X W i)=∑' s,formed X W s := by
  have he := (tighten X W H).of_norm
  rw [he.tsum_sigma,tsum_fintype (formed X W)]
  let Y := fun i => ‖ink X (fun i => (2:ℂ) • W i) i‖
  apply charge_ode X W (∑' i,Y i); intro m
  have hu : (∑ f : Fin (m+1)→ α,Y ⟨m,f⟩) ≤ ∑' i,Y i := by
    rw [H.tsum_sigma, ← tsum_fintype (L:=SummationFilter.unconditional _) ]; exact H.sigma.le_tsum m fun _ _ => tsum_nonneg fun i => norm_nonneg _
  calc
    _ ≤ ∑ f : Fin (m+1)→α, ‖ink X W ⟨m,f⟩‖ := by rw [pSum,tsum_fintype]; exact norm_sum_le _ _
    _ ≤ ∑ f : Fin (m+1)→α, Y ⟨m,f⟩ * (1/2:ℝ)^m := by
      apply Finset.sum_le_sum; intro i _; unfold Y; rw [governed]
      have hx : (0:ℝ)<2^m := by positivity
      dsimp only; rw [div_pow,pow_succ]; rw [mul_comm (2^m*2), mul_assoc ‖ink _ _ _‖]
      apply le_mul_of_one_le_right (norm_nonneg _)
      simp only [one_pow]; field_simp; norm_num
    _ ≤ _ := by rw [← Finset.sum_mul]; gcongr
end Ode
end YM.Further.ThresholdSourceRestart.Clusters
