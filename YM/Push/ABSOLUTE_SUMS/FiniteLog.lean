import Mathlib.Analysis.Calculus.SmoothSeries
import YM.Push.ABSOLUTE_SUMS.Gas
import YM.Push.ABSOLUTE_SUMS.Product



/-!
# Log evaluation with actual absolute hypotheses (I)

Real weights. Evaluate the discrete coefficient recurrence as an ODE on
a real interval, USING absolute forest estimates. Also works for restricted
alphabet (e.g. labels not already excluded). This is not evaluating a
field integral, nor assuming positivity to license opening logs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Gas
open Graph Ursell Coef Trees Filter RG Finset Lattice
open scoped BigOperators Classical Topology
variable {ι : Type*} (R : ι → ι → Prop) (w : ι → ℝ)

def total := ∑' s : Finset ι, value R w s

def term (z : Clusters ι) : ℝ := coefficient R z.2 * (∏ i,w (z.2 i)) / (z.1+1).factorial

def logSum := ∑' z : Clusters ι, term R w z

lemma term_nonneg (z : Clusters ι) : ‖term R w z‖ = clusters R (fun i => ‖w i‖) z.2 := by
  unfold term clusters
  simp [norm_mul,Real.norm_eq_abs]

section Budget
variable {n : Side}

lemma absolute_at (X : ι → Support n) (B : ℕ) (ht : Tests R X) (hX : ∀ i,(X i).Nonempty)
    {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Ready X B (fun i => ‖w i‖) a γ δ q) (m : ℕ) :
    SumBudget (fun i => ‖term R w ⟨m,i⟩‖) (((n.val^4:ℕ)*γ)*q^m) := by
  let g i := ‖w i‖
  let b : ℝ := ((n.val^4:ℕ)*γ)
  let Q (_ : ι) := True
  have he : SumBudget (charge X B (marked Q g) (a+δ)) b := by
    rw [show marked Q g = g by ext; simp [marked,Q]]
    exact Product.everyone_ne X B (fun _ => norm_nonneg _) (fun i _ => hX i) h.2.2.2.2.2
  have ht : SumBudget (fun z : Tuple ι m => clusters R (charge X B g a) z) (b*q^m) := by
    simpa [Q,g] using cluster_at R X B ht Q h he m
  apply budget_mono ht (fun _ => norm_nonneg _)
  intro i; rw [term_nonneg]; unfold clusters g
  have hv (i : ι) : ‖w i‖ ≤ charge X B g a i := le_mul_of_one_le_right (norm_nonneg _)
    (Real.one_le_exp (mul_nonneg ha (by positivity)))
  gcongr
  exact hv _

lemma absolute (X : ι → Support n) (B : ℕ) (ht : Tests R X) (hX : ∀ i,(X i).Nonempty)
    {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Ready X B (fun i => ‖w i‖) a γ δ q) :
    SumBudget (fun z : Clusters ι => ‖term R w z‖) (((n.val^4:ℕ)*γ)*(1-q)⁻¹) :=
  sigma_total _ (fun m => _ * q^m) (absolute_at R w X B ht hX ha h)
    (budget_geometric (mul_nonneg (Nat.cast_nonneg _) h.1.le) (ready_pos X B h).le h.2.2.2.1)
end Budget

section Ode
variable [Fintype ι]

private lemma zero_at (h : Hard R) : gasRow R w 0=1 := by rw [row R w 0 h]; simp [value,separated]

-- Here pure analysis, also useful on sublists; domain reaches 1 since q < 1.
lemma exact_polynomial (hr : Hard R) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (h : q < 1) (he : ∀ m, ‖logRow R w m‖ ≤ C*q^m) :
    Real.exp (∑' m : ℕ, logRow R w m) = ∑ s, value R w s := by
  let u := (1+q⁻¹)/2
  have hu : 1<u := by unfold u; have he := (one_lt_inv₀ hq).2 h; linarith
  have hi : q*u < 1 := by unfold u; rw [← mul_div_assoc,mul_add]; field_simp; linarith
  let L := Set.Ioo (-u) u
  have h0 : 0∈L := ⟨by linarith,by linarith⟩; have h1 : 1∈L := ⟨by linarith,hu⟩
  have hl : IsOpen L := isOpen_Ioo; have hL : IsPreconnected L := (convex_Ioo (-u) u).isPreconnected

  let F n t := logRow R w n * t^(n+1)
  let D (n:ℕ) t := ((n:ℝ)+1)*logRow R w n * t^n
  let log t := ∑' n, F n t
  let slope t := ∑' n, D n t
  let W (n : ℕ) := C*((n:ℝ)+1)*(q*u)^n
  have hk : 0 ≤ q*u := mul_nonneg hq.le (by linarith)
  have hv : ‖q*u‖ < 1 := by rwa [Real.norm_of_nonneg hk]
  have hw : Summable W := by
    have he : Summable fun n : ℕ => ((n:ℝ)^1 * (q*u)^n) + (q*u)^n :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 hv).add (summable_geometric_of_lt_one hk hi)
    apply (he.mul_left C).congr; intro i; unfold W; ring
  have hb n t (ht : t∈L) : ‖D n t‖ ≤ W n := by
    have he' : ‖t‖ ≤ u := by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    unfold D W; simp only [norm_mul, norm_pow]
    rw [Real.norm_of_nonneg (show (0:ℝ) ≤ n+1 by positivity),mul_pow]
    calc
      _ ≤ (n+1)*(C*q^n)*u^n := by gcongr; exact he n
      _ = _ := by ring
  have hd x (hx : x∈L) : HasDerivAt log (slope x) x := by
    refine hasDerivAt_tsum_of_isPreconnected hw hl hL (fun n y hy => ?_) hb h0 ?_ hx
    · convert! (hasDerivAt_pow (n+1) y).const_mul (logRow R w n) using 1; unfold D; push_cast; ring
    simp only [F, pow_succ, mul_zero]; exact summable_zero

  let v n t := gasRow R w n * t^n
  let s := Fintype.card ι
  let P t := ∑ n ∈ range (s+1), v n t
  have hp i (hi : s < i) (t) : v i t = 0 := by unfold v; rw [rows_above R w hr i hi,zero_mul]
  let d (n : ℕ) (t : ℝ) := ((n:ℝ)+1)*gasRow R w (n+1)*t^n
  have hq x : HasDerivAt P (∑ n ∈ range s,d n x) x := by
    let b (n:ℕ) := gasRow R w n * ((n:ℝ)*x^(n-1))
    have he := HasDerivAt.sum (u:=range (s+1)) (A:=v) (A':=b) (x:=x) fun i hi =>
      (hasDerivAt_pow i x).const_mul (gasRow R w i)
    convert! he using 1
    · ext x; simp only [P,Finset.sum_apply]
    rw [Finset.sum_range_succ']; simp only [b, Nat.cast_zero,zero_mul,mul_zero,add_zero]
    apply sum_congr rfl; intro i _; unfold d; push_cast; ring

  have hi x (hx : x∈L) : slope x * P x = ∑ n ∈ range s,d n x := by
    have hw' : Summable fun n : ℕ => ‖v n x‖ := by
      apply summable_of_ne_finset_zero (s:=range (s+1)); intro i hi
      rw [hp i (by have he : s+1 ≤ i := Nat.ge_of_not_lt fun h => hi (mem_range.mpr h); omega),norm_zero]
    have hg : Summable fun n : ℕ => ‖D n x‖ := hw.of_nonneg_of_le (fun i => norm_nonneg _) fun n => hb n x hx
    have hs : P x = ∑' n,v n x := (tsum_eq_sum fun i (hi : i∉range (s+1)) => hp i
      (by simp only [mem_range, not_lt] at hi; omega) x).symm
    unfold slope; rw [hs,tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hg hw']
    have eq (n : ℕ) : ∑ i ∈ range (n+1),D i x*v (n-i) x=d n x := by
      unfold d; rw [recurrence,sum_mul]
      apply sum_congr rfl; intro i hi
      have he : x^i * x^(n-i)=x^n := by rw [← pow_add]; congr; have hh := mem_range.mp hi; omega
      unfold D v; rw [← he]; ring
    simp_rw [eq]
    exact tsum_eq_sum fun i (he : i ∉ range s) => by
      unfold d; rw [rows_above R w hr (i+1) (by simp only [mem_range,not_lt] at he; change s < i+1; omega), mul_zero,zero_mul]

  let H t := P t * Real.exp (-log t)
  have hH x (hx : x∈L) : HasDerivAt H 0 x := by
    convert! (hq x).mul (hd x hx).neg.exp using 1
    rw [← hi x hx]; change 0 = _ * Real.exp _ + P x*(Real.exp _ * -slope x); ring
  have hz : H 1 = H 0 := hl.is_const_of_deriv_eq_zero hL (fun x hx => (hH x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hH x hx).deriv) h1 h0
  have he : H 0=1 := by
    unfold H P log F v
    simp only [pow_succ,mul_zero,tsum_zero,neg_zero,Real.exp_zero,mul_one]
    rw [Finset.sum_range_succ']; simp [zero_at R w hr]
  rw [he] at hz
  unfold H at hz
  have hP : P 1 = ∑ s,value R w s := by simpa only [P,v,s,polyAt,one_pow,mul_one,one_mul] using sums R w 1 hr
  have hf : log 1 = ∑' m,logRow R w m := by simp [log,F]
  rw [hP,hf,Real.exp_neg,← div_eq_mul_inv,div_eq_iff (Real.exp_pos _).ne',one_mul] at hz
  exact hz.symm
end Ode
end YM.Push.AbsoluteSums.Gas
