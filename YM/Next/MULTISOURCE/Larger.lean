import YM.Next.MULTISOURCE.Grades


/-! Uniform over smaller discs follows from ANY pointwise absolute bound on the bigger disc.
    No radius/all-orders estimate is being hidden at infinite degree. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open MvPolynomial Function Finset Filter RG
open scoped Topology BigOperators
variable {I X : Type*} [Fintype I] [DecidableEq I]

def boxes (r : ℝ) : Set (I→ℂ) := {z | ∀ i, ‖z i‖≤r}

lemma nuclear {C η : ℝ} (P : X → Wave I) (H : ∀ z∈ boxes η, ∀ V : Finset X, (∑ i∈V,‖eval z (P i)‖) ≤ C)
    (h : 0 < η) (q : Grade I) : SumBudget (fun i => ‖coeff q (P i)‖) ((price (fun _ => η) q)⁻¹ * C) := by
  classical
  let r (_ : I) := η
  have hp : 0 < price r q := price_pos _ _ (fun _ _ => h)
  have he (V : Finset X) : (∑ i ∈ V, ‖coeff q (P i)‖) ≤ (price r q)⁻¹*C := by
    obtain ⟨N,hN,hs,hq⟩ := span (V.biUnion fun i => (P i).support) q
    have hh (i) (hi : i∈V) : ‖coeff q (P i)‖ ≤
        ∑ j : Cir I N, ‖load r N j q‖ * ‖eval (looped r N j) (P i)‖ := by
      rw [display r q (P i) hN hp hs (fun y hy => hq y (mem_biUnion.mpr ⟨i,hi,hy⟩))]
      simp_rw [← norm_mul]; apply norm_sum_le
    apply le_trans (sum_le_sum hh)
    rw [sum_comm,← total r q hp hN, Finset.sum_mul]
    apply Finset.sum_le_sum; intro b _; rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (H _ (fun i => (circle_val r N _ (fun i => h.le) hN i).le) V) (norm_nonneg _)
  exact ⟨fun _ => norm_nonneg _,summable_of_sum_le (fun i => norm_nonneg _) he,
    Real.tsum_le_of_sum_le (fun i => norm_nonneg _) he⟩

lemma listings {r : ℝ} (hq : 0 < r) (hp : r < 1) : Summable fun q : Grade I => price (fun _ => r) q := by
  classical
  apply summable_of_sum_le (c:=∏ _i : I, ∑' n : ℕ, r^n) (fun i => (price_pos _ i fun _ _ => hq).le)
  intro V
  obtain ⟨N,hN,-,hh⟩ := span V 0
  haveI : NeZero N := ⟨hN.ne'⟩
  let S (p : Grade I) (i : I) : Fin N := ⟨p i % N,Nat.mod_lt _ hN⟩
  let g (p : I→Fin N) := ∏ i, r ^ (p i).val
  have hI (p : Grade I) (hx : p∈V) (i : I) : (S p i).val = p i := Nat.mod_eq_of_lt (hh _ hx i)
  calc
    _ = ∑ i∈ V.image S, g i := by
      rw [Finset.sum_image]
      · apply sum_congr rfl; intro i hi
        simp only [g,hI _ hi,price]
      intro i hi j hj e; exact Finsupp.ext fun t => by rw [← hI _ hi t,← hI _ hj t,e]
    _ ≤ ∑ i, g i := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => prod_nonneg fun j _ => pow_nonneg hq.le _)
    _ = ∏ _ : I, ∑ j : Fin N,r^j.val := (Fintype.prod_sum (fun _ : I => fun j : Fin N => r^j.val)).symm
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (fun i _ => by
      rw [Fin.sum_univ_eq_sum_range]; apply (summable_geometric_of_lt_one hq.le hp).sum_le_tsum _ (fun _ _ => by positivity))

lemma usual (η r : ℝ) (he : 0 < r) (hE : r<η)
    {C : ℝ} (P : X → Wave I) (H : ∀ z∈ boxes η, ∀ V : Finset X, (∑ i∈V,‖eval z (P i)‖) ≤ C) :
    Summable fun x : Grade I × X => ‖coeff x.1 (P x.2)‖ * price (fun _ => r) x.1 := by
  have hs q := nuclear P H (he.trans hE) q
  have hp (q : Grade I) : 0 ≤ price (fun _ => r) q := (price_pos _ q (fun _ _ => he)).le
  let f (q : Grade I) (i : X) := ‖coeff q (P i)‖ * price (fun _ => r) q
  have hb q : Summable (f q) := (hs q).2.1.mul_right _
  refine (summable_prod_of_nonneg ?_).mpr ⟨hb,?_⟩
  · intro q; exact mul_nonneg (norm_nonneg _) (hp _)
  refine ((listings (I:=I) (r:=r/η) (div_pos he (he.trans hE)) ((div_lt_one (he.trans hE)).mpr hE)).mul_right C).of_nonneg_of_le
    (fun i => tsum_nonneg (fun j => mul_nonneg (norm_nonneg _) (hp _))) ?_
  intro q
  change (∑' y, ‖coeff q (P y)‖ * price (fun _ => r) q) ≤ _
  rw [tsum_mul_right]
  refine (mul_le_mul_of_nonneg_right (hs _).2.2 (hp _)).trans_eq ?_
  simp only [price,div_eq_mul_inv,mul_pow,inv_pow,prod_mul_distrib,prod_inv_distrib]; ring

lemma normal {η r C : ℝ} (he : 0 < r) (hE : r<η)
    (P : ℕ → Wave I) (H : ∀ z∈ boxes η, ∀ V : Finset ℕ, (∑ i∈V,‖eval z (P i)‖) ≤ C) :
    TendstoUniformlyOn (fun N z => ∑ j ∈ range N, eval z (P j))
      (fun z => ∑' j, eval z (P j)) atTop (boxes r) := by
  let f (q : Grade I × ℕ) := ‖coeff q.1 (P q.2)‖ * price (fun _ => r) q.1
  have ht : Summable f := usual η r he hE P H
  have hs := ht.prod_symm
  apply tendstoUniformlyOn_tsum_nat hs.prod
  intro n z hz
  have hb : ∀ i : I,‖z i‖ ≤ r := hz
  refine le_trans ?_ ((hs.prod_factor n).sum_le_tsum ((P n).support) (fun i _ =>
    mul_nonneg (norm_nonneg _) ((price_pos _ i (fun _ _ => he))).le))
  rw [MvPolynomial.eval_eq]; apply le_trans (norm_sum_le ..); apply Finset.sum_le_sum
  intro i _
  rw [norm_mul,norm_prod]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [norm_pow]
  change (i.prod (fun x k => ‖z x‖^k)) ≤ _; rw [Finsupp.prod_fintype _ _ (fun x => pow_zero _)]
  exact prod_le_prod (fun _ _ => by positivity) (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hb j) _)

lemma converge {C η : ℝ} (P : Wave I) (x : Grade I) (hp : ∀ z∈ boxes η, ‖eval z P‖ ≤ C) (he : 0 < η) :
    ‖coeff x P‖ ≤ (price (fun _ => η) x)⁻¹*C := by
  obtain ⟨N,hN,hq,hX⟩ := span P.support x
  let r (_ : I) := η
  have h : 0 < price r x := price_pos r x (fun i hi => he)
  rw [display r x P hN h hq hX,← total r x h hN, sum_mul]
  apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro j _
  rw [norm_mul]; apply mul_le_mul_of_nonneg_left (hp _ _) (norm_nonneg _)
  intro i; exact (circle_val r N j (fun i => he.le) hN _).le

lemma settle {r : ℝ} (A B : ℕ → Wave I) (F : (I→ℂ)→ℂ) (q : Grade I) (hp : 0 < r)
    (h : TendstoUniformlyOn (fun n z => eval z (A n)) F atTop (boxes r))
    (hk : TendstoUniformlyOn (fun n z => eval z (B n)) F atTop (boxes r)) :
    Tendsto (fun i => coeff q (A i)-coeff q (B i)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr; intro ε he
  let s := price (fun _ => r) q
  have hs : 0 < s := price_pos _ _ (fun i _ => hp)
  let y := ε*s / 4
  have hy : 0 < y := div_pos (mul_pos he hs) (by norm_num)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h y hy, Metric.tendstoUniformlyOn_iff.mp hk y hy] with i hi hn
  rw [dist_zero_right,← MvPolynomial.coeff_sub]
  refine (converge (A i-B i) q (C:=y+y) ?_ hp).trans_lt ?_
  · intro z hz; rw [map_sub,← dist_eq_norm]
    exact (dist_triangle _ (F z) _).trans (add_le_add (by rw [dist_comm]; exact (hi z hz).le) (hn z hz).le)
  change s⁻¹*_ < _; rw [inv_mul_lt_iff₀ hs]; unfold y; linarith [mul_pos hs he]
end YM.Multi.Desk
