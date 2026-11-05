import YM.AnalyticBridge.VERIFIED_RESET_STEP.Geometry

/-! Exact square completion and clover analogue on the covered row pairs.
All regroupings charged; uses symbol0 of the actual PathData. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG UVNext.PricedKernels Next.Scheduling Work.F03 WilsonStartup Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint}
namespace Low
variable {R : PathData G} {c : Clip} {σ C Λ : ℝ}

lemma label_sum {f : Low → ℝ} (hf : Summable f) : (∑' d, f d) = ∑ a, (f (a,.inl ()) + ∑' j, f (a,.inr j)) := by
  rw [hf.tsum_prod,tsum_fintype]; exact Finset.sum_congr rfl fun a _ => by
    rw [Summable.tsum_sum (f:=fun i : Duo => f (a,i)) Summable.of_finite ((hf.prod_factor a).comp_injective Sum.inr_injective), tsum_fintype]; simp

lemma paired (f : ℕ → G.Color) (h : Summable (fun i => ‖f i‖)) :
    Summable (fun j : ℕ × ℕ => inner ℝ (f j.1) (f j.2) / 2) ∧
      ∑' j : ℕ × ℕ, inner ℝ (f j.1) (f j.2) / 2 = ‖∑' i, f i‖^2 / 2 := by
  have ht : SumBudget (fun i => ‖f i‖) (∑' i, ‖f i‖) := ⟨fun _ => norm_nonneg _,h,le_rfl⟩
  have hs : Summable (fun j : ℕ × ℕ => inner ℝ (f j.1) (f j.2)) := Summable.of_norm_bounded (budget_prod ht ht).2.1 fun j => abs_real_inner_le_norm ..
  have he (x : G.Color) : ∑' j, inner ℝ x (f j) = inner ℝ x (∑' i, f i) := ((innerSL ℝ x).map_tsum h.of_norm).symm
  refine ⟨hs.div_const 2, ?_⟩
  rw [tsum_div_const,hs.tsum_prod,← real_inner_self_eq_norm_sq]
  simp_rw [he, fun i => real_inner_comm (∑' i, f i) (f i),he]
lemma mark_sum (h : R.Bounds c σ C Λ) : Summable fun d : Low => |d.mark R c| :=
  (Geo.lower_budget G R h).2.1.of_nonneg_of_le (fun d => abs_nonneg _) (fun d =>
    le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (by positivity))))

lemma live_sum (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ) (o : Site n) (U : Config G n) : Summable (fun d => live R c d p o U) := by
  let f (d : Low) := |d.mark R c| * Real.exp ((d.length R:ℝ)/c.relaxation)
  have hs : Summable f := (Geo.lower_budget G R h).2.1.of_nonneg_of_le (fun i => by unfold f; positivity) (fun d => by
    unfold f; gcongr
    exact (div_le_iff₀ c.radius_pos).mpr (by nlinarith [hw.2.1,Nat.cast_nonneg (α:=ℝ) (d.length R)]))
  exact Summable.of_norm_bounded (hs.mul_right (2*p.threshold)) fun d => (d.shapeBound R c o U).trans_eq (by unfold f; ring)
lemma plain_sum (h : R.Bounds c σ C Λ) (o : Site n) (U : Config G n) : Summable fun d => mark R c d * plain R d o U := by
  apply Summable.of_norm_bounded ((mark_sum h).mul_right 2); intro d
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]; gcongr
  cases e : d.2
  · change |Sum.elim _ _ d.2| ≤ (2:ℝ); rw [e]; exact (abs_of_nonneg (G.price_range _).1).trans_le (G.price_range _).2
  have hh (s : Slot) := s.eval_norm (expandAt o U)
  unfold plain; rw [e,Sum.elim_inr, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_le_iff₀ (by norm_num)).mpr ((abs_real_inner_le_norm ..).trans (mul_le_mul (hh _) (hh _) (norm_nonneg _) (by norm_num)))
lemma masked_summable {ι : Type*} (X : ι → Support n) (f : ι → Pot G n) (U : Config G n) (t : ℝ) (h : Summable fun i => f i U) :
    Summable fun i => masked t (X i) (f i) U := Summable.of_norm_bounded h.norm fun i => by
  by_cases he : Healthy t (X i) U <;> simp [masked_ne,masked_eq,he]
lemma maskedPlain_sum (h : R.Bounds c σ C Λ) (p : BudgetPoint) (o : Site n) (U : Config G n) : Summable (fun d => maskedPlain R c d o p U) :=
  masked_summable _ _ _ _ (plain_sum h o U)

lemma analogue_sum (h : R.Bounds c σ C Λ) (w : Flux G) : Summable fun d => mark R c d * analogue R d w := by
  let K := ∑ i, ‖w i‖
  have hk i : ‖w i‖ ≤ K := Finset.single_le_sum (fun i _ => norm_nonneg (w i)) (Finset.mem_univ i)
  have he (a b) : |inner ℝ (w a) (w b) / 2| ≤ K*(K/2) := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((abs_real_inner_le_norm ..).trans (mul_le_mul (hk a) (hk b) (norm_nonneg _) ((norm_nonneg _).trans (hk a)))) (by norm_num)
  apply Summable.of_norm_bounded ((mark_sum h).mul_right (K*(K/2))); intro d
  rw [norm_mul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  unfold analogue; cases e : d.2 <;> exact he ..
lemma proxy_sum (h : R.Bounds c σ C Λ) (p : BudgetPoint) (o : Site n) (U : Config G n) : Summable fun d => mark R c d * masked p.threshold {o} (proxy R d o) U := by
  by_cases he : Healthy p.threshold {o} U
  · simp_rw [masked_eq _ _ _ _ he]; exact analogue_sum h _
  simp_rw [masked_ne _ _ _ _ he,mul_zero]; exact summable_zero

lemma rowPair (h : R.Bounds c σ C Λ) (o : Site n) (a : PlaqAxes) (U : Config G n) :
    (∑' (j : ℕ × ℕ), mark R c (a,.inr j) * plain R (a,.inr j) o U) = ‖R.ell U (o,a)‖^2 / 2 := by
  convert (paired _ ((R.ell_dominated h (o,a)).absolute U)).2 using 1
  exact tsum_congr fun j => by simp [PathData.ellTerms, plain,mark,left,right, real_inner_smul_left,real_inner_smul_right]; ring
  rfl
lemma live_total (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ) (o : Site n) (U : Config G n) :
    (∑' d, live R c d p o U) = ∑ a, R.baseTerm c p U (o,a) := by
  rw [label_sum (live_sum h hw o U)]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases he : PathData.kept c p.threshold o U <;>
      simp only [live,he,↓reduceIte,PathData.baseTerm,Sum.elim_inl,Sum.elim_inr,tsum_zero, rowPair h]
lemma plain_total (h : R.Bounds c σ C Λ) (o : Site n) (U : Config G n) :
    (∑' d, mark R c d * plain R d o U) = ∑ a, (c.direct*G.price (faceValue U (o,a)) + ‖R.ell U (o,a)‖^2/2) := by
  rw [label_sum (plain_sum h o U)]; exact Finset.sum_congr rfl fun a _ => congrArg (c.direct*G.price (faceValue U (o,a)) + ·) (rowPair h o a U)

private def symbolRow (R : PathData G) (a : PlaqAxes) (w : Flux G) := ∑ i, R.symbol0 a i • w i
private lemma analogue_pair (h : R.Bounds c σ C Λ) (a : PlaqAxes) (w : Flux G) :
    (∑' (j : ℕ × ℕ), mark R c (a,.inr j) * analogue R (a,.inr j) w) = ‖symbolRow R a w‖^2 / 2 := by
  let c (b : PlaqAxes) i := if (R.row a i).2.plaq=b then (R.row a i).1 else 0
  let f i := (R.row a i).1 • w (R.row a i).2.plaq
  have hf : f = fun i => ∑ b, c b i • w b := funext fun i => by simp [f,c,ite_smul]
  have hs := summable_sum (s:=Finset.univ) (fun b _ => (h.symTerms a b).smul_const (w b))
  have he : symbolRow R a w = ∑' i, f i := by
    rw [hf,Summable.tsum_finsetSum (f:=fun b i => c b i • w b) (fun b _ => (h.symTerms a b).smul_const (w b))]
    simp_rw [symbolRow,PathData.symbol0,← (h.symTerms a _).tsum_smul_const]; rfl
  have hF : Summable f := hf ▸ hs
  rw [he,← (paired _ hF.norm).2]; exact tsum_congr fun j => by simp [f,mark,analogue,left,right,real_inner_smul_left,real_inner_smul_right]; ring

private lemma symbol_pair (a : PlaqAxes) (w : Flux G) : ‖symbolRow R a w‖^2 =
    ∑ b, ∑ i, R.symbol0 a b * R.symbol0 a i * inner ℝ (w b) (w i) := by
  simp only [← real_inner_self_eq_norm_sq, symbolRow,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,mul_assoc]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (w j) (w i)]
private lemma metric_test (h : R.Bounds c σ C Λ) (w : Flux G) :
    (∑ a, (c.direct*‖w a‖^2 + ‖symbolRow R a w‖^2)) = ∑ a, ‖w a‖^2 := by
  simp_rw [symbol_pair, Finset.sum_add_distrib]
  have he b : c.direct*‖w b‖^2 = ∑ i, (if b=i then c.direct else 0)*inner ℝ (w b) (w i) := by simp [ite_mul]
  simp_rw [he]
  rw [Finset.sum_comm (f:=fun a b => ∑ i, R.symbol0 a b * R.symbol0 a i * inner ℝ (w b) (w i)),← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm (f:=fun a i => R.symbol0 a b * R.symbol0 a i * inner ℝ (w b) (w i)),← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul,← add_mul,h.metric _ _]
  simp [ite_mul]
lemma analogue_total (h : R.Bounds c σ C Λ) (w : Flux G) :
    (∑' d, mark R c d * analogue R d w) = (∑ i, ‖w i‖^2) / 2 := by
  rw [label_sum (analogue_sum h w),← metric_test h, Finset.sum_div]; refine Finset.sum_congr rfl fun a _ => ?_
  rw [analogue_pair h]; simp only [mark,analogue,Sum.elim_inl,real_inner_self_eq_norm_sq]; ring
end Low
end YM.AnalyticBridge.VerifiedReset
