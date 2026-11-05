import YM.Next.ROTATIONS.Frost
/-!
# Remainder outside the low spectral box. Costs faster than any paid n-exponential,
without a trace at zero. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace
private def val (f : Form) (k : ℕ) := SchwartzMap.seminorm ℝ k 0 f
private lemma ordinary (f : Form) (x K q : ℝ) (n : ℕ) (h : -K ≤ x) : ‖large (fuel x n) f q‖ ≤ val f 0*fuel K n := by
  rw [large_at,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (fuel_pos x n)).le,← fuel_neg,mul_comm (fuel ..)]
  exact mul_le_mul (f.norm_le_seminorm ℝ _) (fuel_le (by linarith) _) (fuel_pos ..).le (apply_nonneg _ _)
private lemma extraordinary (f : Form) (x K q : ℝ) (k n : ℕ) (h : -K ≤ x) (hp : fuel (1+x) n < |q|) :
    ‖large (fuel x n) f q‖ ≤ val f k * fuel (K-k) n := by
  rw [large_at,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (fuel_pos x n)).le,← fuel_neg]
  let r := q/fuel x n
  have hr : fuel 1 n ≤ ‖r‖ := by
    unfold r; rw [norm_div,Real.norm_of_nonneg (fuel_pos ..).le, le_div_iff₀ (fuel_pos ..),fuel_mul]; exact hp.le
  have ht : fuel k n * ‖f r‖ ≤ val f k := by
    rw [show fuel k n=fuel 1 n^k by rw [fuel_rate,one_mul]]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (fuel_pos ..).le hr k) (norm_nonneg _)).trans (f.norm_pow_mul_le_seminorm ℝ k r)
  have hl : ‖f r‖ ≤ val f k * fuel (-(k:ℝ)) n := by rw [fuel_neg,← div_eq_mul_inv, le_div_iff₀ (fuel_pos ..),mul_comm]; exact ht
  exact (mul_le_mul (fuel_le (by linarith : -x≤K) n) hl (norm_nonneg _) (fuel_pos ..).le).trans_eq (by rw [mul_left_comm,fuel_mul,← sub_eq_add_neg])

lemma worn (w : Axis→ℝ) (d : Axis) (f : Panels) (K : ℝ) (hw : ∀ i, -K ≤ w i) :
    ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) p, ‖reading d (tracks w d n f) p‖ ≤ M*fuel (K*3) n := by
  refine ⟨∏ i∈other d,val (f i) 0,Finset.prod_nonneg (fun i _ => apply_nonneg _ _),fun n p => ?_⟩
  rw [track_reading, show fuel (K*3) n=∏ _i∈other d,fuel K n from by simp [Axis, fuel_rate,other], ← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ordinary _ _ _ _ _ (hw i))

lemma rag (w : Axis→ℝ) (d : Axis) (f : Panels) (K : ℝ) (hw : ∀ i, -K ≤ w i) (y : ℝ) :
    ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) p, p ∉ scatter w d n → ‖reading d (tracks w d n f) p‖ ≤ M*fuel y n := by
  obtain ⟨k,hk⟩ := exists_nat_gt (K*3-y)
  let W j := val (f j) k * ∏ i∈((other d).erase j), val (f i) 0
  have hW j : 0 ≤ W j := mul_nonneg (apply_nonneg _ _) (Finset.prod_nonneg (fun i _ => apply_nonneg _ _))
  refine ⟨∑ j : Axis,W j,Finset.sum_nonneg fun i _ => hW _,fun n p hp => ?_⟩
  unfold scatter at hp; simp only [Set.mem_setOf_eq,not_forall,not_le] at hp
  obtain ⟨j,hj,hp⟩ := hp
  refine le_trans (b:=W j*fuel ((K-k)+K*2) n) ?_ (mul_le_mul (Finset.single_le_sum (fun i _ => hW i) (Finset.mem_univ _)) (fuel_le (by linarith) n) (fuel_pos ..).le (Finset.sum_nonneg fun i _ => hW _))
  unfold W; rw [track_reading, ← Finset.mul_prod_erase _ _ hj,← fuel_mul,mul_mul_mul_comm (val _ k), show fuel (K*2) n=∏ _i∈((other d).erase j),fuel K n by
    rw [Finset.prod_const,Finset.card_erase_of_mem hj, show (other d).card=3 from by simp [Axis,other],fuel_rate]; norm_num,← Finset.prod_mul_distrib]
  refine mul_le_mul (extraordinary _ _ _ _ _ _ (hw j) hp) (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ordinary _ _ _ _ _ (hw i)))
    (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (mul_nonneg (apply_nonneg _ _) (fuel_pos ..).le)

private lemma sells (d K M : ℝ) (hd : d<0) (hK : 0<K) : ∀ᶠ n : ℕ in atTop,
    (n:ℝ)*K + M ≤ fuel (-d) n := by
  have he : Tendsto (fun n : ℕ => n * (-d)) atTop atTop := tendsto_natCast_atTop_atTop.atTop_mul_const (neg_pos.mpr hd)
  filter_upwards [(Real.tendsto_exp_div_pow_atTop 1 |>.comp he).eventually (eventually_ge_atTop ((K+1)/(-d))),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop M),eventually_gt_atTop (0:ℕ)] with n hn hn' h
  change (K+1)/(-d) ≤ Real.exp _ / ((n:ℝ)*(-d))^1 at hn; simp only [pow_one] at hn
  have hh : 0 < (n:ℝ) := Nat.cast_pos.mpr h
  rw [le_div_iff₀ (mul_pos hh (neg_pos.mpr hd))] at hn
  rw [show (K+1)/(-d)*(n*(-d)) = n*(K+1) by field_simp [hd.ne]] at hn
  unfold fuel; change M≤(n:ℝ) at hn'; linarith
lemma sale (d y R : ℝ) (hd : d<0) : ∀ᶠ n in atTop, ∀ E : ℝ,1≤E →
    Real.exp (-(E/fuel d n)) ≤ fuel y n*Real.exp (-R*E) := by
  let x := min (-1) y
  have hx : x < 0 := (min_le_left _ _).trans_lt (by norm_num)
  filter_upwards [sells d (-x) R hd (neg_pos.mpr hx)] with n hn E hp
  refine le_trans (b:=fuel x n*Real.exp (-R*E)) ?_ (mul_le_mul_of_nonneg_right (fuel_le (min_le_right ..) _) (Real.exp_pos _).le)
  rw [div_eq_mul_inv,← fuel_neg,
    show fuel x n=Real.exp ((n:ℝ)*x) from rfl,← Real.exp_add,Real.exp_le_exp]
  have hi := mul_le_mul_of_nonneg_left hn (by linarith : 0≤E)
  nlinarith [show (0:ℝ) ≤ (n:ℝ)*(-x) by exact mul_nonneg (Nat.cast_nonneg _) (neg_pos.mpr hx).le]

abbrev cove (w : Axis→ℝ) (d : Axis) (n : ℕ) := {p : E4 | p d≤1} ∩ scatter w d n
lemma cove_m (w : Axis→ℝ) (d : Axis) (n : ℕ) : MeasurableSet (cove w d n) :=
    (measurableSet_le (by fun_prop) measurable_const).inter (scatter_m w d n)

lemma farther (w : Axis→ℝ) (d : Axis) (f : Panels) (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) (K : ℝ) (hw : ∀ i, -K ≤ w i) (hd : w d<0) (R : ℝ) (hR : 0≤R) (y : ℝ) (b : ℂ) (hb : ‖b‖=1) :
    ∃ M : ℝ,0≤M ∧ ∀ᶠ n in atTop, ∀ p : E4, 0≤p d → p∉cove w d n →
    ‖answer d b (tracks w d n f) p‖ ≤ M*fuel y n*Real.exp (-R*p d) := by
  obtain ⟨m,hm,ht⟩ := worn w d f K hw
  obtain ⟨r,hr,hz⟩ := rag w d f K hw y
  let t := ∫ x : ℝ,‖hat (f d) x‖
  have hp : 0≤t := integral_nonneg (fun i => norm_nonneg _)
  refine ⟨max (t*r/Real.exp (-R)) (t*m),le_max_of_le_right (mul_nonneg hp hm),?_⟩
  filter_upwards [sale (w d) (y-K*3) R hd] with n hn p hv hx
  let E := p d; change 0≤E at hv
  have ht' : ‖Lap b (tracks w d n f d) E‖ ≤ t* Real.exp (-(E/fuel (w d) n)) := by
    unfold tracks; rw [update_self]; exact frozen_size b hb _ (f d) (fuel_pos ..) h E hv
  rw [answer,norm_mul]
  by_cases hy : E≤1
  · have hf : p ∉ scatter w d n := fun hu => hx ⟨hy,hu⟩
    have hm1 : t* Real.exp (-(E/fuel (w d) n)) ≤ t := mul_le_of_le_one_right hp (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hv (fuel_pos ..).le)))
    refine le_trans (mul_le_mul (ht'.trans hm1) (hz n p hf) (norm_nonneg _) hp) ?_
    have hu : Real.exp (-R) ≤ Real.exp (-R*E) := Real.exp_le_exp.mpr (by nlinarith)
    refine le_trans (b:= t*r/Real.exp (-R)*fuel y n*Real.exp (-R)) (le_of_eq (by field_simp)) ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left ..) (fuel_pos ..).le) hu (Real.exp_pos _).le
      (mul_nonneg (le_max_of_le_right (mul_nonneg hp hm)) (fuel_pos ..).le)
  apply le_trans (mul_le_mul (ht'.trans (mul_le_mul_of_nonneg_left (hn E (le_of_not_ge hy)) hp)) (ht _ _) (norm_nonneg _) (mul_nonneg hp (mul_nonneg (fuel_pos ..).le (Real.exp_pos _).le)))
  have he : fuel y n=fuel (y-K*3) n*fuel (K*3) n := by rw [fuel_mul,sub_add_cancel]
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (fuel_pos y n).le) (Real.exp_pos _).le)
  change _ ≤ t*m*fuel y n*_ ; rw [he]; apply le_of_eq; unfold E; ring

variable {G : Gauge} {L : Register G} {S : Table L}
open scoped Classical in
theorem ice (w : Axis→ℝ) (d : Axis) (V : Chamber S d) (H : S.Hierarchy) (B A : Weight L) (f : Panels)
    (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) (K : ℝ) (hw : ∀ i, -K ≤ w i) (hd : w d<0) (b : ℂ) (hb : ‖b‖=1)
    (y : ℝ) : Budget y (fun n => cross V B A ((cove w d n )ᶜ.indicator (answer d b (tracks w d n f)))) := by
  obtain ⟨u,hU,hV⟩ := ((descends d B).and (descends d A)).exists
  obtain ⟨a,ha⟩ := exists_ne d
  let t : ℝ := ↑(u+u:ℝ≥0)
  obtain ⟨M,hM,hX⟩ := farther w d f h K hw hd t (by exact NNReal.coe_nonneg _) y b hb
  unfold cross; refine Budget.times (budget_sum _ _ _ (fun j _ => Budget.times ?_ _)) _
  let p := mom d a 0 t
  let μ := ν V (combo B A j)
  apply ((((budget_fuel y).times M).prod (constant_budget (∫ x,p x ∂μ))).rise (le_of_eq (by ring))).priced
  filter_upwards [hX] with n hn
  change _ ≤ M*fuel y n * ∫ x, p x ∂μ
  rw [← integral_const_mul]; refine norm_integral_le_of_norm_le ((placed_moment V H _ a ha 0 u (meets_air _ _ _ hU hV j)).const_mul _) ?_
  filter_upwards [before V (combo B A j)] with q hq
  by_cases he : q∈cove w d n
  · rw [indicator_of_notMem (show q∉(cove w d n)ᶜ from not_not_intro he),norm_zero]; exact mul_nonneg (mul_nonneg hM (fuel_pos ..).le) (mom_nn ..)
  rw [indicator_of_mem (show q∈(cove w d n)ᶜ from he)]; simp only [p,mom,Nat.mul_zero,pow_zero,mul_one]
  exact hn q hq he
end YM.Outer
