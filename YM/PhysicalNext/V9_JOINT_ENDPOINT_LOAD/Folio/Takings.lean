import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Fares

/-!
Exponential in B after any fixed polynomial degree and support exponent,
before any inspecting of occurrences (including inspecting their true
reach/coupling). Applies also to a uniformly selected upper budget with
extra population factors *after* supplying their growth estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.SectorChange Wisps Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism
open YM.Push.AbsoluteSums
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {a x : ℝ} {r m k B : ℕ} {G : Gauge} {S : StepData c f} {P : Patch} {v : Charges}

lemma total_packages (hP : S.patch=P) (ht : 0 < B) (ha : 0≤a) (hB : a / (B+1) ≤ v.toll/4) (hw : speed v G P a m k * v.coin x ≤ 1/2) (z : Site c) :
    let r := m*B; let w:=packages v G x (home S) k B m a z
    SumBudget w ((1+(r:ℝ))^k*heads P r * (v.ink G+ 2*wind v k * speed v G P a m k^2)*pack a m * v.coin x) := by
  intro r w
  let h := w ∘ Sum.inl; let f' := w ∘ Sum.inr
  let Y := (1+(r:ℝ))^k * heads P r * pack a m; let W := speed v G P a m k
  let C := Y*wind v k * W^2 * v.coin x
  have hn := v.ink_pos G
  have ht' := v.coin_pos x
  have hM : 0≤heads P r := by unfold heads; positivity
  have hY : 0 ≤ Y := mul_nonneg (by positivity) pack_nn
  have hW : 0 ≤ W := speed_nn
  have hC : 0 ≤ C := by have hr := wind_nn (k:=k) v; unfold C; positivity
  have h₁ : SumBudget h (Y*v.ink G * v.coin x) := by
    let E := (1+(r:ℝ))^k*(v.ink G*v.coin x) * pack a m
    apply budget_finite (fun i => packs_nn ..)
    refine le_trans (b := ∑ i:Bond f,if z∈halo r {home S i} then E else 0) (sum_le_sum fun i _ => ?_) ?_
    · change packages v G x (home S) k B m a z (Sum.inl i) ≤ _; unfold packages
      rw [← spread,spread_first]; unfold premiums; simp only [plan,steps,traveled,Sum.elim_inl, Nat.zero_add,Nat.add_zero,Nat.one_mul,award,Nat.cast_add,Nat.cast_one]
      split; next hz =>
        apply mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ (1+((m*B:ℕ):ℝ))^k * _)
        exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast (Corona.tile (home S i) m B ht).trans (Nat.le_add_right .. : _ ≤ tilePrice m)) ha)
      next hz => exact le_rfl
    rw [← Finset.sum_filter,sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (heads_cost hP z r) (by unfold E; have h:= pack_nn (m:=m) (a:=a); positivity)).trans_eq (by unfold E Y; ring)
  have h₂ (n : ℕ) : (∑ i : Bends (Bond f) (Bond f) n, f' ⟨n,i⟩) ≤ C*(1/2)^n := calc
    _ ≤ _ := package_real hP ht ha hB z n
    _ = C*(W*v.coin x)^n := by unfold C Y W; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw n) hC
  have hf :  RG.SumBudget f' (C*(1-(1/2:ℝ))⁻¹) := by
    apply budget_degrees Sigma.fst (fun i=>packs_nn ..) hC (by norm_num : 0≤(1/2:ℝ)) (by norm_num)
    intro n s h
    let X := Bends (Bond f) (Bond f) n
    let E : X → Σ m,Bends (Bond f) (Bond f) m := fun i => ⟨n,i⟩
    suffices hL : s ⊆ Finset.univ.image E by
      apply (sum_le_sum_of_subset_of_nonneg hL (fun i _ _ => packs_nn ..)).trans
      have he : Injective E := fun i j hi => eq_of_heq (Sigma.mk.inj hi).2
      rw [sum_image he.injOn]; exact h₂ n
    rintro ⟨u,i⟩ hi; obtain rfl := h _ hi; exact mem_image_of_mem E (mem_univ i)
  have he := HasSum.sum (f:=w) h₁.2.1.hasSum hf.2.1.hasSum
  exact ⟨fun i => packs_nn ..,he.summable, he.tsum_eq.trans_le ((add_le_add h₁.2.2 hf.2.2).trans (le_of_eq (by unfold C W Y; ring)))⟩

-- uniform on every step/transition (fixed L and J now).
def prize (v : Charges) := v.delay / 4
lemma prize_pos (v : Charges) : 0<prize v := by unfold prize; have := v.time_pos; positivity
lemma tendsto_bill (s : ℝ) (hs : 0<s) (m k : ℕ) : Tendsto (fun B : ℕ => (1+(m:ℝ)*B)^k * rate (-s) B) atTop (𝓝 0) := by
  let K := (1+(m:ℝ))^k*((s/2)⁻¹^k*k.factorial*Real.exp (s/2))
  have h := show Tendsto (fun B : ℕ => rate (-(s/2)) B) atTop (𝓝 0) by
    simpa only [rate,Function.comp_def,neg_mul] using! Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hs))
  apply squeeze_zero (g:=fun B:ℕ => K*rate (-(s/2)) B) (fun _ => mul_nonneg (pow_nonneg (by positivity) _) (rate_pos ..).le)
  swap; simpa using h.const_mul K
  intro B
  have he := polynomial_cost (half_pos hs) (Nat.cast_nonneg (α:=ℝ) B) k
  have hp : (1+(m:ℝ)*B)^k ≤ (1+(m:ℝ))^k*((1+(B:ℝ))^k) := by
    rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); nlinarith [Nat.cast_nonneg (α:=ℝ) m,Nat.cast_nonneg (α:=ℝ) B]
  apply (mul_le_mul_of_nonneg_right (hp.trans (mul_le_mul_of_nonneg_left he (by positivity))) (rate_pos (-s) B).le).trans_eq
  unfold K; rw [mul_assoc, mul_assoc,show Real.exp (s/2*B)*rate (-s) B=rate (-(s/2)) B by unfold rate; rw [← Real.exp_add]; congr 1; ring]; ring

lemma cash (P : Patch) (m k : ℕ) (h : ℝ) (s : ℝ) (hs : 0<s) : ∀ᶠ B : ℕ in atTop, (1+((m*B:ℕ):ℝ))^k * heads P (m*B) * h ≤ rate s B := by
  let g (B : ℕ) := (1+((2*m:ℕ):ℝ)*B)^(k+4)
  let v : ℝ := ((P.L.val^4*Fintype.card Axis:ℕ):ℝ)
  have he (B) : (1+((m*B:ℕ):ℝ))^k * heads P (m*B)*h ≤ g B * (v*|h|) := by
    have ht : 1+((m*B:ℕ):ℝ)≤1+((2*m:ℕ):ℝ)*B := by push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) (m*B),Nat.cast_mul (α:=ℝ) m B]
    unfold g heads; unfold v
    rw [pow_add]; push_cast; push_cast at ht
    rw [show (m:ℝ)*B+m*B+1=1+2*m*B by ring]
    simp only [←mul_assoc]
    apply (mul_le_mul_of_nonneg_left (le_abs_self h) (by positivity : 0 ≤ (1+(m:ℝ)*B)^k * (1+2*(m:ℝ)*B)^4 * (P.L.val:ℝ)^4 * Fintype.card Axis)).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht _) (by positivity)) (by positivity)) (by positivity)) (by positivity)
  have ht := ((tendsto_bill s hs (2*m) (k+4)).mul_const (v*|h|))
  rw [zero_mul] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one] with B hb
  apply (he B).trans
  unfold rate at *; rw [neg_mul,Real.exp_neg] at hb
  apply le_of_mul_le_mul_left (a:=(Real.exp (s*B))⁻¹) ?_ (by positivity)
  rw [inv_mul_cancel₀ (Real.exp_pos _).ne']; unfold g; linarith

structure Enough (v : Charges) (P : Patch) (G : Gauge) (a : ℝ) (k m : ℕ) (x : ℝ) : Prop where
  test {c f : Side} (S : StepData c f) : S.patch=P → Ac.Hit (spread S (m*radiusB x)) (radiusB x) (premiums v G x (home S) k (m*radiusB x)) a (rate (-prize v) (radiusB x))

theorem takings (v : Charges) (P : Patch) (G : Gauge) (a : ℝ) (k m : ℕ) (ha : 0≤a) : ∀ᶠ x : ℝ in atTop, Enough v P G a k m x := by
  let W := speed v G P a m k
  let s := v.toll/4
  have hs : 0<s := by have := v.toll_pos; unfold s; positivity
  have hh : ∀ᶠ x in atTop, a/(radiusB x+1:ℝ) ≤ s := by
    have he : Tendsto (fun x => (radiusB x:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
    filter_upwards [he.eventually_ge_atTop (a/s)] with x hx
    exact (div_le_iff₀ (by positivity)).mpr (((div_le_iff₀ hs).mp hx).trans_eq (mul_comm ..))
  have hW : Tendsto (fun x => W*v.coin x) atTop (𝓝 0) := by simpa only [mul_zero] using!
      (SectorTools.PhysicalGaussianInsertion.Physical.error_limit _ (half_pos v.time_pos)).const_mul W
  let C := (v.ink G+2*wind v k*W^2)*pack a m
  filter_upwards [hh,hW.eventually_le_const (by norm_num : (0:ℝ)<1/2), Work.E01.radiusB_tendsto.eventually_gt_atTop 0,
    Work.E01.radiusB_tendsto.eventually (cash P m k C _ (prize_pos v))] with x hs hv hx hC
  constructor; intro c f S hS j
  apply budget_loosen (total_packages hS hx ha hs hv j)
  apply le_trans (b := ((1+((m*radiusB x:ℕ):ℝ))^k*heads P (m*radiusB x)*C)*v.coin x) (le_of_eq (by unfold C W; ring))
  exact (mul_le_mul_of_nonneg_right hC (v.coin_pos x).le).trans_eq (by unfold Charges.coin rate prize; rw [← Real.exp_add]; congr 1; ring)
end YM.PhysicalNext.JointLoad.Folio
