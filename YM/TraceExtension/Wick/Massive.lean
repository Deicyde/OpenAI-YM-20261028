import YM.TraceExtension.Wick.Gain

/-! Expansion of elementary differential kernels along Euclidean time.
An Euler equation verified right on the convergent Laplace integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Set Filter Function Asymptotics MeasureTheory
open scoped Topology BigOperators Classical

def freq (m t : ℝ) := Real.sqrt (m^2+t^2)
lemma freq_pos (m : ℝ) {t : ℝ} (hp : 0<t) : 0 < freq m t := by unfold freq; positivity
lemma freq_ge (m : ℝ) (t : ℝ) : t ≤ freq m t := by unfold freq; exact Real.le_sqrt_of_sq_le (by linarith [sq_nonneg m])
lemma freq_eq (m t : ℝ) : freq m t ^2 = m^2+t^2 := Real.sq_sqrt (by positivity)
lemma freq_deriv (m : ℝ) {t : ℝ} (hp : 0<t) : HasDerivAt (freq m) (t/freq m t) t := by
    convert! (((Real.hasDerivAt_sqrt (by positivity : m^2+t^2 ≠ 0))).comp t (((hasDerivAt_id' t).pow 2).const_add (m^2))) using 1
    dsimp [freq]; ring

/-- radius and mass moments -/
def stream (m : ℝ) (j k : ℕ) (s t : ℝ) := t^(j+2) / freq m t * freq m t ^ k * Real.exp (-s*freq m t)
def moment (m : ℝ) (j k : ℕ) (s : ℝ) := ∫ t : ℝ in Ioi 0, stream m j k s t
lemma stream_nonneg (m j k s t) (ht : 0<t) : 0 ≤ stream m j k s t := by
    unfold stream; have := freq_pos m ht; positivity
@[fun_prop] lemma measurable_stream (m j k s) : Measurable (stream m j k s) := by unfold stream freq; fun_prop
lemma stream_base (m j s t) (ht : 0<t) (hs : 0<s) : stream m j 0 s t ≤ t^(j+1)*Real.exp (-s*t) := by
    unfold stream; rw [pow_zero,mul_one,pow_succ t]
    exact mul_le_mul ((div_le_iff₀ (freq_pos _ ht)).2 (mul_le_mul_of_nonneg_left (freq_ge ..) (by positivity)))
       (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (freq_ge ..) (neg_nonpos.mpr hs.le))) (by positivity) (by positivity)
lemma stream_step (m s t) (j k) : stream m j (k+2) s t=m^2 * stream m j k s t+stream m (j+2) k s t := by unfold stream; rw [pow_add (freq m t),freq_eq]; ring
lemma stream_first (m j s t) (ht : 0<t) : stream m j 1 s t = t^(j+2)*Real.exp (-s*freq m t) := by unfold stream; rw [pow_one,div_mul_cancel₀ _ (freq_pos m ht).ne']
lemma mass_exp {s : ℝ} (hs : 0<s) (k : ℕ) : (∫ x : ℝ in Ioi 0, x^k * Real.exp (-s*x)) = s⁻¹ ^ (k+1)*Real.Gamma ((k+1:ℕ):ℝ) := by
    have he := Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0:ℝ)< ↑(k+1:ℕ)) hs
    simp only [← neg_mul, Real.rpow_natCast, one_div, Nat.cast_add, Nat.cast_one,add_sub_cancel_right] at *
    rw [show s⁻¹ ^(k+1)= s⁻¹ ^ ((k:ℝ)+1) by rw [show (k:ℝ)+1= ↑(k+1:ℕ) by simp, Real.rpow_natCast] ]; simpa only [Real.rpow_natCast] using he
lemma mass_int {s : ℝ} (hs : 0<s) (k : ℕ) : IntegrableOn (fun x:ℝ=>x^k*Real.exp (-s*x)) (Ioi 0) volume := by
    by_contra h; have he := integral_undef h; rw [mass_exp hs] at he; exact (mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))).ne' he
lemma stream_int (m j k s) (h : 0<s) : IntegrableOn (stream m j k s) (Ioi 0) volume := by
    induction k using Nat.strong_induction_on generalizing j with
    | h k ih=>
      match k with
      | 0 =>
        refine (mass_int h (j+1)).mono' (measurable_stream ..|>.aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; rw [Real.norm_of_nonneg (stream_nonneg _ _ _ _ _ hx)]; exact stream_base _ _ _ _ hx h
      | 1 =>
        refine (mass_int h (j+2)).mono' (measurable_stream ..|>.aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; have ht : 0<x:=hx
        rw [Real.norm_of_nonneg (stream_nonneg _ _ _ _ _ ht),stream_first _ _ _ _ ht]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (freq_ge ..) (by linarith))) (by positivity)
      | k+2 =>
        apply (((ih k (by omega) j).const_mul (m^2)).add (ih k (by omega) (j+2))).congr; apply Eventually.of_forall fun i=>?_
        exact (stream_step ..).symm
lemma moment_step (m j k s) (ht : 0<s) : moment m j (k+2) s=m^2*moment m j k s+moment m (j+2) k s := by
    unfold moment; simp_rw [stream_step]; rw [integral_add ((stream_int _ _ _ _ ht).const_mul _) (stream_int _ _ _ _ ht), integral_const_mul]
lemma moment_d (m j k s) (hs : 0<s) : HasDerivAt (moment m j k) (-moment m j (k+1) s) s := by
    let f z := stream m j k z; let g z := fun t=> -stream m j (k+1) z t
    have hb x s : HasDerivAt (fun z=> f z x) (g s x) s := by
        convert! ((((hasDerivAt_id' s).neg.mul_const (freq m x)).exp).const_mul (x^(j+2) / freq m x * freq m x ^ k)) using 1
        unfold g stream; rw [Pi.neg_apply]; ring
    have he := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=f) (F':=g) (μ:=volume.restrict (Ioi 0))
       (lt_mem_nhds (half_lt_self hs)) (Eventually.of_forall fun i=> (measurable_stream m j k i).aestronglyMeasurable)
       (stream_int _ _ _ _ hs) ((measurable_stream m j (k+1) s).aestronglyMeasurable.neg) (bound:=stream m j (k+1) (s/2))
    have hp : HasDerivAt (moment m j k) (∫ i:ℝ in Ioi 0,g s i) s := by
      refine (he ?_ (stream_int _ _ _ _ (half_pos hs)) (ae_of_all _ fun x t ht=> hb ..)).2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht u hu; have hx := freq_pos m (show 0<t from ht)
      unfold g; rw [norm_neg,Real.norm_of_nonneg (stream_nonneg _ _ _ _ _ ht)]; unfold stream; apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hu)) hx.le
      have hp : 0<t:=ht; positivity
    simpa [g,moment,integral_neg] using hp

lemma euler (m j s) (hs : 0<s) : s*moment m (j+2) 0 s=(j+3:ℝ)* moment m j 1 s := by
    let f (t:ℝ):= t^(j+3)*Real.exp (-s*freq m t)
    let g (t:ℝ):= (j+3:ℝ)*stream m j 1 s t-s*stream m (j+2) 0 s t
    suffices ht : (∫ t in Ioi 0,g t)=0 by
        unfold g at ht; rw [integral_sub ((stream_int _ _ _ _ hs).const_mul _) ((stream_int _ _ _ _ hs).const_mul _),integral_const_mul,integral_const_mul] at ht; exact (sub_eq_zero.mp ht).symm
    have hd t (ht : 0<t) : HasDerivAt f (g t) t := by
       unfold g; rw [stream_first _ _ _ _ ht]
       convert! (((hasDerivAt_id' t).pow (j+3)).mul (((freq_deriv m ht).const_mul (-s)).exp)) using 1
       unfold stream; push_cast; simp only [Pi.pow_apply]; ring
    have he : Tendsto f atTop (𝓝 0) := by
       have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (j+3)).comp (Tendsto.const_mul_atTop hs tendsto_id)
       apply squeeze_zero' (g:=fun x => (s^(j+3))⁻¹ *((s*x)^(j+3)*Real.exp (-(s*x))))
       · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; unfold f; positivity
       · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; unfold f; calc
           _ ≤ x^(j+3)*Real.exp (-(s*x)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [neg_mul]; gcongr; exact freq_ge ..)) (by positivity)
           _ = _ := by rw [mul_pow]; field_simp
       simpa only [mul_zero,comp_apply,id] using ht.const_mul ((s^(j+3))⁻¹)
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (show ContinuousWithinAt f (Ici 0) 0 from (show Continuous f by unfold f freq; fun_prop).continuousWithinAt) hd
       (((stream_int m j 1 s hs).const_mul (j+3:ℝ)).sub ((stream_int m (j+2) 0 s hs).const_mul s)) he
    simpa [f] using h
lemma differentiated (m j) : integrates (fun s => -(m^2)*s^(j+3)*moment m j 0 s) (fun s => s^(j+3)*moment m j 1 s) := by
    intro s hs
    have he := (((hasDerivAt_id' s).pow (j+3)).mul (moment_d m j 1 s hs))
    convert! he using 1; rw [moment_step m j 0 s hs]; push_cast
    have h := euler m j s hs; simp only [Pi.pow_apply]; linear_combination (s^(j+2))*h
lemma first_order (m j) : AtOrder (moment m j 0) (- ((j+2:ℕ):ℤ)) := by
    apply cost_order; apply isBigO_iff.mpr; let A := Real.Gamma (↑(j+1+1:ℕ)); refine ⟨A,?_⟩; filter_upwards [mostly] with x hx
    unfold moment; rw [Real.norm_of_nonneg (show 0 ≤ ∫ t:ℝ in Ioi 0, stream m j 0 x t from integral_nonneg_of_ae (Eventually.mono (ae_restrict_mem measurableSet_Ioi) fun t ht=> stream_nonneg _ _ _ _ _ ht))]
    apply (integral_mono_ae (stream_int _ _ _ _ hx.1) (mass_int hx.1 (j+1)) (Eventually.mono (ae_restrict_mem measurableSet_Ioi) (fun i hi=> stream_base _ _ _ _ hi hx.1))).trans_eq
    rw [mass_exp hx.1, tile, fill_at hx.1,zpow_neg,zpow_natCast,Real.norm_of_nonneg (by have he:=hx.1; positivity),inv_pow,mul_comm]
lemma derived {m j} {k : ℤ} (hk : -((j+2:ℕ):ℤ) ≤ k) (h : AtOrder (moment m j 0) k) : AtOrder (moment m j 1) (k+1) := by
    let t : ℤ:= ↑(j+3:ℕ)
    have hp : AtOrder (fun s => -(m^2)*s^(j+3)*moment m j 0 s) (t+k) := by
        apply ((h.shift t).scale (-(m^2))).upon; filter_upwards [mostly] with s hs; simp only [Pi.smul_apply,Pi.mul_apply, smul_eq_mul,tile,fill_at hs.1,t,zpow_natCast]; ring
    have hb := primitives _ _ (show t+k ≠ -1 by unfold t; omega) (differentiated m j) hp
    rw [show k+1=-t+(t+k+1) by omega]; apply (hb.shift (-t)).upon
    filter_upwards [mostly] with s hs; have hv:=hs.1; simp only [tile,zpow_neg, fill_at hs.1,t,zpow_natCast, Pi.mul_apply]; field_simp
lemma basic_expands (m j) : Expands (moment m j 0) := by
    let b : ℤ:= -↑(j+2:ℕ)
    have he (i : ℕ) : AtOrder (moment m j 0) (b+i) := by
        induction i with
        | zero=> simpa only [Nat.cast_zero,add_zero,b] using first_order m j
        | succ i ih=>
           let k : ℤ:= b+i+1
           have hp : AtOrder (fun s=> - moment m j 1 s) k := by
              have he:= derived (show b ≤ b+i by omega) ih
              exact (he.scale (-1)).upon (by filter_upwards with s; simp)
           have hv : integrates (fun s=> - moment m j 1 s) (moment m j 0) := moment_d m j 0
           suffices he : AtOrder (moment m j 0) k by convert he using 1; dsimp only [k]; omega
           by_cases h:k=-1
           · rw [h] at hp ⊢; exact primitives _ _ (show (-2:ℤ) ≠ -1 by decide) hv (allows (by omega : (-2:ℤ)≤ -1) hp)
           exact allows (by omega) (primitives _ _ h hv hp)
    intro i; exact allows (show i ≤ b+(i-b).toNat by omega) (he _)
lemma moment_expands (m j k) : Expands (moment m j k) := by
    induction k using Nat.strong_induction_on generalizing j with
    | h k ih=>
      match k with
      | 0=> exact basic_expands m j
      | 1=>
          intro i; let b : ℤ:= max (-↑(j+2:ℕ)) i
          exact allows (show i ≤ b+1 from (le_max_right ..).trans (le_add_of_nonneg_right (by norm_num))) (derived (le_max_left ..) (basic_expands m j b))
      | k+2 =>
          intro i; apply ((((ih k (by omega) j).scale (m^2)).plus (ih k (by omega) (j+2))) i).upon; filter_upwards [mostly] with x hx; exact (moment_step _ _ _ _ hx.1).symm
end YM.TraceExtension.Wick
