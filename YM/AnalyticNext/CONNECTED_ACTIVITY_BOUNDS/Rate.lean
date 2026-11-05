import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.FrameCosts
import YM.Push.ABSOLUTE_SUMS.Delay
import YM.Push.ABSOLUTE_SUMS.Mixed


/-!
# Small-stencil cost accounting (saves of one more threshold)

Address geometry for these uses is post-L. `allowance n p` means the
$n$-cost in powers of the actual *fine cut* threshold squared where
squared is priced as n=2. Constants may be paid by another fixed power
of radius. The window gate uses true coarse hat x determining that
radius (can apply again at projected data with different hat). $O$ at
fixed L, not pre-L and not all orders simultaneously through schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Rates
open Filter Lattice RG Wilson Pressure Pressure.Stores Precision Tree
open Next.Fluctuations Push.SectorMeasure Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable (G : Gauge) (D : Patch) -- patch size already fixed (post L)

def pieces (x : ℝ) (p : ℕ) := (radiusB x:ℝ)^p

def allowance (x : ℝ) (n p : ℕ) := pieces x p * (fiery G x D.L)^n

lemma allowance_nn (x : ℝ) (n p : ℕ) : 0 ≤ allowance G D x n p :=
    mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (temp_nonneg _) _)

lemma exchange (x : ℝ) (n p m q : ℕ) : allowance G D x n p * allowance G D x m q =
    allowance G D x (n+m) (p+q) := by unfold allowance pieces; ring

lemma widen (n : ℕ) {p q : ℕ} (hp : p≤q) : ∀ᶠ x : ℝ in atTop, allowance G D x n p ≤ allowance G D x n q := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx
  have hh : 0 ≤ fiery G x D.L := temp_nonneg _
  unfold allowance pieces; gcongr; exact_mod_cast hx

lemma slow : Tendsto (fun p : ℝ => allowance G D p (n:=1) 0) atTop (𝓝 0) := by
  have hs : Tendsto temp atTop (𝓝 0) := by simpa using Work.E09.radiusB_temp 0
  simpa [Function.comp_def,allowance,pieces,fiery] using hs.comp (Work.E09.betaF_growth G D.L)

lemma grow (C : ℝ) {p q : ℕ} (hp : p<q) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, C*allowance G D x n p ≤ allowance G D x n q := by
  have hx : Tendsto (fun x : ℝ => (radiusB x:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
  filter_upwards [hx.eventually (eventually_ge_atTop C),widen G D n hp] with x hx h
  apply le_trans _ h; unfold allowance pieces
  rw [pow_succ]
  apply le_trans (mul_le_mul_of_nonneg_right hx (allowance_nn G D x n p)); exact le_of_eq (by unfold allowance pieces; ring)

lemma closer : ∀ᶠ x : ℝ in atTop, temp x ≤ 2 * fiery G x D.L ∧ fiery G x D.L ≤ 2*temp x := by
  have hl : Tendsto (fun x => fiery G x D.L / temp x) atTop (𝓝 1) := Work.E09.temp_ratio _
  filter_upwards [hl.eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num)),
    hl.eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num)),eventually_gt_atTop (0:ℝ)] with x h1 h2 hx
  have he := Work.E09.temp_pos hx
  exact ⟨by linarith only [(le_div_iff₀ he).mp h2], (div_le_iff₀ he).mp h1⟩

lemma vanishes (p : ℕ) : Tendsto (fun x => allowance G D x 1 p) atTop (𝓝 0) := by
  have ht := Work.E09.radiusB_temp p
  apply squeeze_zero' (Eventually.of_forall fun x => allowance_nn G D x 1 p) ?_
    (g:=fun x => 2*((radiusB x:ℝ)^p*temp x)) (by simpa only [mul_zero] using! ht.const_mul 2)
  filter_upwards [closer G D] with x hx
  unfold allowance pieces; rw [mul_left_comm (2:ℝ),pow_one]
  gcongr; exact hx.2

lemma burn (n p : ℕ) (D' : ℝ) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ x : ℝ in atTop,D'*allowance G D x (n+1) p ≤ ε*allowance G D x n 0 := by
  have hh : Tendsto (fun x => D'*allowance G D x 1 p) atTop (𝓝 0) := by simpa using! (vanishes G D p).const_mul D'
  filter_upwards [hh.eventually (ge_mem_nhds he)] with x hx
  have hu : allowance G D x (n+1) p=allowance G D x 1 p*allowance G D x n 0 := by
    simp only [exchange,Nat.one_add,Nat.add_zero]
  rw [hu,← mul_assoc]; exact mul_le_mul_of_nonneg_right hx (allowance_nn ..)

lemma decay {ε : ℝ} (he : 0<ε) (n p : ℕ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C*pieces x p*Real.exp (-ε*till x) ≤ allowance G D x n 0 := by
  have hh := radius_tail_fiery G D.L (ε/(n+1:ℕ)) (by positivity) p
  have hs : ((max 1 C):ℝ)≥1 := le_max_left ..
  let a x := Real.exp (-(ε/(n+1:ℕ))*till x)
  have hf := hh.const_mul (max 1 C); rw [mul_zero] at hf
  filter_upwards [Delay.shift_pos G D.L, hf.eventually (ge_mem_nhds zero_lt_one),
    (slow G D).eventually (ge_mem_nhds zero_lt_one),Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x h1 hx hy hv
  let t := fiery G x D.L
  have ht : 0<t := Work.E09.temp_pos h1
  have hi : max 1 C * pieces x p * a x ≤ t := by
    have he : max 1 C*((pieces x p * a x)/t) ≤ 1 := hx
    rw [← mul_div_assoc, ← mul_assoc,div_le_one ht] at he; exact he
  have he : 1 ≤ pieces x p := one_le_pow₀ (by exact_mod_cast hv)
  have hu : a x≤t := by calc
    _ ≤ (max 1 C*pieces x p) * a x := le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le hs he)
    _ ≤ _ := hi
  have hj : a x ^ (n+1)= Real.exp (-ε*till x) := by
    unfold a; rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hl : t≤1 := by simpa only [allowance,pieces,pow_zero,one_mul,pow_one,t] using
    (show allowance G D x 1 0 ≤ 1 from hy)
  calc
    _ = (C*pieces x p*a x)*a x ^ n := by rw [← hj,pow_succ']; ring
    _ ≤ t * t^n := by
      have hg : C*pieces x p*a x ≤ t := le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_max_right ..) (zero_le_one.trans he)) (Real.exp_pos _).le) hi
      exact mul_le_mul hg (pow_le_pow_left₀ (Real.exp_pos _).le hu n) (pow_nonneg (Real.exp_pos _).le _) ht.le
    _ ≤ t^n := mul_le_of_le_one_left (pow_nonneg ht.le _) hl
    _ = _ := by unfold allowance pieces; rw [pow_zero,one_mul]

lemma tariff_paid (c : ℕ) : ∀ᶠ x : ℝ in atTop,
    Aff.tariff (c*radiusB x) x ≤ allowance G D x 1 6 := by
  let C := 2*16*(2*(c:ℝ)+1)^5*Fintype.card PlaqAxes
  filter_upwards [closer G D, Work.E01.radiusB_tendsto.eventually_ge_atTop 1,
    grow G D C (by decide : 5<6) 1] with x hx hh hi
  apply le_trans _ hi
  have hb : 1 ≤ (radiusB x:ℝ) := by exact_mod_cast hh
  have hp : 0 ≤ temp x := temp_nonneg _
  have hf : 0 ≤ fiery G x D.L := temp_nonneg _
  unfold C Aff.tariff allowance pieces
  push_cast
  rw [pow_one]
  let t : ℝ := radiusB x
  calc
    _ ≤ 16*((2*c+1)*t)^5 * (Fintype.card PlaqAxes) * (2*fiery G x D.L) := by
      have ht := hx.1; gcongr; unfold t; nlinarith
    _ = _ := by unfold t; ring
end YM.AnalyticNext.ConnectedActivity.Rates
