import YM.Next.ROTATIONS.Mass
import YM.Next.ROTATIONS.Thaw
/-! # Cross expenses inside the low box. Handle zero atoms explicitly. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {L : Register G} {S : Table L} {d : Axis} (V : Chamber S d)

lemma balanced (B A : Weight L) (f : ℕ→E4→ℂ) (hf : ∀ᶠ n in atTop,fits V B A (f n)) (a b : ℝ)
    (x y : ℕ→E4 → ℝ) (hx : ∀ᶠ n in atTop,Integrable (x n) (ν V B)) (hy : ∀ᶠ n in atTop, Integrable (y n) (ν V A))
    (ha : Budget a (fun n => integral (ν V B) (x n))) (hb : Budget b (fun n => integral (ν V A) (y n)))
    (hp : ∀ᶠ n in atTop, ∀ p : E4, 0≤p d → 0≤x n p ∧ 0≤y n p ∧ ‖f n p‖^2 ≤ x n p*y n p) :
    Budget ((a+b)/2) (fun n => cross V B A (f n)) := by
  let t := (b-a)/2
  apply ((((budget_fuel t).prod ha).rise (le_of_eq (by unfold t; ring))).add ((hb.prod (budget_inv t)).rise (le_of_eq (by unfold t; ring)))).priced
  filter_upwards [hf,hx,hy,hp] with n hn hx hy hp
  simpa only [div_eq_mul_inv] using cross_le V B A (f n) hn (x n) (y n) hx hy hp (fuel t n) (fuel_pos ..)
lemma balanced_mul (B A : Weight L) (f : ℕ→E4→ℂ) (hf : ∀ᶠ n in atTop,fits V B A (f n)) (a b : ℝ)
    (x y : ℕ→E4 → ℝ) (hx : ∀ n,Integrable (x n) (ν V B)) (hy : ∀ n, Integrable (y n) (ν V A))
    (ha : Budget a (fun n => integral (ν V B) (x n))) (hb : Budget b (fun n => integral (ν V A) (y n))) (t M : ℝ) (hM : 0≤ M)
    (hp : ∀ n, ∀ p : E4, 0≤p d → 0≤x n p ∧ 0≤y n p ∧ ‖f n p‖^2 ≤ (M*fuel t n)^2*(x n p*y n p)) :
    Budget (t+(a+b)/2) (fun n => cross V B A (f n)) := by
  let T (f : ℕ→E4→ℝ) := fun n p => (M*fuel t n)*f n p
  have hI (f : ℕ→E4→ℝ) (μ : Measure E4) (a) (h : Budget a (fun n => integral μ (f n))) :
      Budget (t+a) (fun n => integral μ (T f n)) := by unfold T; simp_rw [integral_const_mul]; exact ((budget_fuel t).times M).prod h
  refine (balanced V B A f hf (t+a) (t+b) (T x) (T y) (.of_forall fun n => (hx n).const_mul _) (.of_forall fun n => (hy n).const_mul _) (hI _ _ _ ha) (hI _ _ _ hb)
    (.of_forall fun n p he => ?_)).rise (le_of_eq (by ring))
  obtain ⟨hr,hq,hl⟩ := hp n p he
  unfold T; exact ⟨mul_nonneg (mul_nonneg hM (fuel_pos ..).le) hr,mul_nonneg (mul_nonneg hM (fuel_pos ..).le) hq,hl.trans_eq (by ring)⟩

abbrev jar (w : Axis→ℝ) (d : Axis) (f : Panels) (e : ℂ) (n : ℕ) := (cove w d n).indicator (answer d e (tracks w d n f))
lemma track_size (w : Axis→ℝ) (d : Axis) (f : Panels) (e : ℂ) (he : ‖e‖=1)
    (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) (p : E4), 0≤p d → p∈cove w d n →
    ‖jar w d f e n p‖ ≤ M*fuel 3 n*crop (other d) (homes w n) p*Real.exp (-(p d/fuel (w d) n)) := by
  obtain ⟨M,hM,hH⟩ := scatter_size w d f
  let R := ∫ x, ‖hat (f d) x‖
  refine ⟨M*R,mul_nonneg hM (integral_nonneg (fun x => norm_nonneg _)),fun n p hp hz => ?_⟩
  have hy : ‖Lap e (tracks w d n f d) (p d)‖ ≤ R *Real.exp (-(p d/fuel (w d) n)) := by
    unfold tracks; rw [update_self]; exact frozen_size e he _ (f d) (fuel_pos ..) h _ hp
  rw [jar,indicator_of_mem hz,answer,norm_mul]
  exact (mul_le_mul hy (hH n p hz.2) (norm_nonneg _) (hy.trans' (norm_nonneg _))).trans_eq (by ring)

abbrev due (w : Axis→ℝ) (d : Axis) (a : ℝ) (n : ℕ) := cost d Finset.univ (fuel a n) (homes w n)
lemma due_nn (w d a n) (p : E4) (he : 0≤p d) : 0 ≤ due w d a n p := cost_nn _ _ _ _ p (fuel_pos ..) he (fun i _ => home_lit w n i)

private lemma ice_one (t u : ℝ) (ht : 0≤t) (hu : 0<u) : Real.exp (-(t/u)) ≤ u*(t+u)⁻¹ := by
  rw [Real.exp_neg]; apply le_trans (inv_anti₀ (show 0<t/u+1 from by positivity) (Real.add_one_le_exp (t/u))); apply le_of_eq; field_simp
private lemma ice_two (t u v : ℝ) (ht : 0≤t) (hu : 0<u) (hv : u≤v) : Real.exp (-(t/u)) ≤ 4*(v*(t+v)⁻¹)^2 := by
  have hw : 0<v := hu.trans_le hv
  apply le_trans (Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_left ht hu hv)))
  rw [show -(t/v)=-(t/(2*v))+ -(t/(2*v)) by ring,Real.exp_add,← sq]
  have hx : Real.exp (-(t/(2*v))) ≤ 2*(v*(t+v)⁻¹) := (ice_one _ _ ht (mul_pos (by norm_num) hw)).trans (by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) (by positivity))
  exact (pow_le_pow_left₀ (Real.exp_pos _).le hx 2).trans_eq (by ring)

lemma shear_size (w : Axis→ℝ) (d : Axis) (f : Panels) (e : ℂ) (he : ‖e‖=1)
    (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) (a : ℝ) (hl : a≤w d) : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) (p : E4), 0≤p d →
    ‖jar w d f e n p‖^2 ≤ (M*fuel (3+w d) n)^2 * (due w d a n p * due w d (w d) n p) := by
  obtain ⟨M,hM,hx⟩ := track_size w d f e he h
  refine ⟨M,hM,fun n p hp => ?_⟩
  by_cases hy : p∈cove w d n
  · have hv : due w d (w d) n p ≤ due w d a n p := by
      unfold due cost low; rw [if_pos (show p d≤1 from hy.1),if_pos (show p d≤1 from hy.1)]
      have he := fuel_pos a n; exact mul_le_mul_of_nonneg_right (inv_anti₀ (by linarith) (by linarith [fuel_le hl n]))
        (crop_nonneg _ _ (fun i _ => home_lit w n i) _)
    have hh : ‖jar w d f e n p‖ ≤ M*fuel (3+w d) n * due w d (w d) n p := by
      let P := due w d (w d) n
      refine (hx n p hp hy).trans ((mul_le_mul_of_nonneg_left (ice_one _ _ hp (fuel_pos ..))
        (mul_nonneg (mul_nonneg hM (fuel_pos ..).le) (crop_nonneg _ _ (fun i _ => home_lit w n i) _))).trans_eq ?_)
      unfold due cost low other
      rw [if_pos (show p d≤1 from hy.1),← fuel_mul]; ring
    refine (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans ?_
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by rw [sq]; exact mul_le_mul_of_nonneg_right hv (due_nn _ _ _ _ p hp)) (sq_nonneg _)
  rw [jar,indicator_of_notMem hy,norm_zero,zero_pow (by norm_num : 2≠0)]; exact mul_nonneg (sq_nonneg _) (mul_nonneg (due_nn _ _ _ _ p hp) (due_nn _ _ _ _ p hp))

abbrev cave (d : Axis) (q : ℝ) (n : ℕ) := {p : E4| fuel q n≤p d}
lemma cave_m (d : Axis) (q : ℝ) (n : ℕ) : MeasurableSet (cave d q n) := measurableSet_le measurable_const (by fun_prop)
lemma bead_size (w : Axis→ℝ) (d : Axis) (f : Panels) (e : ℂ) (he : ‖e‖=1)
    (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) (a : ℝ) (z : ℝ) (hw : w d≤z) : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) (p : E4), 0≤p d →
    ‖((cave d a n).indicator (jar w d f e n) p)‖^2 ≤ (M*fuel 3 n)^2 * (due w d a n p * coneWeight d (fuel z n) (homes w n) p) := by
  obtain ⟨M,hM,hH⟩ := track_size w d f e he h
  refine ⟨M*8,mul_nonneg hM (by norm_num),fun n p hp => ?_⟩
  let P := (M*8*fuel 3 n)^2 * (due w d a n p * coneWeight d (fuel z n) (homes w n) p)
  have hP : 0≤P := mul_nonneg (sq_nonneg _) (mul_nonneg (due_nn w d a n p hp) (cone_nn _ _ _ (home_lit w n) p (fuel_pos ..) hp))
  by_cases hx : p∈cave d a n
  · rw [indicator_of_mem hx]
    by_cases hy : p∈cove w d n
    · let t := p d; let v := fuel z n; let Q := crop (other d) (homes w n) p; let R := fuel a n
      have hQ : 0≤ Q := crop_nonneg _ _ (fun i _ => home_lit w n i) p
      change R ≤ t at hx; have hv : 0<v := fuel_pos ..; have hr : 0<R := fuel_pos ..; have ht := hr.trans_le hx
      have he : ‖jar w d f e n p‖ ≤ M*fuel 3 n*Q*(4*(v*(t+v)⁻¹)^2) := (hH n p hp hy).trans (mul_le_mul_of_nonneg_left (ice_two t (fuel (w d) n) v hp (fuel_pos ..) (fuel_le hw _)) (mul_nonneg (mul_nonneg hM (fuel_pos ..).le) hQ))
      apply (pow_le_pow_left₀ (norm_nonneg _) he 2).trans
      unfold due cost low coneWeight; rw [if_pos (show p d≤1 from hy.1), if_pos (show p d≤1 from hy.1)]
      let X := M*fuel 3 n*Q*(v*(t+v)⁻¹)^2
      have hs : (1:ℝ) ≤ 4*t/(t+R) := by rw [le_div_iff₀ (by positivity)]; linarith
      calc
        _ = 16*X^2*1 := by dsimp only [X]; ring
        _ ≤ 16*X^2*(4*t/(t+R)) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by change _ = (M*8*fuel 3 n)^2*((t+R)⁻¹*Q*(t*v^4/(t+v)^4*Q)); dsimp only [X]; simp only [div_eq_mul_inv, ← inv_pow]; ring
    rw [jar, indicator_of_notMem hy]; simpa using hP
  rw [indicator_of_notMem hx]; simpa using hP
lemma mote_size (w : Axis→ℝ) (d : Axis) (f : Panels) (e : ℂ) (he : ‖e‖=1)
    (h : ∀ p : ℝ,hat (f d) p≠0 → 1≤|p|) (a : ℝ) : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) (p : E4), 0≤p d →
    ‖((cave d a n)ᶜ.indicator (jar w d f e n) p)‖^2 ≤ (M*fuel (3+a/2) n)^2 * (due w d a n p * due w d 0 n p) := by
  obtain ⟨M,hM,hH⟩ := track_size w d f e he h
  refine ⟨M*2,mul_nonneg hM (by norm_num), fun n p hp => ?_⟩
  let Y := (M*2*fuel (3+a/2) n)^2 * (due w d a n p * due w d 0 n p)
  have hY : 0≤Y := mul_nonneg (sq_nonneg _) (mul_nonneg (due_nn _ _ _ _ p hp) (due_nn _ _ _ _ p hp))
  by_cases hx : p∈ (cave d a n)ᶜ
  · rw [indicator_of_mem hx]
    by_cases hy : p∈cove w d n
    · let Q := crop (other d) (homes w n) p
      have hQ : 0≤ Q := crop_nonneg _ _ (fun i _ => home_lit w n i) p
      have he : ‖jar w d f e n p‖ ≤ M*fuel 3 n*Q := (hH n p hp hy).trans
        (mul_le_of_le_one_right (mul_nonneg (mul_nonneg hM (fuel_pos ..).le) hQ) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hp (fuel_pos ..).le))))
      apply (pow_le_pow_left₀ (norm_nonneg _) he 2).trans
      let R := fuel a n; let t := p d; have hr : 0<R := fuel_pos ..
      have ht : t ≤ 1 := hy.1; change ¬ R≤t at hx; change 0≤t at hp
      have hh : (1:ℝ) ≤ 2*R/(t+R) := by rw [le_div_iff₀ (by positivity)]; linarith
      have hI : (1:ℝ) ≤ 2/(t+1) := by rw [le_div_iff₀ (by positivity)]; linarith
      unfold due cost low; rw [if_pos (show p d≤1 from hy.1), if_pos (show p d≤1 from hy.1),← fuel_mul, fuel0]
      change _≤ (M*2*(fuel 3 n * fuel (a/2) n))^2*((t+R)⁻¹*Q*((t+1)⁻¹*Q))
      calc
        _ ≤ (M*fuel 3 n*Q)^2*(2*R/(t+R)*(2/(t+1))) := by apply le_mul_of_one_le_right (sq_nonneg _) (one_le_mul_of_one_le_of_one_le hh hI)
        _ = _ := by rw [mul_pow (M*2), mul_pow (fuel 3 n),show fuel (a/2) n^2=R by unfold R; rw [sq,fuel_mul,add_halves]]; ring
    rw [jar,indicator_of_notMem hy]; simpa using hY
  rw [indicator_of_notMem hx]; simpa using hY
end YM.Outer
