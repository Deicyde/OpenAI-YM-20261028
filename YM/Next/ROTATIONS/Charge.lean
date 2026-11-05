import YM.Next.ROTATIONS.Budget
import YM.Next.ROTATIONS.Switch
/-! # Live scales. True primary and high band costs. -/
noncomputable section
namespace YM.Outer
open Set Function Filter MeasureTheory Measure Row Boundary Probe OS Word Nodes
open scoped Topology NNReal ENNReal ContDiff BigOperators

def bill (x n) (f : Profile) := width (fuel x n) f
def mails (w : Axis → ℝ) (f : Grouping) (n : ℕ) (i : Axis) := bill (w i) n (f i)
lemma mail_room {x a : ℝ} (h : x<a) (f : Profile) (hf : Ends f) : ∀ᶠ n in atTop, Room (bill x n f) (fuel a n) := by
  obtain ⟨s,hs⟩ := hf.room
  filter_upwards [bigger h s] with i hi
  exact (hs.grow _ (fuel_pos ..)).inc hi
lemma bill_plus {f : Profile} (h : Plus f) (x n) : Plus (bill x n f) := h.tall _ (fuel_pos ..).le
lemma bill_cash (x n) (f : Profile) (K : ℝ) (hx : -K ≤ x) (v) :
    ‖bill x n f v‖ ≤ (SchwartzMap.seminorm ℝ 0 0 f)*fuel K n := by
  rw [bill,width_at,norm_mul,norm_inv,Real.norm_of_nonneg (fuel_pos ..).le,← fuel_neg,mul_comm]
  refine mul_le_mul (f.norm_le_seminorm ℝ _) (fuel_le ?_ n) (fuel_pos _ n).le (apply_nonneg _ _)
  linarith
lemma sum_cash (w : Axis→ℝ) (f : Grouping) (K n) (R : Finset Axis) (h : ∀ i∈R,-K≤w i) (p : E4) :
    ‖crop R (mails w f n) p‖≤ (∏ i∈R,SchwartzMap.seminorm ℝ 0 0 (f i))*fuel (K*R.card) n := by
  rw [crop, norm_prod,← fuel_rate,← Finset.prod_const (s:=R)]
  rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => bill_cash _ _ _ K (h i hi) _

lemma credit_budget (m j k : ℕ) (a : ℝ) (f : Profile) (x : ℝ) (d : ℝ) : Budget ( (x-d)*(2*k:ℕ))
    (fun n => credits m j k (a*fuel d n) (bill x n f)) := by
  let z := 2*k
  have hz : Budget ((x+ -d)*z) (fun n => (fuel x n*(fuel d n)⁻¹)^z*tally z f) := by
    simp_rw [mul_comm _ (tally z f)]
    exact (((budget_fuel x).prod (budget_inv d)).pow z).times _
  have hh := hz.times ((Nodes.coeff m j).coeff k * a⁻¹^z)
  rw [← sub_eq_add_neg] at hh
  refine hh.same (Eventually.of_forall fun i => ?_)
  dsimp only [credits,bill]; rw [tally_width z _ (fuel_pos ..),mul_pow,mul_inv,mul_pow]; ring
lemma width_mul (f : Profile) (x y : ℝ) : width (x*y) f = width x (width y f) := by
  ext z
  simp only [width_at]; rw [div_div]; simp only [mul_inv, mul_assoc]
lemma Plus.add {f g : Profile} (h : Plus f) (p : Plus g) : Plus (f+g) := fun _ => add_nonneg (h _) (p _)
lemma Plus.sum {ι : Type*} (s : Finset ι) {f : ι → Profile} (h : ∀ i∈s,Plus (f i)) : Plus (∑ i∈s,f i) := by
  intro x; rw [_root_.sum_apply]
  exact Finset.sum_nonneg (fun i hi => h i hi _)
lemma menu_plus (i j) : Plus (menu i j) := by
  refine Plus.tall ?_ _ (num_pos _).le
  intro x; rw [slash_at sun_far]; refine mul_nonneg ?_ (sun_plus _)
  rw [pow_mul]; positivity

lemma paid_bill (m : ℕ) (s : ℝ) (hs : 1≤s) (x d : ℝ) (hx : x≤d) (f : Profile) :
    ∃ g : Profile, Far g ∧ Plus g ∧ Reflects false g ∧ ∀ᶠ n in atTop,
      ∀ p : ℝ, ‖bake m (s*fuel d n) (bill x n f) p‖ ≤ bill d n g p := by
  have hf (j k : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ n in atTop, ‖credits m j k (s*fuel d n) (bill x n f)‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := (credit_budget m j k s f x d).rise (y:=0) (by
      apply mul_nonpos_of_nonpos_of_nonneg (sub_nonpos_of_le hx); positivity)
    exact ⟨C,hC,by simpa only [fuel0,mul_one] using h⟩
  choose C hC h using hf
  let G j k := width s (menu j k)
  let g : Profile := ∑ j∈Finset.range m,∑ k∈dish m j,C j k • G j k
  have ht j k : Plus (G j k) := (menu_plus j k).tall _ (show 0≤s by linarith)
  refine ⟨g,Far.sum _ (fun j _ => Far.sum _ (fun k _ => ((menu_far j k).width _).scale _)),Plus.sum _ (fun j _ => Plus.sum _ (fun k _ => (ht j k).scale _ (hC ..))),
    Reflects.sum _ (fun j _ => Reflects.sum _ (fun k _ => ((menu_even j k).tall _).scale _)),?_⟩
  filter_upwards [(eventually_all_finset (Finset.range m)).mpr fun j hj => (eventually_all_finset _).mpr fun k (_ : k∈dish m j) => h j k] with i h p
  simp only [bake,board,bill,g,_root_.sum_apply,_root_.map_sum, map_smul,_root_.smul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_smul, show width (s*fuel d i) (menu j k)=width (fuel d i) (G j k) by rw [mul_comm,width_mul],
    Real.norm_of_nonneg ((ht j k).tall (fuel d i) (fuel_pos ..).le p)]
  exact mul_le_mul_of_nonneg_right (h j hj k hk) (bill_plus (ht j k) _ _ p)

lemma far_gain (x : ℝ) (hx : 0≤x) (k : ℕ) (f : Profile) (hf : Far f) : ∃ C : ℝ,0≤C ∧
    ∀ n : ℕ, ∀ u : ℝ, ‖bill x n f u‖ ≤ C*fuel (-x*(2*k:ℕ)) n*‖u‖^(2*k) := by
  obtain ⟨r,hr,h⟩ := Metric.mem_nhds_iff.mp hf.2
  let Q := SchwartzMap.seminorm ℝ 0 0 f
  have hQ : 0 ≤ Q := apply_nonneg _ _
  let D := Q*r⁻¹^(2*k)
  have hD : 0 ≤ D := mul_nonneg hQ (pow_nonneg (inv_pos.mpr hr).le _)
  refine ⟨D,hD,fun i u => ?_⟩
  let w := fuel x i
  have hw : 1 ≤ w := by simpa only [fuel0] using fuel_le hx i
  rw [show fuel (-x*(2*k:ℕ)) i=((fuel x i)⁻¹)^(2*k) by rw [← fuel_rate, fuel_neg]]
  rw [bill,width_at]; by_cases he : r ≤ ‖u/w‖
  · have hy : D*r^(2*k) ≤ D*‖u/w‖^(2*k) := by gcongr
    have ht : D*r^(2*k)=Q := by dsimp only [D]; rw [inv_pow]; field_simp
    rw [ht,norm_div,Real.norm_of_nonneg (show 0 ≤ w from (fuel_pos x i).le),div_pow,div_eq_mul_inv] at hy
    rw [norm_mul,norm_inv,Real.norm_of_nonneg (fuel_pos ..).le]; calc
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hw)
      _ ≤ _ := (f.norm_le_seminorm ℝ _).trans (hy.trans_eq ?_)
    dsimp only [w]; rw [inv_pow]; ring
  have hx : f (u/w)=0 := h (Metric.mem_ball.mpr (by simpa using lt_of_not_ge he))
  change ‖w⁻¹*f (u/w)‖ ≤ _
  rw [hx,mul_zero,norm_zero]; positivity

lemma runs_order {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i) (H : S.Hierarchy)
    (A : Weight L) (hA : Pressed i A) : ∃ M : ℕ, ∀ m : ℕ,M ≤ m → ∀ (s : ℝ), 0<s → ∀ f : Profile, Ends f → Reflects false f →
        Runs (ν V A) i 1 (stamp (Resid m s f)) := by
  obtain ⟨D,hD⟩ := runs_point V H A hA
  refine ⟨D,fun m hm s hs f hf hl => hD _ (centred_hollow _ D ?_) _ (by norm_num)⟩
  exact fun i hi => correct m s hs f hf hl i (by omega)

variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i)

/-- Alternative cost with any high transverse axis moment. `z` turned into cap
before paying its band. -/
lemma far_pay (A : Weight L) (h : ℕ → Profile) (Q : Finset Axis) (f : Grouping) (w : Axis → ℝ)
    (hs : ∀ᶠ n in atTop, ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i (h n) p) (K : ℝ)
    (hj : ∀ j∈Q, -K ≤ w j) (j : Axis) (hi : j∈Q) (he : j≠i) (k : ℕ) (a : ℝ)
    (hp : ∀ᶠ n in atTop, Integrable (fun p : E4 => Reel i (h n) p * ‖p j‖^(2*k)) (ν V A))
    (ht : Budget a (fun n => ∫ p : E4, Reel i (h n) p * ‖p j‖^(2*k) ∂ν V A))
    (g : Profile) (hg : Far g) (u : ℝ) (hu : 0≤u) :
    Budget (-u*(2*k:ℕ)+K*((Q.erase i).erase j).card+a)
      (fun n => pay (ν V A) i Q (h n) (update (mails w f n) j (bill u n g))) := by
  obtain ⟨C,hC,hG⟩ := far_gain u hu k g hg
  let x : ℝ := -u*(2*k:ℕ)
  let T := (Q.erase i).erase j
  let M := ∏ l∈T, SchwartzMap.seminorm ℝ 0 0 (f l)
  let y := K*T.card
  apply ((((budget_fuel x).times C).prod ((budget_fuel y).times M)).prod ht).priced
  filter_upwards [hp,hs] with n hx hn
  unfold pay
  let μ := ν V A
  let R (p : E4) := Reel i (h n) p * ‖p j‖^(2*k)
  let W := (C*fuel x n)*(M*fuel y n)
  change _ ≤ W * integral μ R
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hx.const_mul W) ?_
  filter_upwards [before V A] with p hp
  rw [crop_cons (Q.erase i) _ j _ _ (Finset.mem_erase.mpr ⟨he,hi⟩),norm_mul,norm_mul,Real.norm_of_nonneg (hn p hp)]
  have hb : ‖crop T (mails w f n) p‖ ≤ M*fuel y n := sum_cash w f K n T (fun i hi => hj i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) p
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hG n _) hb (norm_nonneg _) ((hG n _).trans' (norm_nonneg _))) (hn p hp)) (le_of_eq ?_)
  dsimp only [W,x,R]; ring
lemma done_pay (A : Weight L) (h : ℕ → Profile) (Q : Finset Axis) (f : Grouping) (w : Axis → ℝ)
    (hs : ∀ᶠ n in atTop, ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i (h n) p)
    (hj : ∀ j∈Q,0≤w j) (a : ℝ) (hp : ∀ᶠ n in atTop, Integrable (Reel i (h n)) (ν V A))
    (ht : Budget a (fun n => ∫ p : E4, Reel i (h n) p ∂ν V A)) :
    Budget a (fun n => pay (ν V A) i Q (h n) (mails w f n)) := by
  let T := Q.erase i
  let M := ∏ l∈T, SchwartzMap.seminorm ℝ 0 0 (f l)
  apply (ht.times M).priced
  filter_upwards [hp,hs] with n hx hn
  unfold pay
  change _ ≤ M * integral (ν V A) (Reel i (h n))
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hx.const_mul M) ?_
  filter_upwards [before V A] with p hp
  rw [norm_mul, Real.norm_of_nonneg (hn p hp),mul_comm M]
  refine mul_le_mul_of_nonneg_left ?_ (hn p hp)
  have h : ∀ j∈T,-(0:ℝ)≤ w j := by simp_rw [neg_zero]; exact fun j h => hj j (Finset.mem_of_mem_erase h)
  simpa only [zero_mul,fuel0,mul_one] using sum_cash w f 0 n T h p
abbrev lamps (m : ℕ) (x d a : ℝ) (f : Profile) (n : ℕ) := Resid m (a*fuel d n) (bill x n f)
lemma lamp_signs (m : ℕ) (x d a : ℝ) (f : Profile) (hf : Ends f) (hp : Plus f) (n)
    (ha : 0<a) (hh : Room (bill x n f) (a*fuel d n)) (i) (p : E4) (hi : 0 ≤ p i) :
    0 ≤ Reel i (lamps m x d a f n) p := lamp_sign m (a*fuel d n) (bill x n f) (p i) (mul_pos ha (fuel_pos ..)) hi (hf.width _) (bill_plus hp x n) hh

lemma accounts (H : S.Hierarchy) (A : Weight L) (h : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ D : ℕ, ∀ (x d a : ℝ) (_ : 0 ≤ d) (_ : 1≤ a) (f : Profile), Ends f → Plus f →
    (∀ᶠ n in atTop, Room (bill x n f) (a*fuel d n)) → ∀ m : ℕ, D ≤ m →
    (∀ᶠ n in atTop, Integrable (fun p : E4 => Reel i (lamps m x d a f n) p * ‖p j‖^(2*k)) (ν V A)) ∧
    Budget (max (-x) (d*D)) (fun n => ∫ p : E4, Reel i (lamps m x d a f n) p * ‖p j‖^(2*k) ∂ν V A) := by
  obtain ⟨D,hD⟩ := surface V H A h j hj k
  refine ⟨D,fun x d a hd ha f hf hp hR m hm => ?_⟩
  obtain ⟨C,hC,ht⟩ := hD m (by omega) f hf hp
  have hx n : 1 ≤ a*fuel d n := one_le_mul_of_one_le_of_one_le ha (by simpa only [fuel0] using fuel_le hd n)
  constructor
  · filter_upwards [hR] with n hh; exact (ht _ (hx n) _ (fuel_pos ..) hh).1
  apply ((((budget_inv x).rise (le_max_left ..)).add ((((budget_fuel d).times a).pow D).rise (le_max_right ..))).times C).signed
  · filter_upwards [hR] with n hr
    refine integral_nonneg_of_ae ?_
    filter_upwards [before V A] with p hu
    exact mul_nonneg (lamp_signs m x d a f hf hp n (by linarith) hr i p hu) (pow_nonneg (norm_nonneg _) _)
  filter_upwards [hR] with n hh
  exact (ht _ (hx n) _ (fuel_pos ..) hh).2
end YM.Outer
