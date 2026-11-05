import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Climb.Beams
import YM.Next.ROTATIONS.Tunnel
/-!
# Frozen-position tensor wave packets for exterior. The temporal test vanishes up
through a sold gap. This is NOT a spectral frequency-compact cutoff.
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace

def large (w : ℝ) (f : Form) : Form := if h : w=0 then 0 else ↑(w⁻¹) • along
  (ContinuousLinearEquiv.smulLeft (Units.mk0 w⁻¹ (inv_ne_zero h))) f
lemma large_at (w : ℝ) (f : Form) (p : ℝ) : large w f p = (w⁻¹:ℝ) • f (p/w) := by
  unfold large; split_ifs with h; · simp [h]
  change w⁻¹ • f (w⁻¹*p)=_
  rw [div_eq_mul_inv,mul_comm p]
lemma large_hat (w : ℝ) (f : Form) (hw : 0<w) (p : ℝ) : hat (large w f) p=hat f (w*p) := by
  rw [hat_eq,hat_eq]
  have he := Measure.integral_comp_mul_left (fun b : ℝ => plane b (-p)*large w f b) w
  have hh b : plane (w*b) (-p)=plane b (-(w*p)) := by unfold plane; simp; ring_nf
  simp_rw [hh,large_at,mul_div_cancel_left₀ _ hw.ne',mul_smul_comm] at he
  rw [integral_smul,abs_of_pos (inv_pos.mpr hw)] at he
  simp_rw [large_at,mul_smul_comm]; exact smul_right_injective _ (inv_ne_zero hw.ne') he.symm

/-- Adds the derivative amplitude on temporal factor. -/
def frozen (w : ℝ) (f : Form) := (w:ℂ) • large w f
lemma frozen_hat (w : ℝ) (f : Form) (hw : 0<w) (p : ℝ) : hat (frozen w f) p=(w:ℂ)*hat f (w*p) := by
  rw [frozen,map_smul,_root_.smul_apply, smul_eq_mul,large_hat _ _ hw p]
lemma frozen_away (w : ℝ) (f : Form) (hw : 0<w) (h : ∀ p : ℝ,hat f p ≠ 0 → 1≤|p|) :
    ∀ p : ℝ, hat (frozen w f) p≠0 → w⁻¹ ≤ |p| := by
  intro p hp
  have he : hat f (w*p)≠0 := by intro hz; apply hp; rw [frozen_hat w f hw,hz,mul_zero]
  have h := h (w*p) he; rw [abs_mul,abs_of_pos hw,mul_comm] at h
  rw [← one_div]; exact (div_le_iff₀ hw).mpr h
lemma frozen_size (b : ℂ) (hb : ‖b‖=1) (w : ℝ) (f : Form) (hw : 0<w) (h : ∀ p : ℝ,hat f p≠0 → 1≤|p|)
    (E : ℝ) (he : 0≤E) : ‖Lap b (frozen w f) E‖ ≤ (∫ t, ‖hat f t‖) * Real.exp (-(E/w)) := by
  have hp : (∫ t, ‖hat (frozen w f) t‖) = ∫ t, ‖hat f t‖ := by
    simp_rw [frozen_hat w f hw,norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.le]
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun t : ℝ => ‖hat f t‖),abs_of_pos (inv_pos.mpr hw), smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hw.ne',one_mul]
  rw [← hp,← integral_mul_const]; refine norm_integral_le_of_norm_le ((hat _).integrable.norm.mul_const _) ?_
  filter_upwards with t
  rw [damped_n b hb]
  by_cases hx : hat (frozen w f) t=0
  · simp [hx]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  rw [neg_mul,div_eq_mul_inv, mul_comm E]; exact neg_le_neg (mul_le_mul_of_nonneg_right (frozen_away _ f hw h t hx) he)

def tracks (w : Axis→ℝ) (d : Axis) (n : ℕ) (f : Panels) :=
    update (fun j => large (fuel (w j) n) (f j)) d (frozen (fuel (w d) n) (f d))

lemma track_far (w : Axis→ℝ) (d : Axis) (hw : w d<0) (f : Panels)
    (hf : ∀ p : ℝ, hat (f d) p≠0 → 1≤|p|) (R : ℝ) :
    ∀ᶠ n in atTop, ∀ p,hat (tracks w d n f d) p≠0 → R≤|p| := by
  filter_upwards [(fuel_grows (neg_pos.mpr hw)).eventually (eventually_ge_atTop R)] with n hn p hp
  unfold tracks at hp; rw [update_self] at hp
  rw [fuel_neg] at hn; exact hn.trans (frozen_away _ _ (fuel_pos ..) hf _ hp)

lemma track_reading (w : Axis→ℝ) (d : Axis) (n : ℕ) (f : Panels) (p : E4) :
    ‖reading d (tracks w d n f) p‖=∏ i∈other d,‖large (fuel (w i) n) (f i) (p i)‖ := by
  let g := tracks w d n f
  let x : Axis→ℂ := update (fun j => g j (p j)) d 1
  have he : reading d g p=∏ j,x j := by
    rw [Fin.prod_univ_succAbove _ d]; unfold x; rw [update_self,one_mul]
    unfold reading tests part
    exact Finset.prod_congr rfl fun k _ => by rw [update_of_ne (d.succAbove_ne k)]
  change ‖reading d g p‖=_
  rw [he,← Finset.mul_prod_erase _ _ (Finset.mem_univ d),show x d=1 from update_self ..,one_mul,norm_prod]
  exact Finset.prod_congr rfl fun i hi => by
    unfold x; rw [update_of_ne (Finset.mem_erase.mp hi).1]; unfold g tracks; rw [update_of_ne (Finset.mem_erase.mp hi).1]

abbrev scatter (w : Axis→ℝ) (d : Axis) (n : ℕ) := {p : E4 | ∀ j : Axis,j∈other d → |p j| ≤ fuel (1+w j) n }
lemma scatter_m (w : Axis→ℝ) (d : Axis) (n : ℕ) : MeasurableSet (scatter w d n) := by
  simp only [scatter,setOf_forall]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (by fun_prop) (measurable_const (a:=fuel (1+w _) n))
abbrev homes (w : Axis→ℝ) (n : ℕ) : Grouping := mails (fun j => 1+w j) (fun _ => center) n
lemma home_lit (w n i) : Plus (homes w n i) := bill_plus center_plus _ _

lemma scatter_size (w : Axis→ℝ) (d : Axis) (f : Panels) : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) p, p∈scatter w d n →
    ‖reading d (tracks w d n f) p‖ ≤ M*fuel 3 n*crop (other d) (homes w n) p := by
  let m i := SchwartzMap.seminorm ℝ 0 0 (f i)
  refine ⟨∏ i∈other d,m i,Finset.prod_nonneg (fun i _ => apply_nonneg _ _),fun n p hp => ?_⟩
  have he : fuel (3:ℝ) n = ∏ _i∈other d,fuel 1 n := by
    rw [Finset.prod_const, fuel_rate,show (other d).card=3 from by simp [other,Axis]]; norm_num
  rw [he,crop,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib,track_reading]; refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => ?_
  let W := fuel (1+w i) n
  have hw : 0<W := fuel_pos ..
  have hl : homes w n i (p i)=W⁻¹ := by
    unfold homes mails bill; rw [width_at]
    have hu : |p i/W| ≤ 1 := by rw [abs_div, abs_of_pos hw,div_le_one hw]; exact hp i hi
    rw [center_plane _ hu, mul_one]
  rw [hl,large_at,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (fuel_pos ..)).le]
  apply (mul_le_mul_of_nonneg_left ((f i).norm_le_seminorm ℝ _) (inv_pos.mpr (fuel_pos ..)).le).trans_eq
  change (fuel _ _)⁻¹ * m i=_
  unfold W; rw [← fuel_mul]; field_simp [ (fuel_pos 1 n).ne',(fuel_pos (w i) n).ne']
end YM.Outer
