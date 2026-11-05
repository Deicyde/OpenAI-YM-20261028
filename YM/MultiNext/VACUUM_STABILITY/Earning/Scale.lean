import YM.MultiNext.VACUUM_STABILITY.Holding.Offers
import YM.Next.SCHEDULE.Clocks


set_option warningAsError false

/-!
# Numeric test against the proposed scales

This is per pair of PRE-chosen stages, not an unauthorized choice of L or post-L values from
mesh results. Use at scheduling to issue delays at actual parameter gates without confusing an
data estimate uniform across stages with a realization chosen after integration. Shows template
with paid held-operator scores plausible *numerically*. No theorem constructing physical
trajectory costs; still inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Earning
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture
open Arrival Arrival.Flock Tune Gauss Tree YM.Push.SectorMeasure Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

abbrev proxy (x : ℝ) := Clock.watch 2 x
abbrev Blocks := Clock.cover

def Modest (f : ℝ → ℝ) := ∃ c : ℝ, ∃ p : ℕ, ∀ᶠ x : ℝ in atTop, 0 ≤ f x ∧ f x ≤ c*(proxy x)^p

def Rapid (f : ℝ → ℝ) := (∀ᶠ x in atTop,0 ≤ f x) ∧ ∀ k : ℕ, Tendsto (fun x => (proxy x)^k*f x) atTop (𝓝 0)

namespace Modest
variable {f g : ℝ → ℝ}

private lemma bookings (h : Modest f) : ∃ c : ℝ, 0 ≤ c ∧ ∃ p : ℕ, ∀ᶠ x : ℝ in atTop, 0 ≤ f x ∧ f x ≤ c*(proxy x)^p := by
  obtain ⟨c,p,h⟩:=h; refine ⟨max c 0,le_max_right ..,p,?_⟩; filter_upwards [h] with i hi
  exact ⟨hi.1,hi.2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg (Clock.wp ..).le _))⟩

lemma simple {c : ℝ} (he : 0≤c) : Modest fun _ => c := ⟨c,0,Eventually.of_forall fun _ => by simp [he]⟩

lemma weaker (h : Modest f) (hg : ∀ᶠ x in atTop, 0≤g x ∧ g x≤f x) : Modest g := by
  obtain ⟨c,p,h⟩:=h; exact ⟨c,p,hg.mp (h.mono fun _ hh hg => ⟨hg.1,hg.2.trans hh.2⟩)⟩



lemma prod (h : Modest f) (hg : Modest g) : Modest fun x => f x*g x := by
  obtain ⟨c,n,h⟩:=h; obtain ⟨d,p,hg⟩:=hg
  refine ⟨c*d,n+p,?_⟩; filter_upwards [h,hg] with x hx hy
  exact ⟨mul_nonneg hx.1 hy.1,(mul_le_mul hx.2 hy.2 hy.1 (hx.1.trans hx.2)).trans_eq (by rw [pow_add]; ring)⟩

lemma plus (h : Modest f) (hg : Modest g) : Modest fun x => f x+g x := by
  obtain ⟨c,hc,n,h⟩:=bookings h; obtain ⟨d,hd,p,hg⟩:=bookings hg
  refine ⟨c+d,max n p,?_⟩; filter_upwards [h,hg,(Clock.growing (by norm_num : (0:ℝ)<2)).eventually_ge_atTop 1] with x hx hy hh
  rw [add_mul]; exact ⟨add_nonneg hx.1 hy.1,add_le_add (hx.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (le_max_left ..)) hc))
    (hy.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (le_max_right ..)) hd))⟩

lemma growPower (h : Modest f) (k : ℕ) : Modest fun x => f x^k := by
  induction k with
  | zero => simpa only [pow_zero] using simple zero_le_one
  | succ k hk => simp_rw [pow_succ]; exact prod hk h

lemma period : Modest fun x => ((Blocks x:ℕ):ℝ) := by
  refine ⟨1,1,?_⟩; filter_upwards [(Clock.ceiling_cheaper 2 1 1 (by norm_num) (by norm_num)).eventually
    (ge_mem_nhds zero_lt_one)] with x hx
  have hp := Clock.wp 2 x
  have he : 1+((Clock.cover x:ℕ):ℝ) ≤ Clock.watch 2 x := by
    change (1+((Clock.cover x:ℕ):ℝ))^ (1:ℕ) / Clock.watch 2 x ^ (1:ℝ) ≤ 1 at hx
    simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hp (1:ℝ))).mp hx
  exact ⟨by positivity,by simp only [Blocks,proxy,pow_one,one_mul]; linarith⟩
end Modest

namespace Rapid
variable {f g : ℝ → ℝ}



lemma weaker (h : Rapid f) (hg : ∀ᶠ x in atTop,0 ≤ g x ∧ g x ≤ f x) : Rapid g := by
  refine ⟨hg.mono fun i h=>h.1,fun k => squeeze_zero' ?_ ?_ (h.2 k)⟩
  · exact hg.mono fun i h => mul_nonneg (pow_nonneg (Clock.wp ..).le _) h.1
  exact hg.mono fun i h => mul_le_mul_of_nonneg_left h.2 (pow_nonneg (Clock.wp ..).le _)







lemma shines (c : ℝ) (hc : 0 < c) : Rapid fun i => Clock.gap i ^ c := by
  refine ⟨?_, fun k => by simpa using Clock.light 2 (k:ℝ) c hc⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact (Real.rpow_pos_of_pos (Clock.gp hx) _).le



/-- One example of barrier. For adjacent change x→x+C, use first
Alike.power or comparison, not tˆ as function of earlier actual β. -/
lemma forced (c : ℝ) (hc : 0 < c) : Rapid fun x => Real.exp (- c * proxy x ^ ((1:ℝ)/5)) := by
  have h : Rapid Clock.gap := by simpa using shines 1 zero_lt_one
  refine h.weaker ?_
  filter_upwards [(Clock.burnt (-1) c 2 (1/5) hc (by norm_num) (by norm_num)).eventually (ge_mem_nhds zero_lt_one),
    eventually_gt_atTop (0:ℝ)] with x hx hy
  have he := Clock.gp hy; refine ⟨(Real.exp_pos _).le,?_⟩
  change Clock.gap x ^ (-(1:ℝ)) * _ ≤ (1:ℝ) at hx
  rwa [Real.rpow_neg_one,inv_mul_le_iff₀ he,mul_one] at hx
end Rapid
end YM.Multi.Vacuum.Earning
