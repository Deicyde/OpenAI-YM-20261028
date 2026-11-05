import YM.Lattice.Subdivision
import YM.Space.Configurations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Spacing and period conventions, placements

Spacing `a`.

Endpoints never let this depend on physical period.

Schedule validity
`Gentle` states the asymptotic little-o clause.

The unbounded period list is
chosen strictly increasing.

Physical representatives for each period are
*right*-closed; test corners must be adapted accordingly.
-/

set_option autoImplicit false
noncomputable section
namespace YM
open Lattice Filter Set
open scoped ENNReal Topology

structure Schedule where
  block : ℕ → Side
  block_odd : ∀ m, Odd (block m).val
  block_large : ∀ m, 3 ≤ (block m).val
  period : ℕ → Side
  period_four : ∀ p, 4 ∣ (period p).val
  period_strict : StrictMono fun p => (period p).val

namespace Schedule
variable (S : Schedule)

def denominator : ℕ → Side
  | 0 => 1
  | k+1 => denominator k * S.block k

def steps (k q : ℕ) : Side :=
  match q with
  | 0 => 1
  | j+1 => steps k j * S.block (k+j)

@[simp] theorem den_zero : S.denominator 0 = 1 := rfl

theorem den_add (m q : ℕ) : S.denominator (m+q) = S.denominator m * S.steps m q := by
  induction q with
  | zero => simp [steps]
  | succ i h => rw [steps, ← mul_assoc, ← h]; rfl

theorem den_odd (m : ℕ) : Odd (S.denominator m).val := by
  induction m with
  | zero => exact odd_one
  | succ i h => exact h.mul (S.block_odd i)

theorem den_strict : StrictMono fun m => (S.denominator m).val := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [denominator, PNat.mul_coe]
  have := S.block_large n
  exact (Nat.lt_mul_iff_one_lt_right (S.denominator n).property).mpr (by omega)

def side (m p : ℕ) : Side := (S.period p) * S.denominator m

def radius (p : ℕ) : ℝ := (S.period p).val / (2 : ℝ)

theorem radius_pos (p : ℕ) : 0 < S.radius p := div_pos (by exact_mod_cast (S.period p).property) (by norm_num)

theorem radius_diverges : Tendsto S.radius atTop atTop := by
  exact (tendsto_natCast_atTop_atTop.comp S.period_strict.tendsto_atTop).atTop_div_const (by norm_num : 0 < (2:ℝ))

theorem side_four (m p) : 4 ∣ (S.side m p).val := dvd_mul_of_dvd_left (S.period_four p) _

def oneStep (m p : ℕ) : Ratio (S.side m p) (S.side (m+1) p) :=
  ⟨S.block m, by simp [side, denominator, ← mul_assoc]⟩

theorem oneStep_odd (m p : ℕ) : Odd (S.oneStep m p).count.val := S.block_odd m

def toDepth {m N : ℕ} (h : m ≤ N) (p : ℕ) : Ratio (S.side m p) (S.side N p) where
  count := S.steps m (N-m)
  exact_size := by
    have H : S.denominator N = _ := calc
      _ = S.denominator (m+(N-m)) := by rw [Nat.add_sub_of_le h]
      _ = _ := S.den_add m _
    rw [side, side, H]
    simp [mul_assoc]

theorem toDepth_odd {m N : ℕ} (h : m ≤ N) (p : ℕ) : Odd (S.toDepth h p).count.val := by
  have H (j : ℕ) : Odd (S.steps m j).val := by
    induction j with
    | zero => exact (by rw [steps]; exact odd_one)
    | succ j ih => rw [steps]; exact ih.mul (S.block_odd _)
  exact H _

def a (m : ℕ) : ℝ := ((S.denominator m).val : ℝ)⁻¹

@[simp] theorem a_zero : S.a 0 = 1 := by simp [a]

theorem a_step (m : ℕ) : S.a (m+1) = S.a m / (S.block m).val := by
  simp [a, denominator, div_eq_mul_inv, mul_comm]

theorem a_pos (m : ℕ) : 0 < S.a m := inv_pos.2 (by exact_mod_cast (S.denominator m).property)

theorem shrinks : Tendsto S.a atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp S.den_strict.tendsto_atTop)

theorem strictAnti : StrictAnti S.a := fun _ _ hab ↦
  inv_lt_inv₀ (by exact_mod_cast (S.denominator _).property) (by exact_mod_cast (S.denominator _).property) |>.2
    (by exact_mod_cast S.den_strict hab)

def scale (m : ℕ) : ℝ := Real.log ((S.a m)⁻¹)

theorem divergent : Tendsto S.scale atTop atTop := by
  unfold scale a
  simp only [inv_inv]
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp S.den_strict.tendsto_atTop)

@[simp] theorem scale_zero : S.scale 0 = 0 := by simp [scale]

theorem scale_succ (m) : S.scale (m+1) = S.scale m + Real.log (S.block m).val := by
  simp only [scale, a, inv_inv, denominator, PNat.mul_coe, Nat.cast_mul]
  rw [Real.log_mul]
  all_goals positivity

def Gentle : Prop :=
  Tendsto (fun m => Real.log (S.block m).val / S.scale m) atTop (𝓝 0)

/-- No need to additionally assume mesh inequality, it follows from Gentle. -/
theorem mesh_inequality (h : S.Gentle) : ∃ c > 0, ∀ m : ℕ, c * (S.a m)^2 ≤ S.a (m+1) := by
  have hh : ∀ᶠ m : ℕ in atTop, 1 ≤ S.a (m+1) / (S.a m)^2 := by
    filter_upwards [S.divergent.eventually (eventually_gt_atTop 0),
      h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm h1
    have ha := S.a_pos m
    have hL : 0 < ((S.block m).val : ℝ) := by exact_mod_cast (S.block m).property
    have he : Real.log ((S.block m).val : ℝ) / S.scale m < 1 := h1
    rw [div_lt_iff₀ hm, one_mul] at he
    have hl : (S.block m).val < ((S.a m)⁻¹ : ℝ) := (Real.log_lt_log_iff hL (inv_pos.mpr ha)).1 he
    rw [le_div_iff₀ (sq_pos_of_pos ha), one_mul, a_step, le_div_iff₀ hL]
    apply (mul_le_mul_of_nonneg_left hl.le (by positivity)).trans
    field_simp; rfl
  obtain ⟨n, hn⟩ := eventually_atTop.1 hh
  have H (i : ℕ) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ m < i, c ≤ S.a (m+1) / (S.a m)^2 := by
    induction i with
    | zero => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
    | succ i hi =>
      obtain ⟨c,hc,h1,hci⟩ := hi
      refine ⟨min c (S.a (i+1) / (S.a i)^2), lt_min hc (div_pos (S.a_pos _) (sq_pos_of_pos (S.a_pos _))),
        min_le_left _ _ |>.trans h1, ?_⟩
      intro m hm
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with w | w
      · exact min_le_left _ _ |>.trans (hci m w)
      rw [w]; exact min_le_right _ _
  obtain ⟨c,hc,h1,hcn⟩ := H n
  refine ⟨c,hc, fun m ↦ ?_⟩
  rw [← le_div_iff₀ (sq_pos_of_pos (S.a_pos _))]
  by_cases w : m < n
  · exact hcn m w
  exact h1.trans (hn m (not_lt.mp w))

def gridPoint (m : ℕ) (x : Cover) : E4 := WithLp.toLp 2 (fun i => S.a m * x i)

/-- Centered, *right*-closed fundamental cell representatives. -/
def place {m p : ℕ} (x : Site (S.side m p)) : E4 := S.gridPoint m (lift x)

theorem span_side (m p : ℕ) : S.a m * (S.side m p).val = (S.period p).val := by
  simp only [a, side, PNat.mul_coe, Nat.cast_mul]
  field_simp

theorem places_period {m p : ℕ} (x : Site (S.side m p)) (i : Axis) :
    S.place x i ∈ Ioc (- S.radius p) (S.radius p) := by
  have h := lift_centers x i
  have h1 : -( (S.side m p).val : ℝ) < 2 * (lift x i : ℤ) := by exact_mod_cast h.1
  have h2 : (2:ℝ) * (lift x i : ℤ) ≤ (S.side m p).val := by exact_mod_cast h.2
  rw [radius, ← span_side S m p]; constructor
  · change _ < S.a m * (lift x i : ℝ)
    linarith [mul_lt_mul_of_pos_left h1 (S.a_pos m)]
  · change S.a m * (lift x i : ℝ) ≤ _
    linarith [mul_le_mul_of_nonneg_left h2 (S.a_pos m).le]

theorem embeds_scale {m N : ℕ} {p} (r : Ratio (S.side m p) (S.side N p)) :
    S.a N * r.count.val = S.a m := by
  have hn : ((S.side m p).val : ℝ) ≠ 0 := by exact_mod_cast (S.side m p).property.ne'
  apply mul_right_cancel₀ hn
  rw [span_side, mul_assoc, mul_comm ((r.count.val) : ℝ), ← Nat.cast_mul, ← r.exact_size]
  exact S.span_side N p

theorem embeds_place {m N : ℕ} {p} (r : Ratio (S.side m p) (S.side N p))
    (x : Site (S.side m p)) : S.place (r.embed x) = S.place x := by
  rw [place, r.lift_embed]
  apply PiLp.ext
  intro i
  simp only [place, gridPoint, WithLp.ofLp_toLp, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast]
  rw [← mul_assoc, embeds_scale]
end Schedule
end YM
