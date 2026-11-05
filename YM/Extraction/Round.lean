import YM.Extraction.Patch
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Cyclic step-function Riemann cells with ceil rounding

Offsets in *right*-closed convention. Includes volume check, crucial for
local weak limits and true-Wilson assembly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter MeasureTheory Lattice
open scoped Topology ContDiff BigOperators
variable {S : Schedule} {n : ℕ}

def address (t : ℝ) (x : Points n) : Fin n → Cover := fun i a => ⌈x i a / t⌉

def tile (t : ℝ) (a : ℤ) := Ioc (t*(a-1 : ℝ)) (t*(a:ℝ))

lemma tile_bounds {t : ℝ} (ht : 0 < t) (a : ℝ) (i : ℤ) : ⌈a/t⌉ = i ↔ a ∈ tile t i := by
  rw [Int.ceil_eq_iff, lt_div_iff₀ ht, div_le_iff₀ ht, tile]; simp [mul_comm]

def segment (t : ℝ) (p : Fin n → Cover) : Set (Points n) := {x | address t x = p}

def flat (n : ℕ) (x : Points n) := WithLp.ofLp (Points.flatten x)

lemma preserves : MeasurePreserving (flat n) := (PiLp.volume_preserving_ofLp _).comp (Points.flatten.measurePreserving)

lemma cart {t : ℝ} (ht : 0 < t) (p : Fin n → Cover) : segment t p =
    flat n ⁻¹' Set.pi univ (fun w : Fin n × Axis => tile t (p w.1 w.2)) := by
  ext x
  constructor
  · rintro (h : address t x = p) w _
    exact (tile_bounds ht _ _).mp (congr_fun (congr_fun h w.1) w.2)
  intro h; refine funext fun i => funext fun a => ?_
  exact (tile_bounds ht _ _).mpr (h (i,a) (mem_univ _))

theorem measurable_segment {t : ℝ} (ht : 0 < t) (p : Fin n → Cover) : MeasurableSet (segment t p) := by
  rw [cart ht]; exact (preserves (n := n)).measurable (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc)

theorem cell_volume {t : ℝ} (ht : 0 < t) (p : Fin n → Cover) :
    volume (segment t p) = ENNReal.ofReal (t^(4*n)) := by
  rw [cart ht, (preserves (n := n)).measure_preimage]
  · change (Measure.pi fun _ : Fin n × Axis => volume) _ = _
    rw [Measure.pi_pi]
    have he (i : Fin n × Axis) : volume (tile t (p i.1 i.2)) = ENNReal.ofReal t := by
      unfold tile; rw [Real.volume_Ioc]; congr 1; ring
    simp_rw [he]; rw [Finset.prod_const, Finset.card_univ,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_fin, ← ENNReal.ofReal_pow (by positivity), Nat.mul_comm]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).nullMeasurableSet

/-- Right-closed fundamental domain. -/
def Fund (S : Schedule) (p n : ℕ) := {x : Points n | ∀ i a, - S.radius p < x i a ∧ x i a ≤ S.radius p}

def tag (t : ℝ) (p : Fin n → Cover) : Points n := points fun i => WithLp.toLp 2 fun a => t * p i a

theorem coord_grid_bound {t : ℝ} (ht : 0 < t) (x : Points n) (i a) : |tag t (address t x) i a - x i a| ≤ t := by
  have he := (tile_bounds ht (x i a) (address t x i a)).mp rfl
  unfold tile at he
  have ha := he.1; have hb := he.2
  change |t * ((address t x i a : ℤ) : ℝ) - x i a| ≤ _; rw [abs_le]
  constructor <;> linarith

theorem approximate {t : ℝ} (ht : 0 < t) (x : Points n) : dist (tag t (address t x)) x ≤ (4*n : ℝ)*t := by
  let E := tag t (address t x) - x
  rw [dist_eq_norm]
  change ‖E‖ ≤ (4*n : ℝ)*t
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), ← (Points.flatten.norm_map E), EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _k : Fin n × Axis, t^2 := Finset.sum_le_sum fun i _ => sq_le_sq.mpr
      (by rw [abs_of_pos ht]; exact coord_grid_bound ht x i.1 i.2)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_mul,Nat.cast_ofNat]
      rcases Nat.eq_zero_or_pos n with h|h
      · rw [h]; simp
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hf : (1:ℝ) ≤ n := by exact_mod_cast h
      nlinarith

lemma chosen (x : Points n) : Tendsto (fun N => tag (S.a N) (address (S.a N) x)) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun i => approximate (S.a_pos i) _) ?_
  convert (S.shrinks.const_mul (4*n : ℝ)) using 1; simp

/-- Partition of fundamental cell; right-closed seams. -/
theorem tile_in {N p : ℕ} (r : Fin n → Site (S.side N p)) :
    segment (S.a N) (fun i => lift (r i)) ⊆ Fund S p n := by
  intro x hx i a
  let y := lift (r i) a
  set t := S.a N
  obtain ⟨hp,hP⟩ := (tile_bounds (S.a_pos N) _ y).mp (congr_fun (congr_fun (show address t x = _ from hx) i) a)
  have he := S.places_period (r i) a
  obtain ⟨c, hc⟩ := (S.side_four N p)
  have hz : -(c*2 : ℤ) < y := by
    have hy := (lift_centers (r i) a).1
    rw [hc] at hy; change -(((4*c : ℕ)) : ℤ) < 2*y at hy; omega
  have hu : (- (c:ℝ)*2 + 1) ≤ y := by
    exact_mod_cast (show (-(c:ℤ)*2+1) ≤ y by omega)
  constructor
  · apply lt_of_le_of_lt _ hp
    rw [Schedule.radius,← S.span_side N p, hc, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hu (S.a_pos N).le]
  exact hP.trans he.2

theorem corners {p N} {x : Points n} (h : x ∈ Fund S p n) :
    ∃! r : Fin n → Site (S.side N p), x ∈ segment (S.a N) (fun i => lift (r i)) := by
  let u := address (S.a N) x
  let r (i) : Site (S.side N p) := wrap _ (u i)
  have he (i) : lift (r i) = u i := by
    rw [lift_eq_iff]
    refine ⟨rfl,fun a => ?_⟩
    have hw := h i a
    rw [Schedule.radius, ← S.span_side N p] at hw
    have hv := (tile_bounds (S.a_pos N) _ (u i a)).mp (show _ from (@rfl ℤ (u i a)))
    obtain ⟨c,hc⟩ := S.side_four N p
    constructor
    · apply (show ((-(S.side N p).val : ℤ) : ℝ) < ((2*u i a : ℤ) : ℝ) → _ from
        fun w => by exact_mod_cast w)
      push_cast
      nlinarith [hw.1,hv.2,S.a_pos N]
    rw [hc]; suffices hs : u i a ≤ (c:ℤ)*2 by omega
    by_contra! hk
    rw [hc,Nat.cast_mul,Nat.cast_ofNat] at hw
    have he' : (c : ℝ) * 2 + 1 ≤ u i a := by exact_mod_cast (show (c:ℤ)*2+1 ≤ u i a by omega)
    nlinarith [mul_le_mul_of_nonneg_left he' (S.a_pos N).le,hv.1,hw.2]
  refine ⟨r,(show u = _ from funext fun i => (he i).symm),?_⟩
  rintro v (h : u = _)
  exact funext fun i => (wrap_lift (v i)).symm.trans (congr_arg (wrap _) (congr_fun h i).symm)
end YM.Extraction
