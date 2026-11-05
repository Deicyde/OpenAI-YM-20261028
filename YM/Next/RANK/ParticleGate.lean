import YM.Next.RANK.Compass
import YM.Next.RANK.ScaleJet
import YM.Next.RANK.Zone

/-!
# Fixed charges of Taylor/Wick chamber pipeline

No study only of x on reflected translated torus after changing grouping. Use
the finite probe read from this same coordinate reference (true representative).
Degree d fixed. Prices E prior to amplification by b; b must be big enough to
absorb those. Show this is doable in isolation (and keep that b for rows).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Set Labels Filter Perch  Rise Glimmer Normal MvPolynomial Marker
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p : ℕ}

-- $b_s(Y)$ on the k-stencil for *any primary*. These are the already-oriented
-- Wick coefficients (can form normal polynomial using control defined earlier).
-- Need same coordinate and kernel after pulling ALL copies to that alignment. E
-- pre-Q h numbers may right-multiply by a fixed basis change first, don't undo it here.

abbrev clim (A : Levels G) (k : ℕ) := A.clock.hatBeta k
abbrev wood (A : Levels G) (k : ℕ) := lengthW (clim A k)
abbrev Heater (C : Family G) (k d : ℕ) := C.label d →ₗ[ℂ] poly (trimV (wood C.path.levels k) G)

-- Use p in the raw bound on Heating coefficients per k, unscaled labels
structure Heating (C : Family G) (k N p d n : ℕ) (M : Heater C k d) (T : C.label d→ₗ[ℂ] C.label d) : Prop where
  span : Price.Tested C d k N p T
  primal (v : C.label d) : coin (M v) ≤ C.path.levels.clock.monitor k * (C.labels.level d).coeffSize (Price.awake C d k N p v)
  order (v : C.label d) : MvPolynomial.totalDegree (M v) ≤ n
  test (v : C.label d) : Perch.Verdict (Subtype.val : trimV (wood C.path.levels k) G→_) d (M v)
    ((C.labels.level d).coords.symm ((C.labels.level d).scaled (Price.shrink C k N p) (T v)))

lemma mag_bill (C : Levels G) (b : ℝ) (k) : Station.mag C b k=bill b (clim C k) := by
  unfold Station.mag Calendar.monitor bill boil; rw [← Real.exp_mul]; rfl
lemma fire_bill (C : Levels G) (k) : C.clock.monitor k=bill 1 (clim C k) := (Real.rpow_one _).symm.trans (mag_bill C 1 k)

def leash (F : Frame G d) := Finset.univ.sup fun i => (F.grades i).2
-- E=degree of monomial in connection at realization plus safety
def saves (F : Family G) (d : ℕ) : ℝ := leash (F.labels.level d)+2

lemma income (b : ℝ) (hv : 0<b) (h : G.Simple) (H : C.Makes) (v : C.label d) : ∀ᶠ k : ℕ in atTop,
    ∀ N (p : ℕ) (_ : k≤N) (T : C.label d→ₗ[ℂ] C.label d), Price.Tested C d k N p T →
      ∀ u, Price.Solves C (Station.mag C.path.levels b k) d k N p T v u →
        C.path.levels.clock.monitor k * (C.labels.level d).coeffSize (Price.awake C d k N p u) ≤ bill (b*d+saves C d) (clim C.path.levels k) := by
  let F := C.labels.level d; let P := C.path.levels
  let q := leash F
  let γ := b*d+(q:ℝ)+1
  filter_upwards [ (hat_rate P h).eventually (transports (show γ < b*d+saves C d from by dsimp [γ,q,saves,F]; ring_nf; linarith) (2*(2:ℝ)^q *∑ i,‖v i‖))]
    with k hk N p hp T ho u hi
  let m := P.clock.monitor k
  have hm : 1 ≤ m := Real.one_le_exp (sq_nonneg _)
  let ρ:= Station.mag P b k
  have hr : 1 ≤ ρ := Real.one_le_rpow hm hv.le
  let f := T u
  let a:= Price.shrink C k N p
  have hz : 0<a := Price.shrink_pos C H hp p
  have he : f = F.scaled a⁻¹ (Price.weightTag C d ρ v) := by
    have ht : F.scaled a f= _ := hi
    rw [← ht]; have hh := F.scaled_inv (inv_ne_zero hz.ne') f; rw [inv_inv] at hh; exact hh.symm
  let s := clim P k
  let b₀ : ℝ := 2*m
  have hc (i) : ‖f i‖ ≤ b₀^q * ρ^d*‖v i‖ := by
    rw [he]; unfold Price.weightTag; simp only [Frame.scaled_apply,LinearMap.coe_mk,AddHom.coe_mk,norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hz).le _)]
    have hF : a⁻¹ ≤ b₀ := Price.shrink_min C H hp p
    simp only [Real.norm_of_nonneg (zero_le_one.trans hr)]
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [inv_pow]
    apply mul_le_mul ((by simp only [← inv_pow]; exact (pow_le_pow_left₀ (inv_pos.mpr hz).le hF _).trans (pow_le_pow_right₀ (show 1 ≤ b₀ by dsimp [b₀]; linarith) (Finset.le_sup (f:=fun i => (F.grades i).2) (Finset.mem_univ i)))) : _)
      (pow_le_pow_right₀ hr (F.bound _)) (pow_nonneg (zero_le_one.trans hr) _) ?_
    exact pow_nonneg (le_trans (inv_pos.mpr hz).le hF) _
  have h1' : F.coeffSize f ≤ b₀^q*ρ^d*(∑ i,‖v i‖) := by rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hc i
  refine (mul_le_mul_of_nonneg_left ((Price.Tested.cost C T ho u).trans (mul_le_mul_of_nonneg_left h1' (by positivity))) (zero_le_one.trans hm)).trans ?_
  apply le_trans _ hk; apply le_of_eq
  have h1 : ρ^d=bill (b*d) s := by rw [show ρ=_ from mag_bill P b k,bills]
  change m*(2*(b₀^q*ρ^d* _))= _ * bill γ s
  dsimp only [b₀]; rw [mul_pow,show m=_ from fire_bill P k,show bill 1 (clim P k)=bill 1 s from rfl,bills,h1]
  unfold γ; rw [← overlap,← overlap]; ring_nf
lemma love (b : ℝ) (hv : 0<b) (h : G.Simple) (H : C.Makes) (v : C.label d) : ∀ᶠ k : ℕ in atTop,
    ∀ N (p : ℕ) (_ : k≤N) (n : ℕ) (M : Heater C k d) (T : C.label d→ₗ[ℂ] C.label d), Heating C k N p d n M T →
      ∀ u, Price.Solves C (Station.mag C.path.levels b k) d k N p T v u →
        coin (M u) ≤ bill (b*d+saves C d) (clim C.path.levels k) := by
  filter_upwards [income b hv h H v] with k he N p hp n M T ht u hg; exact (ht.primal u).trans (he N p hp T ht.span u hg)
end YM.Next.Rank.Atlas
