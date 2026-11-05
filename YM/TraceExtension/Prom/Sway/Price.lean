import YM.Next.RANK.ParticleGate
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Set Labels Filter Perch  Rise Glimmer Normal MvPolynomial Marker
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p : ℕ}

lemma incomeSky (h : G.Simple) (H : C.Makes) (v : C.label d) : ∀ᶠ k : ℕ in atTop, ∀ b:ℝ, 0 ≤ b →
    ∀ N (p : ℕ) (_ : k≤N) (T : C.label d→ₗ[ℂ] C.label d), Price.Tested C d k N p T →
      ∀ u, Price.Solves C (Station.mag C.path.levels b k) d k N p T v u →
        C.path.levels.clock.monitor k * (C.labels.level d).coeffSize (Price.awake C d k N p u) ≤ bill (b*d+saves C d) (clim C.path.levels k) := by
  let F := C.labels.level d; let P := C.path.levels
  let q := leash F
  let γ := (q:ℝ)+1
  filter_upwards [ (hat_rate P h).eventually (transports (show γ < saves C d from by dsimp [γ,q,saves,F]; ring_nf; linarith) (2*(2:ℝ)^q *∑ i,‖v i‖))]
    with k hk b hv N p hp T ho u hi
  let m := P.clock.monitor k
  have hm : 1 ≤ m := Real.one_le_exp (sq_nonneg _)
  let ρ:= Station.mag P b k
  have hr : 1 ≤ ρ := Real.one_le_rpow hm hv
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
  let D : ℝ:=2*(2:ℝ)^q *∑ i,‖v i‖
  have he' : D*bill (b*d+γ) s ≤ bill (b*d+saves C d) s:= by
    rw [← overlap (b*d) γ,← overlap (b*d) (saves C d)]; change D*(_* _ )≤_ ; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
  apply le_trans _ he'; apply le_of_eq
  have h1 : ρ^d=bill (b*d) s := by rw [show ρ=_ from mag_bill P b k,bills]
  change m*(2*(b₀^q*ρ^d* _))= _ * bill (b*d+γ) s
  dsimp only [b₀]; rw [mul_pow,show m=_ from fire_bill P k,show bill 1 (clim P k)=bill 1 s from rfl,bills,h1]
  unfold γ D; rw [← overlap,← overlap]; ring_nf
lemma loveSky (h : G.Simple) (H : C.Makes) (v : C.label d) : ∀ᶠ k : ℕ in atTop, ∀ b:ℝ, 0 ≤ b →
    ∀ N (p : ℕ) (_ : k≤N) (n : ℕ) (M : Heater C k d) (T : C.label d→ₗ[ℂ] C.label d), Heating C k N p d n M T →
      ∀ u, Price.Solves C (Station.mag C.path.levels b k) d k N p T v u →
        coin (M u) ≤ bill (b*d+saves C d) (clim C.path.levels k) := by
  filter_upwards [incomeSky h H v] with k he b hb N p hp n M T ht u hg; exact (ht.primal u).trans (he b hb N p hp T ht.span u hg)
end YM.Next.Rank.Atlas
