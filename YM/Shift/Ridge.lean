import Mathlib.Analysis.Distribution.Support
import YM.Boundary.Contour


/-!
# Abs positions: edge forecasts from *tested* time derivative & power

Instead of dyadic extension to get all-profile boundary: high-order Taylor
with height-integrable remainder after fixing common interior direction to
descent. Uniform estimate with LINEAR gap d common only along this
auxiliary ray, applies also arbitrary partial-boundary approaches. All
other W heights/relative derivatives still to be tested. Contract
`Breathes` for power (word-by-word, no uniformity over arity). `Lines` for
actual Cauchy Riemann. Absolute points (no translation invariance input).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Filter Set Function MeasureTheory LinearMap Probe LineDeriv Complex
open scoped Topology InnerProductSpace ContDiff BigOperators Interval ENNReal
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

def sunrise (n : ℕ) := {t : Heights n|Monotone t}
def dawn (t : Heights n) := place 0 t
def rate (n : ℕ) : Heights n := fun i => ↑i.val

/-- gap ≥ c. includes 0 and 1 slot conventions. -/
def broad (u : Heights n) (c : ℝ) := ∀ i j : Fin n, i < j → c ≤ u j-u i
lemma bigger {u : Heights n} (p : u∈east n) : u ∈ sunrise n := p.monotone
lemma begins {t : Heights n} (p : t∈sunrise n) (k : ℝ) (h : 0 ≤ k) : broad (t+k • rate n) k := by
  intro i j he
  change k ≤ t j+k*(j.val:ℝ)-(t i+k*(i.val:ℝ))
  have hv : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast he
  have hh : k * ((i.val:ℝ)+1) ≤ k*(j.val:ℝ) := mul_le_mul_of_nonneg_left hv h
  have ht := p he.le
  linarith
lemma dawns {t : Heights n} (p : t∈sunrise n) {k : ℝ} (h : 0<k) : t+k • rate n ∈ east n :=
  fun a b hp => sub_pos.mp (h.trans_le (begins p k h.le a b hp))
lemma grows {t : Heights n} (p : t∈east n) {k : ℝ} (h : 0≤k) : t+k • rate n∈east n := by
  rcases h.eq_or_lt with hh|hh
  · simpa [hh.symm] using p
  exact dawns (bigger p) hh
@[simp] lemma light (n) : (0:Heights n) ∈ sunrise n := monotone_const
lemma awaits {t : Heights n} (hp : t∈sunrise n) : (𝓝[east n] t).NeBot := by
  have he : Tendsto (fun k : ℝ => t+k • rate n) (𝓝[>] 0) (𝓝[east n] t) := by
    rw [tendsto_nhdsWithin_iff]; refine ⟨?_,?_⟩
    · have he : Continuous (fun k : ℝ => t+k • rate n) := by fun_prop
      simpa using (he.tendsto 0).mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with k hk using dawns hp hk
  exact he.neBot

lemma sways {F : Probe (Points n) →ₗ[ℂ] ℂ} (p : Joint n → ℝ) (hp : Continuous p) (h0 : p 0=0) (h : ∀ t, ‖F t‖ ≤ p t) : Continuous F := by
  apply continuous_of_continuousAt_zero F
  apply Metric.tendsto_nhds.mpr
  intro ε he
  rw [← h0] at he
  filter_upwards [(hp.tendsto 0).eventually (gt_mem_nhds he)] with x hx
  rw [map_zero,dist_zero_right]; exact lt_of_le_of_lt (h x) hx

def weight (f : Joint n) := ‖SchwartzMap.toLpCLM ℂ ℂ 1 volume f‖
@[simp] lemma feath (n) : weight (0 : Joint n)=0 := by rw [weight,map_zero,norm_zero]
lemma weight_eq (f : Joint n) : weight f=∫ x, ‖f x‖ := SchwartzMap.norm_toLp_one
lemma weight_cont : Continuous (@weight n) := continuous_norm.comp ((SchwartzMap.toLpCLM ℂ ℂ 1 (volume (α := Points n))).continuous)
lemma compromise (f : Joint n) (g : Points n → ℂ) (K : ℝ) (h : ∀ x, ‖g x‖ ≤ K) : ‖∫ x, g x * f x‖ ≤ K*weight f := by
  rw [weight_eq,← integral_const_mul]; refine norm_integral_le_of_norm_le (f.integrable.norm.const_mul K) (ae_of_all _ fun i => ?_)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)

namespace Waves
variable (F : Waves S)

/-- Germ independent of a on contour not assumed here. -/
def Breathes : Prop := ∀ n (v : Fin n → S.Union), ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m

def psi (v : Fin n → S.Union) (y : Heights n) (f : Joint n) :=
    ∫ x, F.restricted v y x * f x

def clock (a : Heights n) := (-Complex.I) • LineDeriv.lineDerivOpCLM ℂ (Joint n) (dawn a)

def Lines : Prop := ∀ n (v : Fin n → S.Union) (f : Joint n) (y a : Heights n) (i : ℝ), y+i • a∈east n →
    HasDerivAt (fun t : ℝ => F.psi v (y+t • a) f) (F.psi v (y+i • a) (clock a f)) i

def Bounds : Prop := ∀ n (v : Fin n → S.Union) (y : Heights n) (hy : y∈east n) (f : Joint n),
    Integrable (fun x => F.restricted v y x * f x)

def Along : Prop := ∀ n (v : Fin n → S.Union) f, ContinuousOn (fun y => F.psi v y f) (east n)

variable {v : Fin n → S.Union}
lemma beam (m : ℕ) (C : ℝ) (p : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x,
    ‖F.restricted v y x‖ ≤ C*k⁻¹^m) {y : Heights n} (h : y∈sunrise n) (f : Joint n) {k : ℝ} (hh : k ∈ Ioc 0 1) :
    k^m*‖F.psi v (y+k • rate n) f‖ ≤ C * weight f := by
  have he := hh.1
  refine (mul_le_mul_of_nonneg_left (compromise f _ _ (p _ _ hh (begins h _ hh.1.le))) (pow_nonneg he.le m)).trans_eq ?_
  rw [← mul_assoc, mul_left_comm, ← mul_pow,mul_inv_cancel₀ he.ne',one_pow,mul_one]
end Waves
end YM.Boundary
