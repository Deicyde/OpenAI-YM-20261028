import YM.Push.STATIONARY_UNIFORM.Paths

/-! # PreL-power accounting: no evaluation on an actual torus -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

def Tame (j : ℕ) (f : Patch → ℝ) : Prop := ∃ (u : ℕ) (C : ℝ), 0 < C ∧ ∀ P : Patch, P.J=j →
  |f P| ≤ C * (P.L.val:ℝ)^u
structure Lit (j : ℕ) (f : Patch → ℝ) : Prop where
  high : Tame j f
  low : Tame j (fun x => (f x)⁻¹)
  pos : ∀ P : Patch, P.J=j → 0<f P

variable {C : ℝ} {j : ℕ} {f g : Patch → ℝ}
lemma tame_k (a : ℝ) : Tame j (fun _ => a) := ⟨0,1+|a|,by positivity,fun x _ => by simp⟩
lemma lit_k (ha : 0<C) : Lit j (fun _ => C) := ⟨tame_k _, tame_k _, fun _ _ => ha⟩
lemma Tame.add (hf : Tame j f) (hg : Tame j g) : Tame j (fun x => f x+g x) := by
  obtain ⟨p,C,hC,hf⟩ := hf; obtain ⟨q,D,hD,hg⟩ := hg
  refine ⟨max p q,C+D,by positivity, fun x hx => ?_⟩
  have ht : 1 ≤ (x.L.val:ℝ) := by exact_mod_cast x.L.property
  apply le_trans ((abs_add_le ..).trans (add_le_add (hf _ hx) (hg _ hx))); rw [add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left ..)) hC.le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right ..)) hD.le)
lemma Tame.mul (hf : Tame j f) (hg : Tame j g) : Tame j (fun x => f x*g x) := by
  obtain ⟨p,C,hC,hf⟩ := hf; obtain ⟨q,D,hD,hg⟩ := hg
  refine ⟨p+q,C*D,by positivity, fun x hx => ?_⟩
  rw [abs_mul]; apply (mul_le_mul (hf _ hx) (hg _ hx) (abs_nonneg _) (by positivity)).trans_eq; rw [pow_add]; ring
lemma Tame.ltMore (hf : Tame j f) (he : ∀ x : Patch, x.J=j → |g x| ≤ f x) : Tame j g := by
  obtain ⟨p,C,hC,hf⟩ := hf
  exact ⟨p,C,hC,fun x hx => le_trans (he x hx) ((le_abs_self _).trans (hf _ hx))⟩
lemma Tame.at_eq (hf : Tame j f) (he : ∀ x : Patch, x.J=j → f x=g x) : Tame j g := by
  obtain ⟨p,C,hC,hf⟩ := hf; exact ⟨p,C,hC,fun x hx => by rw [← he x hx]; exact hf x hx⟩
lemma Tame.absolute (hf : Tame j f) : Tame j (fun x => |f x|) := by
  obtain ⟨p,C,hC,hf⟩ := hf; exact ⟨p,C,hC, fun x hx => by simpa using hf x hx⟩
lemma Tame.power (hf : Tame j f) (k : ℕ) : Tame j (fun x => (f x)^k) := by
  induction k with
  | zero => simp_rw [pow_zero]; exact tame_k _
  | succ k ih => simp_rw [pow_succ]; exact ih.mul hf
lemma Tame.exp' {j : ℕ} {f : Patch → ℝ} (h : ∀ P : Patch, P.J=j → f P ≤ C) : Tame j (fun x => Real.exp (f x)) := by
  refine (tame_k (Real.exp C)).ltMore ?_; intro x hx; rw [abs_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone (h x hx)

lemma lit_size : Lit j (fun x => x.L.val) := by
  refine ⟨⟨1,1,by norm_num,fun x _ => by simp⟩,(tame_k 1).ltMore (fun x _ => ?_), fun x _ => ?_⟩
  · rw [abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast x.L.property)
  exact_mod_cast x.L.property
lemma Lit.inv (hf : Lit j f) : Lit j (fun x => (f x)⁻¹) := ⟨hf.low,by simp_rw [inv_inv]; exact hf.high,fun x hx => inv_pos.mpr (hf.pos _ hx)⟩
lemma Lit.add_left (hf : Lit j f) (h : Tame j g) (hp : ∀ x : Patch, x.J=j → 0≤g x) : Lit j (fun x => f x+g x) := by
  refine ⟨hf.high.add h, hf.low.ltMore (fun x hx => ?_), fun x hx => add_pos_of_pos_of_nonneg (hf.pos x hx) (hp x hx)⟩
  have hh := hf.pos x hx; have he := hp x hx
  rw [abs_of_nonneg (by positivity)]; exact inv_anti₀ hh (by linarith)
lemma Lit.add (hf : Lit j f) (hg : Lit j g) : Lit j (fun x => f x+g x) := hf.add_left hg.high fun x hx => (hg.pos x hx).le
lemma Lit.mul (hf : Lit j f) (hg : Lit j g) : Lit j (fun x => f x*g x) := by
  refine ⟨hf.high.mul hg.high,?_, fun x hx => mul_pos (hf.pos x hx) (hg.pos x hx)⟩
  simp_rw [_root_.mul_inv]; exact hf.low.mul hg.low
lemma Lit.div (hf : Lit j f) (hg : Lit j g) : Lit j (fun x => f x/g x) := by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv
lemma Lit.pow (hf : Lit j f) (k : ℕ) : Lit j (fun x => (f x)^k) := ⟨hf.high.power _,by simp_rw [← inv_pow]; exact hf.low.power _,fun x hx => pow_pos (hf.pos x hx) _⟩
lemma Lit.min' (hf : Lit j f) (hg : Lit j g) : Lit j (fun x => min (f x) (g x)) := by
  have hu x (hx : x.J=j) : 0 < min (f x) (g x) := lt_min (hf.pos x hx) (hg.pos x hx)
  refine ⟨hf.high.ltMore (fun x hx => ?_),(hf.low.add hg.low).ltMore (fun x hx => ?_),hu⟩
  · rw [abs_of_nonneg (hu x hx).le]; exact min_le_left ..
  have hh := hf.pos x hx; have he := hg.pos x hx
  rw [abs_of_nonneg (inv_pos.mpr (hu x hx)).le]
  rcases le_total (f x) (g x) with h|h
  · rw [min_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  rw [min_eq_right h]; exact le_add_of_nonneg_left (by positivity)

lemma tame_radius (j : ℕ) : Tame j (fun x => x.radius) := by
  unfold Patch.radius
  simp_rw [Nat.cast_mul]
  refine ((tame_k ((j+3:ℕ):ℝ)).mul lit_size.high).at_eq ?_
  intro x hx; simp only [hx]
end YM.Push.Uniform
