import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Profiles
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FOUNDATIONS.TestBounds
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Along

/-!
Currency of transported incoming regular E letters. Real, all finite orders
through the input price, at arbitrary allowed fields, not just the bare chart.
Diagonal-left to ordinary bounds with no fine volume loss, also on differences
at two bindings of the field. No assumption that continuity of top derivatives
has a *linear* modulus uniform in labels and side. Keep that price explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.Foundations Push.Local
open scoped Topology BigOperators ContDiff Classical

private def Forms (i : ℕ) : Submodule ℝ (Tensor.T (Fin i → ℝ) ℝ i) where
  carrier := {T | Tensor.Sym T}
  zero_mem' := fun _ _ => rfl
  add_mem' {A B} (ha : Tensor.Sym A) (hb : Tensor.Sym B) v p := by simp only [add_apply,ha _ _,hb _ _]
  smul_mem' t A (ha : Tensor.Sym A) v p := by simp only [smul_apply,ha _ _]



def Polar (k : ℕ) (C : ℝ) := 1 ≤ C ∧ ∀ i ≤ k, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Tensor.T E ℝ i) (a : ℝ), 0 ≤ a → Tensor.Sym T → (∀ u, ‖u‖ ≤ 1 → ‖Tensor.diagonal T u‖ ≤ a) → ‖T‖ ≤ C*a


variable {G : Gauge} {n : Side} {p : BudgetPoint} {U V : Config G n} {o : Site n} {f g : Config G n → ℝ} {C a b : ℝ} {k : ℕ}

def normalized (p : BudgetPoint) (f : Config G n → ℝ) (V : Config G n) := dilate (f ∘ increment V) p.threshold
lemma tests {i : ℕ} (h : Chart i f V) (z : Directions G n) :
    Tensor.diagonal (iteratedFDeriv ℝ i (normalized p f V) 0) z = leftDerivs f (List.replicate i (p.threshold • z)) V := by
  have ht : ContDiffAt ℝ (↑i) (normalized p f V) 0 := dilate_smooth (by simpa using h)
  rw [← iteratedDeriv_on_line ht, ← Work.G07.at_zero_increment V, ← zero_smul ℝ (p.threshold • z),leftDerivs_diag,zero_smul,Work.G07.at_zero_increment]
  simp only [normalized,dilate,Function.comp_apply,smul_comm p.threshold]

structure Diagonals (k : ℕ) (p : BudgetPoint) (o : Site n) (U V : Config G n) (f g : Config G n → ℝ) (a b : ℝ) : Prop where
  a_nn : 0≤a
  b_nn : 0≤b
  chart_west : Chart k f U
  chart_east : Chart k g V
  west i (hi : i ≤ k) z (hz : p.dirBound o z) : ‖leftDerivs f (List.replicate i z) U‖ ≤ a
  east i (hi : i ≤ k) z (hz : p.dirBound o z) : ‖leftDerivs g (List.replicate i z) V‖ ≤ a
  budget i (hi : i ≤ k) z (hz : p.dirBound o z) : ‖leftDerivs f (List.replicate i z) U-leftDerivs g (List.replicate i z) V‖ ≤ b

lemma Diagonals.transfer (h : Diagonals k p o U V f g a b) (hp : Polar k C) :
    Towers k (normalized p f U) (normalized p g V) 0 0 (C*a) (C*b) := by
  have he {F : Config G n → ℝ} {U : Config G n} (h : Chart k F U) : ContDiffAt ℝ (↑k) (normalized p F U) 0 := dilate_smooth (by simpa using h)
  have hx := he h.chart_west
  have hy := he h.chart_east
  have hz (z : Directions G n) (hv : ‖z‖ ≤ 1) : p.dirBound o (p.threshold • z) := fun i => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg p.threshold_pos.le]; apply mul_le_mul_of_nonneg_left _ p.threshold_pos.le
    exact (norm_le_pi_norm _ i).trans (hv.trans (one_le_pow₀ (by simp)))
  refine ⟨hx,hy,fun i hi => ?_⟩
  have hw := Analysis.sym_Jet (hx.of_le (Nat.cast_le.mpr hi)); have hE := Analysis.sym_Jet (hy.of_le (Nat.cast_le.mpr hi))
  have H := tests (p:=p) (i:=i) (h.chart_west.of_le (Nat.cast_le.mpr hi) : Chart i f U)
  have H' := tests (p:=p) (i:=i) (h.chart_east.of_le (Nat.cast_le.mpr hi) : Chart i g V)
  refine ⟨hp.2 i hi _ _ a h.a_nn hw (fun z hu => (H z).symm ▸ h.west _ hi _ (hz z hu)),?_,?_⟩
  · exact hp.2 i hi _ _ a h.a_nn hE (fun z hu => (H' z).symm ▸ h.east _ hi _ (hz z hu))
  refine hp.2 i hi _ _ b h.b_nn (fun z s => congr_arg₂ (·-·) (hw z s) (hE z s)) (fun z hu => ?_)
  change ‖Tensor.diagonal (iteratedFDeriv ℝ i (normalized p f U) 0) z-Tensor.diagonal (iteratedFDeriv ℝ i (normalized p g V) 0) z‖ ≤ _
  rw [H,H']; exact h.budget i hi _ (hz z hu)






end YM.AnalyticBridge.MarginalMultiplier3b1d
