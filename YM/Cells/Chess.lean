import YM.Cells.Polar
import YM.Cells.Flood
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chessboard theorem

Conditional internal only on seam reflection positive. Root is total number
of cells of the actual T. Proof independent of `S.a` conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (T : Tiling n) (β : ℝ)

theorem cells_positive : 0 < Fintype.card T.Cell := Fintype.card_pos

theorem root_nonneg (F : Config G n → ℂ) : 0 ≤ T.rootTest β F := Real.rpow_nonneg (norm_nonneg _) _

theorem powering (F : Config G n → ℂ) : (T.rootTest β F)^(Fintype.card T.Cell) = T.rootPower β (fun _ => F) := by
  unfold rootPower rootTest
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    inv_mul_cancel₀ (by exact_mod_cast T.cells_positive.ne'), Real.rpow_one]; rfl

theorem manyIntegral (F : T.Cell → Config G n → ℂ) (HF : ∀ i, Interior (T.chamber 0) (F i)) : Integrable (T.fullAt F)
    (law G n β) := ((show Interior univ (T.fullAt F) from Interior.combines _ _ fun i _ =>
      (T.copies i (HF _)).enlarges (subset_univ _)).integrable _)

lemma maximize {α : Type*} [Fintype α] [Nonempty α] (h : ∀ x a, Positive G β (T.bandCut x a))
    (f : α → Config G n → ℂ) (H : ∀ i, Interior (T.chamber 0) (f i)) :
    ∃ c : α, ∀ A : T.Cell → α, T.rootPower β (f ∘ A) ≤ T.rootPower β fun _ => f c := by
  classical
  let V (g : T.Cell → α) := T.rootPower β (f ∘ g)
  obtain ⟨B,hb,Hb⟩ := Finset.exists_max_image Finset.univ V Finset.univ_nonempty
  let Q (A) := V A = V B
  have Hx : T.Reflects Q := by
    intro p a F hF
    let A (x) := F (T.mate p a x)
    have hu := T.fold_both p a (h p a) (f ∘ F) (f ∘ A) (fun i => H _) (fun i => H _)
    have ht (F P : T.Cell → α) : T.assign p a (f ∘ F) (f ∘ P) = f ∘ T.assign p a F P := by
      funext x; simp only [assign, Function.comp_apply]; split <;> rfl
    rw [ht,ht,ht, show T.assign p a F A=F by
      funext i; unfold assign; split; rfl; simp [A]] at hu
    let m := V B
    let q := T.assign p a F F
    let r := T.assign p a A A
    change V F ^2 ≤ V q * V r at hu
    rw [show V F = m from hF] at hu
    have hv : V q ≤ m := Hb _ (Finset.mem_univ _)
    have hh : V r ≤ m := Hb _ (Finset.mem_univ _)
    have hk : 0 ≤ V q := norm_nonneg _
    have hl : 0 ≤ m := norm_nonneg _
    change V q=m
    apply le_antisymm hv
    rcases eq_or_lt_of_le hl with ht|ht
    · rwa [← ht]
    apply le_of_mul_le_mul_right _ ht
    exact (sq m) ▸ hu.trans (mul_le_mul_of_nonneg_left hh hk)
  obtain ⟨c,hc⟩ := T.existence Q Hx B rfl
  exact ⟨c,fun i => (Hb i (Finset.mem_univ _)).trans_eq (show V (fun _ => c) = V B from hc).symm⟩

lemma copied_scale (F : Config G n → ℂ) (t : ℝ) v U :
    T.copy v (fun U => (t:ℂ)*F U) U = (t:ℂ)*T.copy v F U := by
  classical
  simp only [copy]; split_ifs <;> simp

lemma rootPower_scale (F : T.Cell → Config G n → ℂ) (t : T.Cell → ℝ) (h : ∀ v, 0 ≤ t v) :
    T.rootPower β (fun v U => (t v:ℂ)*F v U) = (∏ v, t v) * T.rootPower β F := by
  let C := ∏ v : T.Cell, t v
  have hc : 0 ≤ C := Finset.prod_nonneg fun i _ => h _
  unfold rootPower moment
  simp_rw [fullAt,copied_scale,Finset.prod_mul_distrib, ← Complex.ofReal_prod,integral_const_mul]
  change ‖(C:ℂ) * _‖ = _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hc]

/-- WFS1. -/
theorem tiles (h : ∀ p a, Positive G β (T.bandCut p a)) (F : T.Cell → Config G n → ℂ) (H : ∀ p, Interior (T.chamber 0) (F p)) :
    T.rootPower β F ≤ ∏ i : T.Cell, T.rootTest β (F i) := by
  have he (ε : ℝ) (he : 0 < ε) : T.rootPower β F ≤ ∏ i : T.Cell, (T.rootTest β (F i)+ε) := by
    let r i := T.rootTest β (F i)+ε
    let X (i : T.Cell) := fun U => ((r i)⁻¹ : ℝ) • F i U
    have hw (i U) : X i U = (((r i)⁻¹ : ℝ) : ℂ) * F i U := Complex.real_smul
    have ht (i) : 0 < r i := add_pos_of_nonneg_of_pos (T.root_nonneg _ _) he
    obtain ⟨c,hc⟩ := T.maximize β h X (by intro i; rw [show X i = _ from funext (hw i)]; exact (H i).scale _)
    have hy := hc id
    rw [show X ∘ id = fun v U => (((r v)⁻¹ : ℝ) : ℂ) * F v U from funext fun i => funext (hw i),
      T.rootPower_scale β F _ (fun i => (inv_pos.mpr (ht i)).le)] at hy
    have hh : T.rootPower β (fun _ : T.Cell => X c) ≤ 1 := by
      rw [show X c = _ from funext (hw c),
        T.rootPower_scale β (fun _ => F c) (fun _ => (r c)⁻¹) (fun i => (inv_pos.mpr (ht c)).le),
        Finset.prod_const,Finset.card_univ, ← powering T β, ← mul_pow, inv_mul_eq_div]
      apply pow_le_one₀ (div_nonneg (T.root_nonneg _ _) (ht c).le)
      apply (div_le_one (ht c)).mpr
      exact (lt_add_of_pos_right _ he).le
    have Hf := hy.trans hh
    rw [Finset.prod_inv_distrib,inv_mul_eq_div] at Hf
    exact (div_le_one (Finset.prod_pos (fun i _ => ht i))).mp Hf
  have hx : Tendsto (fun ε : ℝ => ∏ i : T.Cell, (T.rootTest β (F i)+ε)) (𝓝[>] (0:ℝ))
      (𝓝 (∏ i : T.Cell, T.rootTest β (F i))) := by
    have ht : Continuous (fun ε : ℝ => ∏ i : T.Cell, (T.rootTest β (F i)+ε)) := by fun_prop
    simpa [ContinuousWithinAt] using ht.continuousAt.continuousWithinAt (x := 0) (s := Ioi 0)
  exact ge_of_tendsto hx ((show ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε from self_mem_nhdsWithin).mono fun ε hx => he ε hx)

/-- WFS2. -/
theorem adds (h : ∀ p a, Positive G β (T.bandCut p a)) (F P : Config G n → ℂ)
    (hf : Interior (T.chamber 0) F) (hp : Interior (T.chamber 0) P) :
    T.rootTest β (F+P) ≤ T.rootTest β F + T.rootTest β P := by
  classical
  let V (i : T.Cell → Bool) (a : T.Cell) := if i a then F else P
  have HV i a : Interior (T.chamber 0) (V i a) := by unfold V; split_ifs <;> assumption
  let A (b : Bool) := if b then F else P
  have HE : T.fullAt (fun _ => F + P) = fun U => ∑ i : T.Cell → Bool, T.fullAt (V i) U := by
    funext x; unfold fullAt
    have hg (i) : T.copy i (F+P) x = ∑ b : Bool, T.copy i (A b) x := by
      simp [copy, A]
    simp_rw [hg, Fintype.prod_sum]; rfl
  have hm (i) := T.tiles β h (V i) (HV i)
  apply le_of_pow_le_pow_left₀ (T.cells_positive.ne') (add_nonneg (T.root_nonneg ..) (T.root_nonneg ..))
  rw [T.powering]
  calc
    T.rootPower β (fun _ : T.Cell => F+P) = ‖∑ i : T.Cell → Bool, moment β (T.fullAt (V i))‖ := by
      rw [rootPower, HE]; congr 1; unfold moment; exact integral_finsetSum _ (fun i _ => T.manyIntegral _ _ (HV i))
    _ ≤ _ := norm_sum_le ..
    _ ≤ ∑ i : T.Cell → Bool, ∏ v, T.rootTest β (V i v) := Finset.sum_le_sum (fun i _ => hm i)
    _ = (T.rootTest β F + T.rootTest β P) ^ Fintype.card T.Cell := by
      conv_rhs => rw [← Finset.card_univ, ← Finset.prod_const]
      have hx : T.rootTest β F + T.rootTest β P = ∑ b : Bool, T.rootTest β (A b) := by simp [A]
      rw [hx, Fintype.prod_sum]
end YM.Cells.Tiling
