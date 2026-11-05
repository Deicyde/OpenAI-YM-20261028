import YM.Further.DENSE_MIXED_KERNELS.Mileage
import YM.Further.DENSE_MIXED_KERNELS.Street

/-!
# Using the per-letter tests

Here speak about the actual chosen arrays (no assertion that they form a
valid simultaneous propagation). Cost ALSO for any global tree tag with its
weight; for reconstruction keep the same vault. Structural data are **inputs**,
not equations on supports obtained for free just because analytic budgets passed.
Transom is one way to supply variance and size budgets (even if supports wind).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Lattice RG Wilson Precision Labels Marker Overlay Extra.Multi Extra.Multi.Merger Tree
open Port Gaussian Surface Mileage
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {A : ChartRatio G} {H : Port A} {m n : Side} {S : StepData m n}
    {V I : Type} [Fintype I] [DecidableEq V] {R : Census V} {P : Rep G n} {L : Bands R P}
    {E F O : Layer G V m}
    {Z : Bazaar L S E F} {C : Vault I S}

/-- Economists: these numbers go into all-sector *primitive* tests,
never charged uniformly over the post-V off-support volume. -/
structure Oars where
  amp : ℝ   -- e.g. post-L with post polynomial cost, fixed independently of all volumes
  pos : 1≤amp
  degree : ℕ  -- r: extra word support powers
  sends : 0 < degree
  q : ℕ  -- Gaussian velocity exponent per derivative

namespace Oars
variable (W : Oars) (H : Port A) (Z : Bazaar L S E F) (M B k : ℕ) (e : Pieces→ℝ)

abbrev mileage (x : Chain (E.Id⊕F.Id)) := transom W.amp W.degree x (Z.scale M B)

def price (x : E.Id⊕F.Id) := shift H k W.q W.degree (Z.scale M B x) W.amp * Z.cash x * metric Z.owner e x

theorem loads {e : Pieces→ℝ} (he : ∀ i,0≤e i) (x) : 0≤W.price H Z M B k e x := mul_nonneg
    (mul_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 3) (Mileage.shift_pad H k W.q W.degree _ W.pos))
      ((Z.pays x).trans (Z.down_le x))) (by rcases x with i|i; exact he _; exact zero_le_one)

lemma income (x : Chain (E.Id⊕F.Id)) :
    Merger.paid (W.price H Z M B k e) (catalog x) = oneWord x * ((∏ i,metric Z.owner e (x.2 i)) * (∏ i, Z.cash (x.2 i)) *
      ∏ i,Mileage.shift H k W.q W.degree (Z.scale M B (x.2 i)) W.amp) := by
  rw [costed]; unfold price; rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]; ring
end Oars

variable {o : O.Id→Site m} {B : BudgetPoint} {k M : ℕ} {g : ℝ}
    {W : Oars} {x : Chain (E.Id⊕F.Id)}

/-- All-word constituent per tree average. -/
abbrev Stamp (H : Port A) (C : Vault I S) (Z : Bazaar L S E F) (x : Chain (E.Id⊕F.Id)) :=
    ∀ i, Word H (C.tree i) x L Z.owner

/-- Numeric window and analytic primitive grants BEFORE V integration with
markers. Need for every tree occurrence. -/
structure SizeUp (D : Stamp H C Z x) (B : BudgetPoint) (o : Site m) (s : Support m) (M : ℕ) (g : ℝ) (W : Oars) : Prop where
  earns : let T := W.mileage Z M B.B x
    ∀ i : I,(Fintype.card (↥(D i).model.J):ℝ) ≤ T ∧
      ((Module.finrank ℝ (H.front (D i).model.J (H.Room (D i).model.K))):ℝ)≤ T ∧
      ∀ u,Healthy B.threshold s u → (D i).Green g u (B.dirBound o) T T⁻¹ T (Z.cash ∘ x.2) B.order W.q

structure Workable (D : Stamp H C Z x) (B : BudgetPoint) (s I : Support m) (g : ℝ) : Prop where
  earns : ∀ i u, s ∩ RG.flags B.threshold u=I → (D i).Prepared g u ∧
    Dark (D i).model.base (D i).model.fare ((D i).post g) u (Z.down ∘ x.2) g

variable {κ γ : ℝ} (ht : L.Active) {e : Pieces→ℝ} (he : Inbox L γ e) (hl : γ ≤ 1)
include ht he hl

theorem SizeUp.use (D : Stamp H C Z x) {o : Site m} {s : Support m}
    (h : SizeUp D B o s M g W) (hg : 0<g) (hi : g ≤ 1) {U : Config G m} (hy : Healthy B.threshold s U) :
      (∀ᶠ v in 𝓝 0,∀ j, Integrable ((D j).pre g (increment U v))
        (((D j).model.base (increment U v)).ante (D j).model.fare)) ∧
      Pitch (C.pour fun i => (D i).value g) U (B.dirBound o) B.order
        (Merger.paid (W.price H Z M B.B B.order e) (catalog x)) 1 := by
  let T := W.mileage Z M B.B x
  have ht₀ : (Fintype.card x.Index:ℝ)≤ T := Mileage.enough_length x W.degree W.sends _ (Z.greater ht M B.B) W.pos
  have hT : 1 ≤ T := (Nat.one_le_cast.mpr Fintype.card_pos).trans ht₀
  have hz : 0≤∏ i,metric Z.owner e (x.2 i) := Finset.prod_nonneg fun i _ => by
    cases x.2 i
    case inl y => exact he.pos _
    case inr y => exact zero_le_one
  have hp i : 0≤ Z.cash (x.2 i) := (Z.pays _).trans (Z.down_le _)
  have hB (i) := (D i).green_light g U (inv_pos.mpr (zero_lt_one.trans_le hT)) hT (zero_le_one.trans hT) hg hi
    ht he hl hp ((h.earns i).2.2 U hy)
  refine ⟨eventually_all.mpr (fun i => (hB i).1), C.pitch fun i => (hB i).2.mono ?_ zero_le_one le_rfl⟩
  rw [Oars.income]; apply mul_le_mul_of_nonneg_left _ (DenseMixedKernels.word_positive _).le
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hz (Finset.prod_nonneg fun i _ => hp i))
  exact (Mileage.pay H B.order W.q hT (h.earns i).1 (h.earns i).2.1 ht₀).trans
    (Mileage.receipt H B.order W.q W.degree _ _ W.pos)

theorem Workable.use (D : Stamp H C Z x) {inv s : Support m}
    (h : Workable D B s inv g) (hp : (collect Z.flags (catalog x)).Nonempty)
    (hκ : Real.exp (-Z.plain.ep) ≤ κ) (hw : 0<g) {U : Config G m} (hy : s ∩ RG.flags B.threshold U=inv)
    (W : Oars) (M : ℕ) :
    (∀ i, Integrable ((D i).pre g U) (((D i).model.base U).ante (D i).model.fare)) ∧
    ‖C.pour (fun i => (D i).value g) U‖ ≤ κ * Merger.paid (W.price H Z M B.B B.order e) (catalog x) := by
  have hb (i : I) := (D i).hard g U ht he hl hw (fun i => Z.pays (x.2 i)) (h.earns i U hy).2 (h.earns i U hy).1
  let T := W.mileage Z M B.B x
  have hk : 0≤κ := (Real.exp_pos _).le.trans hκ
  refine ⟨fun i => (hb i).1,C.norm_le (fun i => (D i).value g) U _ (fun i => (hb i).2.trans ?_)⟩
  have ht₀ : (Fintype.card x.Index:ℝ)≤ T := Mileage.enough_length x W.degree W.sends _ (Z.greater ht M B.B) W.pos
  have hT : 1 ≤ T := (Nat.one_le_cast.mpr Fintype.card_pos).trans ht₀
  let M₀ := (∏ i,metric Z.owner e (x.2 i))
  let E := ∏ i,Z.down (x.2 i)
  let P := ∏ i,Z.cash (x.2 i)
  have hM₀ : 0≤M₀ := Finset.prod_nonneg fun i _ => by cases x.2 i <;> first | exact he.pos _ | exact zero_le_one
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => (Z.pays _).trans (Z.down_le _)
  let f := Mileage.license B.order W.q H
  let X := Mileage.orderPrice B.order W.q
  have hh : E ≤ κ*P := Z.discount hp hκ
  change oneWord x*(M₀*E*3) ≤ κ*_ ; rw [W.income,mul_left_comm κ]
  apply mul_le_mul_of_nonneg_left _ (DenseMixedKernels.word_positive _).le
  let t := ∏ i,Mileage.shift H B.order W.q W.degree (Z.scale M B.B (x.2 i)) W.amp
  have hf : 3≤f := Mileage.license_pad ..
  have H : 3≤t := le_trans (b:=f*T^X) (hf.trans (le_mul_of_one_le_right (by linarith : 0≤f) (one_le_pow₀ hT)))
    (Mileage.receipt _ _ _ _ _ _ W.pos)
  change _ ≤ κ*(M₀*P*t)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hh hM₀) H (by norm_num) (mul_nonneg hM₀ (mul_nonneg hk hP))).trans_eq
    (by ring)
end YM.Further.DenseMixedKernels
