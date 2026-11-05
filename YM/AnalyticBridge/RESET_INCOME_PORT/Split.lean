import YM.AnalyticBridge.RESET_INCOME_PORT.Quote
import YM.Next.UV_STRESS.Across
import YM.Next.UV_STRESS.Fringe
import YM.Push.COMMON_WITNESSES.Link
import YM.UVNext.COUPLING_RESET.Sectors


set_option warningAsError false

/-!
# Split currency for Reset (at the two actually used probes)

Turn a menu of **local tests per matched Store and choice** in the exact
Gaussian formula into the exact extensive/charge currency of Split. No
curve regularity assumptions needed for this service. Keep the forecast of
the scalar `v` ENTIRELY common between the two probes, not cancelling two
independent price estimates as if they were log prices in the same units!
One Teller/Funds/Ringing buys across the bands where here used. See Journal
for producing Prereset on a further regime (the `Split` accuracy needn't
produce the localized E's or the exact identity required there).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {e : Plate G S} {V : Config G c} {R : Rep G f} {κ u δ : ℝ}

/-- Select the head before invoking the pricing adapter. Potentially all
Stores. Keep the tail pricing positive and in the same currency. -/
structure Menu (e : Plate G S) where
  chosen : Finset (Stores S)
  core : ∀ A : Stores S, S.Choices → Coupon e A
  tail : ∀ A : Stores S, S.Choices → Tariff e A

namespace Menu

def columns (e : Plate G S) (V : Config G c) (p : Stores S → S.Choices → ℝ) (J : Finset (Stores S)) :=
  ∑ A ∈ J, ∑ k, if e.matched A V then p A k else 0

/-- Arithmetic EXACTLY in Split forecast units: after explicit log and
reference prices, sums must already fit the output window at δ. Mismatches
require no price. -/
structure Cash (m : Menu e) (V : Config G c) (δ : ℝ) : Prop where
  lower : Real.exp (-δ/2) ≤ columns e V (fun A k => (m.core A k).down) m.chosen
  upper : columns e V (fun A k => (m.core A k).up) m.chosen ≤ Real.exp (δ/2)
  limit : columns e V (fun A k => (m.tail A k).ceiling) (Finset.univ \ m.chosen) ≤ Real.exp (-δ/2)*(1-Real.exp (-δ/2))

structure Paid (m : Menu e) (R : Rep G f) (V : Config G c) (u δ κ : ℝ) : Prop where
  main A : A∈m.chosen → e.matched A V → ∀ k, (m.core A k).Uses R V k u
  rest A : A∈Finset.univ\m.chosen → e.matched A V → ∀ k, (m.tail A k).Paid R V k u κ
  cash : m.Cash V δ

lemma into (m : Menu e) (h : m.Paid R V u δ κ) (he : e.Receipt R) :
    let r := Real.exp (e.outside R V-u)
    r*e.head R V m.chosen ∈ Icc (Real.exp (-δ/2)) (Real.exp (δ/2)) := by
  intro r
  let l A k := if e.matched A V then (m.core A k).down else 0
  let g A k := if e.matched A V then (m.core A k).up else 0
  have hv A k (hy : A∈m.chosen) : r*e.value R A V k∈Icc (l A k) (g A k) := by
    by_cases hx : e.matched A V
    · unfold l g; simp only [if_pos hx]; exact (h.main _ hy hx k).cashed he hx
    simp [Plate.value, l,g,hx]
  unfold Plate.head; simp_rw [Finset.mul_sum]
  refine ⟨h.cash.lower.trans ?_,le_trans ?_ h.cash.upper⟩
  · exact Finset.sum_le_sum fun A hh => Finset.sum_le_sum fun k hk => (hv A k hh).1
  exact Finset.sum_le_sum fun A hh => Finset.sum_le_sum fun k hk => (hv A k hh).2

lemma out (m : Menu e) (h : m.Paid R V u δ κ) (he : e.Receipt R) {P : Teller G} (ht : P.Funds S e.tube) :
    let r := Real.exp (e.outside R V-u)
    let W := Finset.univ \ m.chosen
    r*(∑ A ∈ W, ∑ k, e.expense R A V k κ) ≤ Real.exp (-δ/2)*(1-Real.exp (-δ/2)) := by
  intro r W
  have hv A k (hy : A∈W) : r*e.expense R A V k κ ≤ if e.matched A V then (m.tail A k).ceiling else 0 := by
    by_cases hx : e.matched A V
    · rw [if_pos hx]; exact (h.rest _ hy hx k).cashes he hx ht
    simp [Plate.expense,hx]
  simp_rw [Finset.mul_sum]; exact (Finset.sum_le_sum fun A hh => Finset.sum_le_sum fun k _ => hv A k hh).trans h.cash.limit

lemma cash_core (m : Menu e) (h : m.Paid R V u δ κ) (he : e.Receipt R) :
    (∑ A∈m.chosen, cutEntry e.book e.forest e.tube R A V) ∈ Icc (Real.exp (u-δ/2)) (Real.exp (u+δ/2)) := by
  rw [Plate.cut_sum he]
  have hh := m.into h he; let r := Real.exp (e.outside R V-u)
  have ht : Real.exp (e.outside R V) = Real.exp u * r := by unfold r; rw [← Real.exp_add]; ring_nf
  rw [ht,mul_assoc,show u-δ/2=u+ -δ/2 by ring,Real.exp_add,Real.exp_add]
  exact ⟨mul_le_mul_of_nonneg_left hh.1 (Real.exp_pos _).le,mul_le_mul_of_nonneg_left hh.2 (Real.exp_pos _).le⟩

lemma split (m : Menu e) (h : m.Paid R V u δ κ) (he : e.Receipt R) {σ a Λ g v : ℝ} (hh : R.Lawful σ a Λ g v)
    {P : Teller G} (ht : P.Funds S e.tube) : Split e.book e.forest e.tube κ R V u δ := by
  refine ⟨m.chosen,m.cash_core h he,?_⟩
  simp_rw [Plate.earn_eq he ht hh _ V, ← Finset.mul_sum]
  have hf := m.out h he ht
  let r := Real.exp (e.outside R V-u)
  have hr : Real.exp (e.outside R V) = Real.exp u*r := by unfold r; rw [←Real.exp_add]; ring_nf
  rw [hr,mul_assoc,show u-δ/2=u+-δ/2 by ring,Real.exp_add,mul_assoc]
  exact mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
end Menu

/- Prediction in negative log units, WITHOUT any as-yet undetermined
normalization. -/
section
variable {b : Sheet G} {D : Rolls b} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)

def demand (N : ℕ) {m p : ℕ} (R : Rep G (B.a.S.side (m+1) p)) (V : Config G (B.a.S.side m p)) :=
  let S := B.kin.path N m
  let T := (B.a.params m).clip
  R.beta * mainTerm T S V + B.kin.alpha N m * secondTerm T S V + loop S V

variable {g a E : ℕ → ℕ → ℝ} {N m p : ℕ}






end
end YM.AnalyticBridge.ResetIncome
