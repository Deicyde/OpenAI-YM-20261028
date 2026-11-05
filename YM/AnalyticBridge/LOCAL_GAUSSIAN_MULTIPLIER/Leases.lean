import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Clearance


/-!
# Buying participant charges for the Lease

Ordinary optional parents flat price (cap b). Exponential endpoint
optionals earn a square-root price (sqrt b=x), only use with the
stated *one-hit* conditions at **every** participant (or other numerical
upper adding them together at the same θ,Y,V). Includes selected physical
triggers, in their shared coordinates. No pretending there is one suppression
factor per occurrence of the SAME endpoint. Uniform payments NOT historical
claims these rents or ratios have the required incomes in the density engine.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson ProjectorNext.Equivariance Next.SectorChange
  Next.SectorChange.Gaussian Next.SectorChange.Rows YM.Push.SectorMeasure
  YM.Next.Foundations Precision MeasureTheory Metric Curtain Moments Tariff Notice
open scoped Topology BigOperators Matrix.Norms.Frobenius YM.Push.SectorMeasure ContDiff Classical

variable {G : Gauge}

def floorPrice {ι : Type} (S : Finset ι) (z : Vec ι) := 1+load S z
lemma inPrice {ι : Type} (S : Finset ι) (z : Vec ι) : 1 ≤ floorPrice S z := le_add_of_nonneg_right (load_nonneg ..)

/-- A convenient payment plan, linear budget for unmarked optionals,
(square x) budget on ratio letters. In addition to the gradient debts
of the kept ones. Growth radius polynomial flexibly consumes any rank
powers of B p Λ and ancestor costs at this fixed k, including support
anchor payments. Only `leased` when bills verified. -/
structure Install (α β γ I : Type) where
  gate : α → ℝ
  spend : β → ℝ
  body : Finset β
  yen : ℝ
  big : Finset γ
  rate : γ → ℝ
  sit : γ → Finset (I×G.ColorIndex)
  expose : Finset I
  threshold : ℝ -- unit Z thickness on each trigger
  eps : ℝ
  capacity : ℝ -- applies to commuting all, same step
  meter : ℝ
  plan : ℕ

namespace Install
variable {α β γ I : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype I]
    [DecidableEq I] [DecidableEq β] [DecidableEq γ] (t : Install (G:=G) α β γ I)

def markers := t.expose ×ˢ (Finset.univ:Finset G.ColorIndex)

def watch (ι : I × G.ColorIndex) := if ι∈t.markers then t.eps else 0

def warmth (i : γ) := t.rate i + (t.rate i)^2

def hit (i : γ) (j : I × G.ColorIndex) := if i∈t.big ∧ j∈t.sit i then t.warmth i else 0

-- Stake in normalized trigger load; `eps` is on *all* its coordinates.
def rooted := t.eps * (t.expose.card*t.threshold^2)

def rents : Tariff α β γ (I×G.ColorIndex) where
  core := t.body
  value := t.yen
  cost := t.spend
  port := t.gate
  wage i := if i∈t.big then t.rate i*Real.exp (t.warmth i) else t.rate i*Real.exp (t.rate i)
  quota i z := if i∈t.big then (t.rate i)^2 * floorPrice (t.sit i) z else t.rate i
  send := fun _ _ => 0
  wait := fun _ _ => 0
  use := t.hit
  seat := t.markers ∪ t.big.biUnion t.sit
  capacity := t.capacity
  mark := t.watch
  stake := t.rooted
  ray := t.meter
  orderPay := t.plan

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype I] [DecidableEq β] in
lemma seats_count : t.rents.seat.card ≤ t.expose.card*Fintype.card G.ColorIndex + ∑ i∈t.big,(t.sit i).card :=
    (Finset.card_union_le ..).trans (add_le_add (le_of_eq (by simp [markers])) Finset.card_biUnion_le)

/-- Producer for simultaneous use. The taxes can be checked before
the actual occurrence. -/
lemma lease (hv : ∀ i, 0 ≤ t.gate i) (he : ∀ i, 0 ≤ t.rate i) (hC : 0 < t.capacity)
    (h1 : 1 ≤ t.meter) (hK : ∀ i : I × G.ColorIndex,t.watch i + (∑ j : γ,t.hit j i) ≤ t.capacity⁻¹/8)
    (hT : ∀ i, (if i∈t.big then (t.rate i)^2 else t.rate i) ≤ t.meter)
    (hR : 1≤ t.plan) : t.rents.Lease := by
  classical
  refine ⟨hC,fun i _ => ?_,h1,hv,fun j => ?_,fun i z => ?_,fun i z => ?_⟩
  · simpa [rents] using hK i
  · by_cases hy : j∈t.big
    · simp only [rents,if_pos hy]; exact mul_nonneg (he _) (Real.exp_pos _).le
    simp only [rents,if_neg hy]; exact mul_nonneg (he _) (Real.exp_pos _).le
  · unfold rents Tariff.slide; dsimp only
    by_cases hx : i∈t.big
    · simp only [if_pos hx]; have hh : t.sit i ⊆ t.rents.seat := fun j hj => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hx,hj⟩)
      unfold hit; simp_rw [hx,true_and]
      exact t.rents.prepaid _ (he _) _ hh z
    simp only [hit,Tariff.reach,hx,false_and,↓reduceIte,zero_mul,Finset.sum_const_zero,Real.exp_zero,mul_one]
    exact le_of_eq (mul_comm ..)
  let u := floorPrice (t.sit i) z
  have hi : 1 ≤ powers z := grows z
  have hp : u ≤ powers z := add_le_add_right (load_le _ (Finset.subset_univ _)) _
  have hh := hT i
  unfold Tariff.grow rents; dsimp only
  split
  next hx =>
    rw [if_pos hx] at hh
    refine mul_le_mul hh (hp.trans ?_) (zero_le_one.trans (inPrice ..)) (zero_le_one.trans h1)
    simpa only [pow_one] using! pow_le_pow_right₀ hi hR
  next hx => rw [if_neg hx] at hh; exact hh.trans (le_mul_of_one_le_right (zero_le_one.trans h1) (one_le_pow₀ hi))

omit [DecidableEq β] [Fintype α] [Fintype β] [Fintype γ] in
lemma mark_money {z : Prices G I} (h : ∀ i∈t.expose,t.threshold^2 ≤ ‖tape z i‖^2)
    (he : 0 ≤ t.eps) : t.rents.Event z := by
  have hi : t.rents.reach t.watch z=t.eps*load t.markers z := by
    unfold Tariff.reach watch load; rw [Finset.mul_sum, ← Finset.sum_subset (show t.markers ⊆ t.rents.seat from Finset.subset_union_left)
      (f:=fun i => (if i∈t.markers then t.eps else 0)*z i^2) (fun i _ hi => by rw [if_neg hi,zero_mul])]
    exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
  unfold Tariff.Event
  rw [show t.rents.mark = _ from (show t.rents.mark=t.watch from rfl),hi]
  apply mul_le_mul_of_nonneg_left _ he
  simp only [load,markers,Finset.sum_product]
  simp_rw [EuclideanSpace.real_norm_sq_eq,tape_ap] at h
  simpa using Finset.sum_le_sum h
end Install

open Spot
namespace Reading
variable {c f : Side} {S : StepData c f} {d : Desk G S} {u : Spot d}
    {H R K α β γ : Type} [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ]
    {X : Support c} {l : Viewport u X H R K} {a : Notice l} {p : Reel G H R K}
    {b : Finset ℕ} {D : u.Slices} {q : Programme D b} {n : q.Run α β γ} {B : Reading a n}
    {r : Install (G:=G) α β γ (H⊕R)} {V : Config G c} {Ω : Set (Config G c)}

-- Unforced use of witnesses. Note require the extension's CONTINUITY
-- only at V for these triggers; need on Wakes points (can arrange on held
-- domain as above if a.m continuous, or pull back increment approach).
omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] in
lemma signs (h : B.Wakes p V) (hx : Ω∈nhds V) (he : ContinuousAt (fun V => a.imprint V p) V)
    (hs : ∀ i∈r.expose,∃ j : α ⊕ γ, ∀ W∈Ω, B.awakeAtom p j W ≠ 0 → r.threshold^2 ≤ ‖tape (a.imprint W p) i‖^2)
    (hε : 0 ≤ r.eps) : r.rents.Event (a.imprint V p) := by
  apply Install.mark_money _ _ hε
  intro i hi
  obtain ⟨j,hj⟩ := hs i hi
  have hc : Continuous fun z : Prices G (H⊕R) => ‖tape z i‖^2 := by
    have hx : Continuous (tape (G:=G) (ι:=H⊕R)) := gaugeCount.continuous
    fun_prop
  by_contra! hh
  obtain ⟨W,hv,hW,hp⟩ := ((h j).and_eventually ((show ∀ᶠ W in nhds V,W∈Ω from hx).and
    ((hc.continuousAt.comp he).eventually (gt_mem_nhds hh)))).exists
  exact (hj _ hW hv).not_gt hp
end Reading
end YM.AnalyticBridge.LocalGaussian
