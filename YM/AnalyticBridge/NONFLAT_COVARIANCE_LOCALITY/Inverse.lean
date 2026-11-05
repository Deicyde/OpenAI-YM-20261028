import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Bundle
import YM.Push.FREE_RESOLVENT.JetWindows


/-!
# Common income for all inverse jets

Connecting the sector's precision hypotheses to `Push.FREE_RESOLVENT`
for a table (also for its identity completion). All continuity is on the
specified real germ; weighted bounds for each Taylor occurrence list.
Use *positive* `s,Y` with BoardPrices; we don't expect even uniform
unshifted-inverse bounds without a positive gap.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Matrix Function Filter Metric Set
open Lattice RG Wilson Pressure Tree
open Next.SectorChange 
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c : Side} {α : Type} [Fintype α]

/-- Whole kernel derivatives with exponential pricing. Factor `drain u`
is `(1+u)⁻¹`. For an inverse expect `1+u` only for zeroth and the square
for positive orders. Here `C` not shift-dependent in uses. Applies even on
finite windows explicitly varying by column. -/
structure PolePrices (u : ℝ) (a : α → Site c) (F : Coord G c → Matrix α α ℝ) (n : ℕ)
    (s C : ℝ) (z : Coord G c) : Prop where
  smooth : ContDiffAt ℝ n F z
  entry (l : List (Index G c)) : l.length ≤ n → Bill (locations G c s) (native c) a a l s
    (charges l.length 1 C (drain u)) (jet (direction G c) F l z)

variable {p : α → Site c} {n : ℕ} {s C t M η L V θ u : ℝ} {A : Coord G c → Matrix α α ℝ}
    {x : Coord G c}




lemma price_steps (P : TestD.Price s M η t 1 V 1 n) :
    0<t ∧ t ≤ 3*(n+1:ℕ)*t ∧ 3*(n+1:ℕ)*t ≤ 4*(n+1:ℕ)*t ∧ 4*(n+1:ℕ)*t ≤ s := by
  have hp := P.pos
  refine ⟨hp,?_,?_,P.roomEnough.trans P.roomTop⟩ <;>
    push_cast <;> nlinarith [mul_nonneg hp.le (show 0 ≤ (n:ℝ) by positivity)]
lemma price_shrink (P : TestD.Price s M η t 1 V 1 n) : t ≤ s := by
  obtain ⟨-,ha,hb,hc⟩ := price_steps P; exact ha.trans (hb.trans hc)

lemma purchase (h : Tagged p p n s M A x) (he : FreeResolvent.Gap (A x) η) (ht : t ≤ s) :
    Knew (locations G c t) (native c) p (direction G c) x n s M η 1 A :=
  ⟨h.smooth,he,Tagged.order_zero h,fun l _ hv =>
    (marks_budget (h.bound l hv) ht).mono le_rfl (by rw [mul_one])⟩

def inverseFare (n : ℕ) (M η V : ℝ) := meter n n M 1 (rise V η)






structure BoardPrices (p : α → Site c) (F : Coord G c → Matrix α α ℝ) (n : ℕ)
    (s C Y : ℝ) (x : Coord G c) : Prop where
  form : (F x).IsSymm
  floor : FreeResolvent.Gap (F x) Y
  paid : Tagged p p n s C F x
  inverse : ∀ (u : ℝ), 0 ≤ u → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → α),
    Function.Injective e → PolePrices u (p ∘ e) (action (limitTo F e) u) n s C x

namespace BoardPrices




lemma cap (h : BoardPrices p A n s M η x) (hσ : 0 ≤ s) (i : α → ℝ) :
    η*dotProduct i i ≤ dotProduct i (A x *ᵥ i) ∧ dotProduct i (A x *ᵥ i) ≤ M*dotProduct i i :=
  ⟨h.floor.lower i, le_of_abs_le (schur_qf _ _ ((Tagged.order_zero h.paid).mono hσ le_rfl) i)⟩



end BoardPrices





end YM.AnalyticBridge.NonflatCovarianceLocality
