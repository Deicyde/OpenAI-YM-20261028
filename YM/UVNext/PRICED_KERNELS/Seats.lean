import YM.Next.SCHEDULE.Pre
import YM.UVNext.PRICED_KERNELS.Addresses
import YM.UVNext.PRICED_KERNELS.Order



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Enough Before asks for each paths-of-ℓ choice `Ways`

Commutes with `issue` on the stated earns. Includes all finite moments i.e. does not
require consuming a width on each consecutive use of a Horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure Laurent Exterior Bloch
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

/-- Finite rates for the layout on each smoothing stage. If using several types downstream
can also take common prices before L. Pay any
finite required order from the actual Stage. No taking sup of all exponents into a single
price. For these results on ell, no estimate outside the accepted (repaired) strip needed. -/
structure LayoutPrices where
  stride : ℕ → ℝ
  base : ℕ → ℝ
  mass : ℕ → ℝ
  stride_nn i : 0 ≤ stride i
  base_nn i : 0 ≤ base i
  mass_pos i : 0 < mass i

/-- Buy for both sides of an RG edge OFFERING double the needed length width.
  Cost amount can be booked at width ≤ 1 of the final Openings.active (price
  for 2). Thus neither Opening choices nor Moment order need to feed back into
  this part of Amount (nonlinear arrays must produce the separate moment cost
  they may need against their own recurrence). -/
def LayoutPrices.fee (g : LayoutPrices) (K : MapPrices) (i : ℕ) :=
    wayPrice 2 (g.base i) (g.mass i) (K.Ω i)

-- Sufficient pre-L quote
structure Covers (K : MapPrices) (P : Before) (g : LayoutPrices) : Prop where
  width i : P.opening.wish i * g.stride i ≤ K.α i
  top i : g.fee K i ≤ P.amount.born i
  steps i j : StepStages j i → g.fee K i ≤ P.amount.sends j i

namespace LayoutPrices
variable (g : LayoutPrices)

def requests (R : Charges) : Charges :=
    { R with
      wants := fun c f K =>
        let w := R.wants c f K
        let hi := fun i => K.α i / (g.stride i+1)
        { w with wish := fun i => min (w.wish i) (hi i),
                 wp := fun i => lt_min (w.wp i) (div_pos (K.alpha_pos _) (by have := g.stride_nn i; linarith)) }
      asks := fun c f K w =>
        let t := R.asks c f K w
        { t with born := fun i => max (t.born i) (g.fee K i)
                 sends := fun j i => max (t.sends j i) (g.fee K i)
                 born_pos := fun _ => (t.born_pos _).trans_le (le_max_left ..)
                 sends_pos := fun _ _ => (t.sends_pos ..).trans_le (le_max_left ..) } }

lemma covered (R : Charges) (p : Before) (Q : FlatBill) (c : ℕ → Clip) :
    let P := issue G p Q c (g.requests R)
    Covers (P.frozen G) P g := by
  intro P
  obtain ⟨-,hh,ht,hs⟩ := linear_paths G p Q c (g.requests R)
  constructor
  · intro i; have hv := (hh i).trans (min_le_right ..)
    have hc : 0 < g.stride i+1 := by linarith [g.stride_nn i]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) (P.opening.wp i).le).trans
      ((le_div_iff₀ hc).mp hv)
  · intro i; exact (le_max_right ..).trans (ht i)
  intro i j _; exact (le_max_right ..).trans (hs j i)

end LayoutPrices

section Paid
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G} {V : Horizon a}

def receipt (Q : PathData G) (σ A : ℝ) := ∀ b, SumBudget (fun i => |(Q.row b i).1| * Real.exp (σ * (Q.row b i).2.length)) A

lemma receipt_le {σ τ A C : ℝ} {Q : PathData G} (h : receipt Q τ A) (he : σ ≤ τ) (ha : A ≤ C) :
    receipt Q σ C := fun b => sumBudget_mono (h b) (fun _ => by positivity) (fun _ => by gcongr) ha



structure Billed (P : Before) (a : Levels G) (V : Horizon a) (N m : ℕ) (Q : PathData G) : Prop where
  placed : Attached (V.H N m) Q
  metric : Q.metric_zero (a.params m).clip
  top : let i := a.clock.J m; receipt Q (2 * (a.params m).width) (P.amount.born i)
  edge j : let i := a.clock.J m; StepStages j i → receipt Q (2 * (a.params m).width) (P.amount.sends j i)







/-- Canonical special-spelling version (e.g. if using earlier generator API).
  Need only Canonical.Quotes, not Ways. -/
theorem charge_canonical (h : Permit M I a) (hV : V.Suffices (P.frozen G)) (hg : Canonical.Quotes (P.frozen G) P.opening P.amount)
    (N m : ℕ) (hm : m ≤ N) (Q : PathData G) (hQ : Q.row = Canonical.row (V.H N m)) :
    Billed P a V N m Q := by
  let i := a.clock.J m; let K := P.frozen G; let t := P.opening; let σ := (a.params m).width
  have hw : 2*σ ≤ K.α i := by unfold σ; rw [params_eq h.paid]; exact (t.wish_ge i).trans (hg.fit i)
  have hR := (hV.rows N m hm).2.2.2.1
  have hx : receipt Q (K.α i) (Canonical.fee (K.α i) (K.Ω i)) := fun b => by
    rw [hQ]; exact Canonical.cost _ hR _
  exact ⟨Canonical.attached Q hQ,Canonical.weights hR (K.alpha_pos i).le (hV.all N m hm 1) hQ,
    receipt_le hx hw (hg.top i),fun j h => receipt_le hx hw (hg.send i j h)⟩
end Paid
end YM.UVNext.PricedKernels
