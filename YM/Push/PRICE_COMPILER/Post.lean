import YM.Push.PRICE_COMPILER.LoopGate
import YM.Push.PRICE_COMPILER.Pre
import YM.Push.PRICE_COMPILER.Scene


/-!
# Post-L cost compiler (for the indicated local uses)

Works for *every* Rolls meeting the authorized floor. First get grant w
and β-asks from pre proof, and θ-independent stationary requests that
need the actual L. Next can set cost numbers and bound θ, after all these
and any other valid fixed-L asks. Then buy Delays: for any larger Delays
with this T we still earn the indicated receipts. `betaEntry` includes
the first plateau; don't try to always pay there via `s_m` since s₀=0!
`scaleEntry` on the other hand may depend on the later Bar value (and
works on all higher plateaus). First β waits, unlike `W₀`, depend on θ.

Quantification over W lower bounds & larger waits allows rechecking these
receipts when incorporating *other* lawful costs.

No changing represented configurations to lower a cost.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG RG.Supply Wilson Precision Pressure Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators

section Ordering
variable {G : Gauge} {p : Sheet G} {D : Rolls p} {T : Protection D}

/-- Increase Delays componentwise. -/
structure DelayLe (V W : Delays T) : Prop where
  beta : V.betaEntry ≤ W.betaEntry
  scale : V.scaleEntry ≤ W.scaleEntry
  shells : V.shells ≤ W.shells
  growth : V.growth ≤ W.growth

lemma DelayLe.refl (W : Delays T) : DelayLe W W := ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩
lemma DelayLe.trans {U V W : Delays T} (h : DelayLe U V) (h' : DelayLe V W) : DelayLe U W :=
  ⟨le_trans h.beta h'.beta, le_trans h.scale h'.scale, le_trans h.shells h'.shells, le_trans h.growth h'.growth⟩
lemma DelayLe.prices {U V : Delays T} (h : DelayLe U V) (he : Stock.Priced U) : Stock.Priced V :=
  ⟨fun j hj x hx => he.1 j hj x ((h.beta j).trans hx),
   fun j hj γ s hs hg => he.2 j hj γ s hs ((h.scale j γ).trans hg)⟩

/-- Monotone **in stage**, even at the fictitious stages. Can budget these
strongly. -/
structure OrderedDelays (W : Delays T) : Prop where
  beta : Monotone W.betaEntry
  positive j : 0 < W.betaEntry j
  scale γ : Monotone (fun i => W.scaleEntry i γ)
  shells : Monotone W.shells
  growth : Monotone W.growth

def envelopeDelay (W : Delays T) : Delays T :=
  ⟨payHi W.betaEntry, fun i γ => payHi (fun j => W.scaleEntry j γ) i,
    prefixHi W.shells, prefixHi W.growth⟩
lemma envelope_orders (W : Delays T) : DelayLe W (envelopeDelay W) ∧ OrderedDelays (envelopeDelay W) :=
  ⟨⟨le_payHi _,fun _ y => le_payHi (fun j => W.scaleEntry j y) _,fun _ => le_prefixHi _ le_rfl, fun _ => le_prefixHi _ le_rfl⟩,
    payHi_mono _,payHi_pos _, fun _ => payHi_mono _, prefixHi_mono _, prefixHi_mono _⟩

/-- Combine with other (fixed-θ) requests. -/
def joinDelay (W V : Delays T) : Delays T :=
  ⟨fun i => max (W.betaEntry i) (V.betaEntry i), fun i γ => max (W.scaleEntry i γ) (V.scaleEntry i γ),
   fun i => max (W.shells i) (V.shells i), fun i => max (W.growth i) (V.growth i)⟩
lemma joinDelay_above (W V : Delays T) : DelayLe W (joinDelay W V) ∧ DelayLe V (joinDelay W V) :=
  ⟨⟨fun _ => le_max_left ..,fun _ _ => le_max_left ..,fun _ => le_max_left ..,fun _ => le_max_left ..⟩,
    ⟨fun _ => le_max_right ..,fun _ _ => le_max_right ..,fun _ => le_max_right ..,fun _ => le_max_right ..⟩⟩

/-- Priming. For `β`: price starts even for level 0. For `s`: oneself may
require only at higher stages or conditional on being there. The bar value is
an *argument* of the latter schedule. No dependence on period/n unknowns. -/
theorem delay_extra (V : Delays T) (F : ℕ → ℝ → Prop) (f : ℕ → ℝ → ℝ → Prop)
    (hp : ∀ j, ∀ᶠ x in atTop, F j x) (hq : ∀ j γ, ∀ᶠ s in atTop, f j γ s) :
    ∃ W : Delays T, DelayLe V W ∧ OrderedDelays W ∧
    ∀ U : Delays T, DelayLe W U → (∀ j x, U.betaEntry j ≤ x → F j x) ∧
      (∀ j γ s, U.scaleEntry j γ ≤ s → f j γ s) := by
  obtain ⟨B,-,hB,hF⟩ := collect_upper V.betaEntry F hp
  have hr γ := collect_upper (fun j => V.scaleEntry j γ) (fun j s => f j γ s) (fun j => hq j γ)
  choose R _ hr hf using hr
  let W : Delays T := { V with betaEntry := B, scaleEntry := fun j γ => R γ j }
  have hw : DelayLe V W := ⟨hB,fun _ γ => hr γ _,le_rfl,le_rfl⟩
  obtain ⟨hm,hO⟩ := envelope_orders W
  exact ⟨envelopeDelay W,hw.trans hm,hO,fun _ H => ⟨fun j x hx => hF j x
    (((hm.trans H).beta j).trans hx), fun j γ s hs => hf γ j s (((hm.trans H).scale j γ).trans hs)⟩⟩
end Ordering

section Purchasing
variable {G : Gauge} {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}

/-- Can buy *before* choosing θ. Finite-cost schema, nothing else priced. -/
structure Preparations (P : Before) (D : Rolls (P.sheet G f)) where
  w : ℕ → ℕ → ℝ -- w for each pressure query
  rate : ℕ → ℝ -- earned then at the following entrance
  entrance : ℕ → ℝ
  charges : Charges (P.frozen G) D w entrance rate
  gap : ℕ → ℝ
  scenes : SceneRate (P.sheet G f) D (P.frozen G) gap

/-- Compatible post-L choices after any qualifying Rolls. Both parts can
also be purchased separately if there are other costs to thread. -/
theorem preparations (hP : Before.Funded P G f) (D : Rolls (P.sheet G f)) (v : ℕ → ℕ → ℝ)
    (e : ℕ → ℝ) (he : ∀ i, 0 < e i) : ∃ Q : Preparations P D, v ≤ Q.w ∧ Q.gap ≤ e := by
  obtain ⟨w,E,μ,A,h,hv,-, -⟩ := charges_extra (fun _ _ x => (hP.qualify D x).2) v
  obtain ⟨g,hg,H⟩ := gap_prices _ D (P.frozen G) e he
  exact ⟨⟨w,μ,E,h,g,H⟩,hv,hg⟩

namespace Preparations
variable (m : Preparations P D)

def budget (q : AfterBill) : PostCost D := q.post D m.gap m.scenes.pos

/-- Example phase: theta can be chosen *after* these budgets, even when
its bound uses them; arbitrary positive upper requests. Can shrink it
further **before** pricing the β-chassis. -/
theorem withTheta (q : AfterBill) (u : PostCost D → ℕ → ℝ)
    (h : ∀ i, 0 < u (m.budget q) i) : ∃ T : Protection D, T.theta ≤ u (m.budget q) :=
  Protection.exists_margin D (u (m.budget q)) h

/-- These grants are interpretation predicates, so robust to increasing
Delays. Remark: taking a *smaller* θ before defining such a Ledger is
possible; not asserting that criteria of an old Ledger still hold! Re-pay
for instance the loop seed-purchase condition. -/
structure Ledger {T : Protection D} (W : Delays T) : Prop where
  priced : Stock.Priced W
  entry : m.entrance ≤ W.betaEntry
  orders : stencilNeed G P.orders ≤ W.shells
  macroFits : macroNeed D ≤ W.shells
  loops j x : W.betaEntry j ≤ x → ∀ i, StepStages j i → Grows P.slopePrices T j i x

variable {m}


variable (m)
/-- Even with ANY additional demands in V, after-L and after-θ. -/
theorem ledger_exists (hG : G.Simple) (T : Protection D) (V : Delays T) :
    ∃ W : Delays T, OrderedDelays W ∧ DelayLe V W ∧ ∀ U : Delays T, DelayLe W U → Ledger m U := by
  obtain ⟨F,-,he,hF⟩ := can_delay_loop P.slopePrices T m.entrance
  let R : Delays T :=
    { V with betaEntry := F, shells := fun i => max (stencilNeed G P.orders i) (macroNeed D i) }
  let Z := joinDelay V R
  obtain ⟨Y,hb,hc,hd,h₁,h₂⟩ := Stock.raises Z hG
  have hh : DelayLe Z Y := ⟨hb,hc,hd.le,h₁.le⟩
  let W := envelopeDelay Y
  obtain ⟨hw,hy⟩ := envelope_orders Y
  refine ⟨W,hy, (joinDelay_above V R).1.trans (hh.trans hw), fun U hU => ?_⟩
  have h : DelayLe Y U := hw.trans hU
  have hx : DelayLe R U := (joinDelay_above V R).2.trans (hh.trans h)
  exact ⟨h.prices h₂,le_trans he hx.beta,
    fun i => (le_max_left ..).trans (hx.shells i), fun i => (le_max_right ..).trans (hx.shells i),
    fun j x hu => hF j x ((hx.beta j).trans hu)⟩
end Preparations
end Purchasing

section Runs
variable {G : Gauge} {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W}

/-- After fixing post-L Delays still accommodate more compatible stretching
requests. Note use of *function in s* with a growth condition (per j, no
uniformity in j) -- not imposing a circular requirement on absolute starts.
We merely combine requests of allowed shape; proving a physical weak-scale
stretch/request has that shape is not implied. -/
structure WaitLe (a b : Wait Y) : Prop where
  ready : a.readyHere ≤ b.readyHere
  window : a.window ≤ b.window
  length : a.minLength ≤ b.minLength

def joinWait (a b : Wait Y) : Wait Y where
  readyHere j := max (a.readyHere j) (b.readyHere j)
  window j s := a.window j s + b.window j s
  sublin j := by
    simp only [Nat.cast_add, add_div]
    simpa only [add_zero] using (a.sublin j).add (b.sublin j)
  minLength := max a.minLength b.minLength



/-- Simple cushion also proves nonemptiness of arbitrary constant-window &
arbitrary per-stage scale asks and global minLength. -/
def cushion (Y : Bar W) (f : ℕ → ℝ) (w : ℕ → ℕ) (x : ℕ) : Wait Y where
  readyHere := f
  window j _ := w j
  sublin _ := tendsto_const_nhds.div_atTop (tendsto_id (x:=(atTop : Filter ℝ)))
  minLength := x


end Runs
end YM.Push.PriceCompiler
