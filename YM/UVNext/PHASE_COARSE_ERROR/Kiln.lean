import YM.Next.BOUNDARY.Unique
import YM.Next.FLUCTUATIONS.Bare
import YM.Next.UV_STRESS.Union
import YM.UVNext.PHASE_COARSE_ERROR.Cylinder
import YM.UVNext.PHASE_COARSE_ERROR.Freight
import YM.UVNext.PHASE_COARSE_ERROR.Marginal



set_option warningAsError false

/-!
Finite step, fixed k and stop and Form and Wallet constants before any
of the integrations. ALL h copies in the actual torus along actual
ancestry; all subsets from birth through every remaining step. Frontier
may run on the realized Directed recipe/Ringing from SectorMeasure.Consumer;
we hold its prescribed tags/β etc, don't try to infer the quotes from the
point/cut grants alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PhaseCoarse
open Function Set Filter MeasureTheory Analysis Extraction Lattice Wilson RG Overlay Marker Next.UVStress Mix Push.SectorMeasure Cells
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) {d h k p N m u r ℓ : ℕ}

abbrev Batch (h p : ℕ) := Site (C.side h p)
abbrev Vessel (N p h u : ℕ) := Bands (trays C h p) (C.path.rep N p u)
def serve (Y : Vessel C N p h u) (s : (trays C h p).Mode) (V : Config G (C.side u p)) := (Y.density V).part s

/-- Numerical and separation prerequisites. **Pay before instantiating
OneTransfer**. Mixed input at the actual lenses exponent/order; not allowed
to requisition stronger than recurrence will deliver. Not a schedule lemma
that those recurrence-compatible one-step estimates can be anticipated. -/
structure Charges (N p h k ℓ d : ℕ) where
  initi : h≤ℓ
  stays : ℓ≤k
  admits : k≤N
  bank : Bid.Worth
  solvent : Bid.Bank bank C.path.levels
  room : Bid.roomCost C.path.levels bank
  -- separation. Same throughout all queries. No assumption far at the h level itself.
  space i : ℓ ≤ i → i ≤ k → ∀ a b : Batch C h p,a≠b →
    8 ≤ (C.path.rep N p i).p.B ∧ (C.path.rep N p i).p.B*(C.path.rep N p i).p.B ≤
      separation (camp C p h i a) (camp C p h i b)
  fit i : ℓ≤ i → i ≤ k → stencil_at C i d
  -- paired duet may be driven farther, to r before ℓ
  base : ℕ
  matched : base ≤ ℓ
  cost : ℝ
  loan : 0 ≤ cost
  cap : ℕ → ℝ -- ordinary radius W
  rate : ℕ → ℝ -- provisional rate on output of step i+1→i *after* bump
  exponent : ℕ → ℝ -- extra support exponent at this rate, not at cap
  profit : ℕ → ℝ
  loss : ℕ → ℝ
  positive i : 0 < cap i
  one : ℕ → ℝ -- units & isolated kitchens
  many : ℕ → ℝ
  terms i : one i ≤ 1 ∧ many i ≤ 1 ∧ 0 < one i ∧ 0 < many i
  invoices i : ℓ≤ i → i ≤ k →
    cap i*gainRead C k i cost ≤ one i ∧
      cap i*slope_fee (lenses C i)*(1+stencil_fee C i)*gainRead C k i cost ≤ one i ∧
      cap i*Real.sqrt (C.path.levels.clock.forcedAllowance i)*gainRead C k i cost ≤ one i
  regenerates i : ℓ ≤ i → i < k → 0 < rate i ∧ 0 ≤ exponent i ∧ 1 ≤ profit i ∧ 0 ≤ loss i ∧
    profit i*cap i ≤ rate i*Real.exp (exponent i*(C.path.rep N p i).p.B/64) ∧
    cutRate (one (i+1)) (many (i+1)) (loss i) (profit i) ≤ many i

namespace Charges
variable (M : Charges C N p h k ℓ d)

abbrev Accord := Batch C h p → Bid.Duet C.path (C.labels.level d) N p M.base k

/-- Tie supplies to the actual density and origins. The optional `memo`
lets estimates ask further proof-book predicates about the actual
representation/process; must obtain and propagate these too (including
at signed birth). -/
structure Form (Z : M.Accord C) (i : ℕ)
    (memo : (i : ℕ) → Vessel C N p h i → Prop) (Y : Vessel C N p h i) : Prop where
  active : Y.Active
  fidelity : memo i Y
  itinerary j : Y.origins j = camp C p h i j
  letters j : Nonempty (GridPattern C (Z j) Y j)
  singleton j : serve C Y ((trays C h p).fire j) =
    ((Z j).voice i).density ((Z j).atPoint i) (C.localSection d) (C.path.rep N p i)



def Wages (i : ℕ) (Y : Vessel C N p h i) (T : Stubs Y) := (∀ j,M.cap i * ‖Y.units j‖ ≤ M.one i) ∧
    T.funded (fun _ => M.cap i) 0 false (M.one i) ∧ T.funded (fun _ => M.cap i) 0 true (M.many i)





def Watched (Y : Vessel C N p h m) := ∀ s : (trays C h p).Mode,GaugeInvariant (serve C Y s)
end Charges

open Charges
variable (M : Charges C N p h k ℓ d)

/-- To compute/check the actual next signed density with sector work: all
sectors measured, using unchanged tag weights, THAT beta, certified
Allocation (could use hard/alive cells), probability Haar in & out,
centered h copies, every subset. No assertion `Funds` pays the
Post charges of this receipt.

A relation to verify at just one step. Provides the **same** representation
for the equality and the costs (incl preserving singleton calibration and
addressing). -/
structure OneTransfer (Z : M.Accord C) (memo : ∀ i, Vessel C N p h i → Prop) (m : ℕ)
    (X : Vessel C N p h (m+1)) (T : Stubs X) where
  height : ℝ
  threshold : ℝ
  forest : Tree.Forest (operation C p m).ratio
  billed : Allocation G (operation C p m) height threshold
  result : Vessel C N p h m
  signed : ∀ s V, serve C result s V=Ride.bump (C.S.block m).val s (fun _ => d) *
    ∑ A, output billed forest (C.path.β N p (m+1)) (serve C X s) A V
  keep : M.Form C Z m memo result
  stubs : Stubs result
  finances : Customs T stubs (M.cap (m+1)) (M.rate m) (M.exponent m) (M.loss m)

/-- The MIXED transfer input.

Note actual lens on each input (regular
grain at full `.order`, loaf at trajectory `.supportExponent`, true support
`coverNumber` etc) and only ordinary weights there.

A producer of the output
inequality will have to budget all cross-marker and reassembly effects and
any angle/width/exponent strengthening it uses.

In particular the `regenerates` number inequality about output
costs is no solution to this issue. -/
def Front (Z : M.Accord C) (memo : (i : ℕ) → Vessel C N p h i → Prop) : Prop :=
    ∀ m : ℕ, ℓ≤m → m<k → ∀ X : Vessel C N p h (m+1), M.Form C Z (m+1) memo X → Watched C X →
      ∀ T : Stubs X, M.Wages C (m+1) X T → Nonempty (OneTransfer C M Z memo m X T)









/-- Remaining finite price question (per admitted N,p). It asks for actual
matched Duets in C, including terminal coordinate cancellation at `.base`,
and **exact signed join at k**, plus a raw mixed birth bound there. Then
per-step Front, e.g. from a recursive assumption quantified before the
configuration/weights, not assuming future Radial at stop. The earlier
signal to join against needn't come with Stubs or even Active at all; can
compare against our literal sector integral prescription via signal_columns
and only re-describe at k (or generate its representation & then merge
markers as E proposes; will need budgets for that strategy). Note *strict
real*, physical normalization and transport of the same dye into every
copy in this request (no frozen mismatched branches). -/
structure Pantry (v : Stones C d) (z : C.label d)
    (memo : (i : ℕ) → Vessel C N p h i → Prop) : Prop where
  real_dye : star z=z
  offers : ∃ Z : M.Accord C, (∀ i, Bid.Duet.Woke (Z i) C.params M.bank (C.localSection d) M.cost) ∧
    Front C M Z memo ∧
    ∃ (X : Vessel C N p h k) (T : Stubs X), M.Form C Z k memo X ∧
      (∀ s, serve C X s=blend (fun _ => d) (old ⟨d,piece C d v⟩ (M.initi.trans (M.stays.trans M.admits)))
        s.val (fresh (M.initi.trans M.stays) (paint (dye C k p d z))) M.admits) ∧
      T.funded (fun _ => M.cap k) 0 true (M.many k)




end YM.UVNext.PhaseCoarse
