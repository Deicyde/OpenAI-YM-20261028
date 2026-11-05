import YM.Next.RANK.Promises
import YM.Next.RANK.Ratchet

/-!
# Concordance of Rank meters

This is an independent prerequisite PLAN. Thermal requests must be earned as
actual estimates below Short and Corrected (calendar tied to C as well).
- Stage cohesion: same charges at each family depth regardless of p,N and
  of the conformation of each frame row.
- Post-L gates: numbers of this plan and Supported(W for each row).
- End wind kernel money (`Vantage` each arity): earlier unmarked/Stationary data
  on this *same* order. In particular bounds on P inputs and cumulative dilation in A units.
- `survivors`: Epoch chosen with the entering exponent and k vacuum readings,
  certified continuation MarketGrant of *that* reworking. existence of
  survivors alone shown earlier but NOT that can serve all MarketGrant and Crew,
  so use a joint test. No specifying W readings of the thermal row already at endpoint.
- `Crew`: one-step receipts for this same W schedule plus K-step continuation
  after restoration. No contours estimated on any independently tuned path.
- `Stake`: earlier value-order uncert polynomial estimate needed (mixed
  histories). Call BEFORE the regenerated threshold and at old widths. NO
  polynomial clipping or Wick answer yet.
Fees in this ledger are conjunctive, including agreement on atlas kernel stamps
through a comparison. These aren't hypotheses requiring a particular algorithm
or implicitly changing anything about Family or its point-limit path. This is
not claiming a proof from an opaque Producer.fields nor from UV of unnormalized labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {S : Table C.book}

-- Particular stage purchase. rho predetermined; weights b need ALL large.
structure Cohesion (C : Family G) (d : ℕ) where
  purses : ℕ → Purse
  fixed : ℝ
  large : 6 ≤ fixed
  gain : saves C d + 3 ≤ fixed
  atoms : ℕ
  numbers : d ≤ atoms
  pan : ℝ
  mark : ℝ
  supported : 0 ≤ mark
  sameB j : (purses j).band=fixed
  credit j : (purses j).band*d+saves C d ≤ (purses j).credit
  funding j : (purses j).f=pan
  same_size j : (purses j).taylor=atoms
  -- steps can vary α and cut horizon after this shape per stage (still pay growth before L)
namespace Cohesion
def current (c : Cohesion C d) (j) := c.purses (C.path.levels.clock.J j)
lemma hr (c : Cohesion C d) : 0<c.fixed:= by linarith only [c.large]
lemma money (c : Cohesion C d) : c.pan+c.fixed*d+saves C d ≤ -8 := by
  rw [← c.sameB 0,← c.funding 0, add_assoc]; exact (add_le_add_right (c.credit 0) _).trans (c.purses 0).fits
end Cohesion

variable (F : Cohesion C d) (W : HaarBudget G) (P : Columns C S d)

structure Metering (k : ℕ) (w : ℝ) : Prop where
  charge : Peak.Charge C.path.levels F.fixed k 2 W (F.current k).era
  cost : Launch C k (F.current k) w F.mark

variable (H : C.Makes)

-- Keep visible mathematical checkpoint. This does NOT assert density Comparison.
def supplies {w} (p₀ : Launch C k (F.current k) w F.mark) :=
    let A:= C.path.levels; let s:= clim A k; let D:=F.current k
    ∀ (hk : C.ref d ≤ k),(∀ i,Fit C.path.levels D.band k (P.row i).expected) →
      ∀ᶠ N in atTop,∃ (hN : k ≤ N), ∀ p, ∃ (X : AtlasData G C.S p) (T : Lead G C.S p) (c : Course C N p k) (Y : (u : ℕ)→Rep G (C.side u p)),
        survivors C N k p p₀.pane (Y k) ∧ MarketGrant c Y X T D ∧
          ∀ i, Crew c Y T D (P.row i).expected ∧ Wall.Vantage A d k p ((P.row i).extra+1) F.atoms F.fixed X ∧
            ∀ V : Fin ((P.row i).extra+1)→ C.label d, (∀ j, Perch.bill F.pan s*moneys C d k N p (V j)≤ Perch.bill (-8) s) →
              Stake (P.row i).extra (P.row i).expected D.band hN V H hk c (Hat s ^ F.mark)

-- simultaneous demands before comparison (post-L gates and actual existence of all these inputs on these k stamps)


-- assembly proof
variable (v : Price.Representatives C P)



end YM.Next.Rank.Tapes
