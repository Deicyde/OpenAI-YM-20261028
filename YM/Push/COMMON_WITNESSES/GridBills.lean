import YM.Push.COMMON_WITNESSES.Orders

/-!
# A finite approximation port and transport to Grill -- stations and gluing

Positive compatibility lemma (not Grid Approximation from multi-source, still
have actual grid estimate assumptions).

Our finite hypothesis specializes
 to requests for the anti-products that will suffice here.

Allows
even finite translation prefixes, and finite basis-monomial tests -- joint
plots in each of these estimates.

No changes to cutoff products.

If wanting a local grid theorem
with shrinking supports/invariant plots etc., those are separate claims (but
one might produce these hypotheses as part of that argument).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Lattice MeasureTheory Next.Extract Wilson OS
open scoped Topology BigOperators ContDiff

variable {G : Gauge} (C : Family G)

/-- Fixed signature at grid estimate: all basis choices for these n slots,
no restriction that they are different. Coordinate reference basis in `book`. -/
abbrev Combo {n : ℕ} (d : Caps n) := ∀ i, (C.labels.level (d i)).Index

def baseWord {n : ℕ} (d : Caps n) (p : Combo C d) : Fin n → C.book.Token :=
    Extraction.stack ⟨n,d,p⟩

/-- k supersets of Gram budget -- only off-diagonal i≠j. No bound uniform
in k asked for the approximants, but *need* `cap k` BEFORE any number J of
translates (also before t). `past` is a large-translation threshold selected
already, for each pair, at each fixed approximation cost. -/
structure GrillCosts where
  cap (k : ℕ) : ℝ
  nonneg k : 0≤cap k
  past (k i j : ℕ) : ℕ

variable {n : ℕ} (h : ℕ) (x : Fin n → Cover) (d : Caps n)

/-- Actual flash products on this cutoff; same common Wilson law. Cross
observable for different basis choices. `flash` = actual A−θA with time-axis
mirror on BOTH positions and fields according to the signed action.
NO conjugation of the second flash; balances an ordinary real pair in the
intended application (not RP pair). As with `bill`, take real part. Distant
centers j are at cover translation t*j in each coordinate. -/
def cross (N p t i j : ℕ) (s u : Combo C d) :=
    ∫ q : Config G (C.side N p),
      (Grid.flash (C:=C) h (baseWord C d s) x N p t i q * Grid.flash (C:=C) h (baseWord C d u) x N p t j q).re
      ∂law G _ (C.beta N p)

abbrev Plots (N p : ℕ) := ℕ → Combo C d → Config G (C.side N p) → ℝ

variable (A : GrillCosts)

/-- Finite in regulator and observable family. At fixed t,J, the estimates
are **simultaneous** (and in the same measure). Only asks bills at t if
pair horizon has been crossed. Outside j<J the candidate functions are
dummies. The bound does not depend on J,t,N,p. It can depend on n,d,grid,
including positions (when A is chosen in our theorems), and k. Tolerance
`toll k` chosen for convenience -- may reindex any null tolerances in
supplying it. -/
structure Instalment (k N p t J : ℕ) (y : Plots C d N p) : Prop where
  safe j : j<J → ∀ s, Measurable (y j s) ∧ ∀ q, |y j s q| ≤ A.cap k
  joins i j : i<j → j<J → A.past k i j≤t → ∀ s u,
    |(∫ q, y i s q*y j u q ∂law G _ (C.beta N p))-cross C h x d N p t i j s u| ≤ toll k

def PrefixBill (f : Extraction.Order) (k t J : ℕ) : Prop :=
  f.late fun N p => ∃ y : Plots C d N p, Instalment C h x d A k N p t J y

/-- The single resulting group of functions. -/
abbrev Exhibit := ℕ → ∀ N p : ℕ, ℕ → Plots C d N p

def Exhibits (f : Extraction.Order) (P : Exhibit C d) : Prop := ∀ k t J,
  f.late fun N p => Instalment C h x d A k N p t J (P k N p t)

variable {C h x d A}

lemma PrefixBill.upon {f g : Extraction.Order} {k t J : ℕ} (H : PrefixBill C h x d A f k t J) (hw : Tails g f) :
    PrefixBill C h x d A g k t J := by
  unfold PrefixBill at *
  exact hw.late H

lemma Exhibits.upon {f g : Extraction.Order} {P : Exhibit C d} (H : Exhibits C h x d A f P) (hw : Tails g f) :
    Exhibits C h x d A g P :=
  fun i t J => hw.late (H i t J)

private lemma Instalment.drop {J k p t U W : ℕ} {v : Plots C d U p} (H : Instalment C h x d A k U p t W v)
    (he : J ≤ W) : Instalment C h x d A k U p t J v :=
  ⟨fun j hj => H.safe j (lt_of_lt_of_le hj he),fun i j hq hj => H.joins i j hq (lt_of_lt_of_le hj he)⟩


end YM.Push.Common
