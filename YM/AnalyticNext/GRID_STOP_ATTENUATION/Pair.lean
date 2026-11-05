import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.MULTISOURCE.Curves
import YM.Push.GRID_APPROXIMATION.Match
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_DIFFERENCE.Subtraction



set_option warningAsError false

/-!
# Use G09 on the *internal* comparison, at the actual vacuum and masks

We take Clocks/Based from k down to C.ref d on `Match.view`, not k's own
history as a cutoff. Use its exact terminal inverse (we don't choose other
matching rows on k, nor another ref, nor use a vacuum limit). . Even with calibration, we need local PSREC-style
estimates on the COMBINED remainder and primary for this application!
See `Recovery`. These are strictly upstream gates. In particular no
cost of order exp(-γ * scale difference) required in those hypotheses.
Use the same support alphabet and the sign after coarrival. For rays at
equal index & support this combines before measuring; for forced this
subtracts on the same address. If necessary an upstream producer can
match/coordinate its dictionaries to use this lemma; there is no inferred
promise of that compatibility from `Based`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Pair
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi
open Push.GridApprox
open Match
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {C : Family G} {d k m p N : ℕ}

/-- Analysis exponents `+δ` in the signed direction below birth, no change to
any masks, paths, orders or names. May eventually use this for compatibility
at a prescribed singleton in the response estimates; erase before a call of
G09. -/
def funds (R : Rep G n) (δ : ℝ) (H : 0≤δ) : Rep G n :=
    { R with p := { R.p with supportExponent := R.p.supportExponent+δ,
                               exponent_pos := add_pos_of_pos_of_nonneg R.p.exponent_pos H } }

variable {F : Frame G d} {P : Rep G n} {o : Site n} {j κ z ε : ℝ} {u : Coefficient F n}

theorem funds_erases (h : 0≤j) (H : u.remBound o (funds P j h) κ z) : u.remBound o P κ z := by
  obtain ⟨a,b,ha,hb,hab,hκ,⟨x,hX,hx⟩,y,hY,hy⟩ := H
  have ht (X : Support n) (t : ℝ) (he : 0≤t) : 0≤ P.p.mass X t ∧ P.p.mass X t≤ (funds P j h).p.mass X t := by
    unfold BudgetPoint.mass; refine ⟨mul_nonneg (Real.exp_pos _).le he,mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) he⟩
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h) (by exact_mod_cast Nat.zero_le _)
  refine ⟨a,b,ha,hb,hab,hκ,⟨x,Multi.permit_le hX le_rfl (fun i => ht _ _ (hx i).1),hx⟩,y,
    Multi.permit_le hY le_rfl (fun i => ht _ _ (hy i).1),hy⟩

abbrev Probe (C : Family G) (N p d k : ℕ) := TransferData (C.labels.level d) (Match.view C.path N) k p
variable (B : Probe C N p d k)

def tune (v : C.label d) : C.label d := B.terminal.symm v
def fresh (m : ℕ) (v : C.label d) : Coefficient (C.labels.level d) (C.side m p) := B.entries m (tune B v)
def split (m : ℕ) (v : C.label d) : Coefficient (C.labels.level d) (C.path.S.side m p) := Push.RelayDifference.combine (fresh B m v) (Match.old C m N p v)

def remTop {m : ℕ} (Q : Coefficient (C.labels.level d) (C.side m p)) :=
    (C.path.levels.params m).columns * (C.labels.level d).coeffSize ((C.labels.level d).core Q.x)

variable (v : C.label d) (x : ℕ → ℝ)

def duet : Duet C.path (C.labels.level d) N p (C.ref d) k where
  voice m := split B m v
  cost m := if m=k then remTop (C:=C) (p:=p) (m:=k) (fresh B k v) + remTop (C:=C) (p:=p) (m:=k) (Match.old C k N p v) else x m
  atPoint _ := 0

/-- Priced *one-step inequalities* on these data. 
ki's maps may use all the information picked from this stepped path.
No freedom claimed to reinterpret differences by another choice of
labels. Costs include all derivative orders of R.p. If your extraction
procedure cannot supply the estimates on these particular labels, cannot
use this contract.

Ask for an extra support reserve on the remainders (but do NOT
claim to produce it); preserves the option to use normalized output
probes at the neighboring step at that extra exponent. `funds 0` suffices
if can satisfy our local mixed gate without that (in general that may be
harder!). -/
structure Recovery (W : Bid.Worth) (δ : ℝ) : Prop where
  sure : 0 ≤ δ
  remainder (m : ℕ) : C.ref d ≤ m → m < k → (split B m v).remBound 0
    (funds (C.path.rep N p m) δ sure) (Multi.money C.path.levels m) (x m)
  principal (m : ℕ) : C.ref d ≤ m → m < k → let T := duet B v x
    Bid.direction C.path W m (C.labels.level d) (T.voice m).x (T.voice (m+1)).x (T.cost m) (T.cost (m+1))

variable (H : C.Makes) (hB : B.Based C.params (C.localSection d) (C.ref d)) (hk : k≤N)
include hB H hk













/-- Common envelope scale for origin pairs at k with coeffSize ≤ R. -/
def principal (C : Family G) (k : ℕ) (R : ℝ) :=
    8*(1+(C.path.levels.params k).columns)*Match.ladder C.path k * R




end YM.AnalyticNext.GridStop.Pair
