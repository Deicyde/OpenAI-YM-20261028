import YM.Next.FLUCTUATIONS.Kernel
import YM.Next.FOUNDATIONS.SU2
import YM.Push.COMMON_WITNESSES.RowEstimates

/-!
# Common RankWidths and receipts

Compatibility contribution for finite all-subset inputs. Supply on a
specified tower, *or* give producers which can run on arbitrary inherited
extracts below the base -- compare original RCorrected plan in the ledger.
NEITHER supply proved from `Base`. The precise finite estimates include a
quantitative  input. Common upper-rank use is on the *same*
projection/the *same* measure estimates (`S,T`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Wilson Cells Table Next.Extract Dash
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {b : Presentation C} {S T : Table C.book} {R : Bin S} {M : ℕ → Table C.book}
variable {V : DiffPlan T} {z : ∀ d : ℕ, ℕ → CoordMap C d} {d : ℕ} {f : Order}

/-- Complete receipt for a d. Same-A proof so later jobs can really reuse the
finite estimates. Includes both-stage limits and **actual** phase input. -/
structure Solvent {X : Columns C T d} (Y : X.Trials) (b : Presentation C) (f : Order) (A : ℕ → ℝ)
    (o : ProbeID X → ℕ → C.label d) : Prop where
  setup : Setup Y
  nonneg k : 0≤A k
  purchases i : rankInvoice Y b A i f
  response : Response Y f o
  unselected : Prices Y T
  level : Module.finrank ℂ (T.Field d) = X.dim+1
  valid : Columns.Trials.Valid f Y



lemma Solvent.upon {X : Columns C T d} {Y : X.Trials} {A o} {g : Order} (H : Solvent Y b f A o) (h : Tails g f) :
    Solvent Y b g A o := by
  refine ⟨H.setup,H.nonneg,fun i => pay Y b _ _ h (H.purchases i),?_,H.unselected,H.level,
    (refines_iff.mpr h).rank _ H.valid⟩
  exact h.keeps H.response

/-!
When data are specified across weight families on successive orders, don't
need to assume a `Valid` producer for even one d, or that the finite bills
are ready for all k at one refinement. This is useful since some of those
require both finer offsets and previously chosen schedules. The real physical
obligation is now `Stock` below, with the specific quantitative constants
AND the successive-refinement compatibility. (Also normalization elsewhere.)
-/

/-- Candidate rank fields for all degrees. -/
structure Offers (T : Table C.book) where
  cols (d : ℕ) : Columns C T d
  cylinder (d : ℕ) : (cols d).Trials
  cost : ℕ → ℕ → ℝ

namespace Offers
variable (Y : Offers T)

/-- No ordering estimate assertions. -/
def sane : Prop := (∀ d, Setup (Y.cylinder d)) ∧ ∀ d k, 0 ≤ Y.cost d k

def prices (b : Presentation C) (j : ℕ × Option (Bool × ℕ × ℕ)) (f : Order) : Prop :=
  rankInvoice (Y.cylinder j.1) b (Y.cost j.1) j.2 f

-- y final comparison coordinates only. Other fields unchanged.
def aim (y : ∀ d, ProbeID (Y.cols d) → C.label d) : Offers T := { Y with cylinder d := decoded (Y.cylinder d) (y d) }

def affords (b : Presentation C) (f : Order) (o : ∀ d, ProbeID (Y.cols d) → ℕ → C.label d) : Prop :=
    ∀ d, Solvent (Y.cylinder d) b f (Y.cost d) (o d)
end Offers

lemma valid_offers {X : Offers T} {o} (h : X.affords b f o) : RankWidths C f T :=
  fun d => ⟨X.cols d,X.cylinder d,(h d).valid⟩



/-- Antecedent on actual rank data. All cost/position constants chosen
jointly as above -- at a fixed `C`. It is OK if produced only after another
REFINEMENT of f: just start the invoice tower at that order. -/
def Stock (b : Presentation C) (T : Table C.book) (f : Order) : Prop :=
  ∃ X : Offers T, X.sane ∧ Stationed f (X.prices b)




end YM.Push.Common
