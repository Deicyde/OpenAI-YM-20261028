import YM.Ac.Table
import YM.Pressure.Seeds
import YM.SectorNext.RECONNECTED_LOCALITY.Gram
import YM.SectorNext.RECONNECTED_LOCALITY.Parts
import YM.SectorNext.RECONNECTED_LOCALITY.Replica



set_option warningAsError false

/-!
# Dictionary after optional extensions

Present the actual Gaussian conditional sector step  on this
IR. The alphabet isn't a support type; give a distinct address for each raw choice incl packet
seed set, marked internal letter/path/outcome choice, alternatives in a split etc (labels may
also stay dormant or denote the zero function). Exclude forbidden pairs e.g. duplicate physical
*parent* address using the gate, with full queried sites. `Cellular` is a purchase, not imposing
that a physical analytic expression already use a quotient locality: compute contents and
validity of an address from selections (packet origins, original K labels etc), fields, regular
color args, and independent bindings; require these individual recipe/table operations to respect
complete footprints BEFORE taking the integral. Record halos all physical tag/Y/Z positions
(incl the halo for the covariance table/conditional computations at a Z entry), even if their
value there is zero. To integrate a term multiplying a flag query keep the link endpoints it can
probe also (use e.g. `inspected`). No assertion that every stored site is a numerical read.
Weights may jump at thresholds here. Standalone integrals are *not* the smooth extensions one
will need a separate port to supply later, though they are measurable/gauge/local under explicit
hypotheses. All applications of the analytic charge after this will be *also* conditional on the
source hypotheses producing the actual integral and its absolute/differentiated bounds. The tag
law is not hidden in existence hypotheses on coarse activities: see `Bind` below and the tie-in
requiring the chart identity with the actual `StepData.Choices`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect

open RG Lattice Filter Function MeasureTheory Words Wilson
open Bind Window

variable {G : Gauge} {c : Side} {ι η κ : Type*} {Y : η → Type*}

/-- Factors & geometry. Can include evaluated profile choices/kernels, kept guards, potentials,
Mayer remainders, determinant/Jacobian letters etc. Include complete decisions and paths. `value`
uses one address at a time with SAME V,θ,z even for likelihoods. Sector/context computations
use `s` plus that common data. The compatibility predicates on raw choices use the `s` table
(eg eligibility of a selected optional address); internal Borel/flag predicates on actual fields
keep INSIDE `value`. `gate` not a test of realizability by off-address fine fields. Real-valued
physical weights; if doing probabilities on complex marks handle absolute value and signs also
inside, not in reference law (this release uses ℝ, countable gas). -/
structure Form (G : Gauge) (c : Side) (ι κ : Type*) {η : Type*} (Y : η → Type*) where
  foot : ι → Support c
  flag : ι → Support c
  foot_ne : ∀ i,(foot i).Nonempty
  flag_sub : ∀ i,flag i ⊆ foot i
  stages : ι → Finset η
  lines : ι → Finset κ
  gate : ι → Finset ι → Prop
  value : ι → Finset ι → Config G c → Tables Y → Z κ → ℝ

namespace Form
variable (X : Form G c ι κ Y)

abbrev land (p : Finset ι) := region X.foot p
abbrev vote (p : Finset ι) := region X.flag p

def roll (s p : Finset ι) (V : Config G c) (t : Tables Y) (z : Z κ) := ∏ i∈p,X.value i s V t z

def Ok (p : Finset ι) := permits X.gate p
def Reads (P : BudgetPoint) (p : Finset ι) (V : Config G c) := X.land p ∩ flags P.threshold V = X.vote p



end Form

/-- Agreement on exactly the tested table coordinates. -/
def Tied {α : Type*} {E : α → Type*} (I : Finset α) (x y : Tables E) := ∀ i∈I,x i=y i

lemma Tied.smaller {α : Type*} {E : α → Type*} {I J : Finset α} {x y : Tables E}
    (h : Tied I x y) (hv : J⊆I) : Tied J x y := fun _ he => h _ (hv he)

variable [∀ i,MeasurableSpace (Y i)]

/-- ONE conditional full Z covariance, can depend on all tables and V
(e.g., to complete local evaluations with actual D' far away). `Borel`/smooth not part of
this record. Outside may be inactive with identity covariance. When tying to a Wilson or
fluctuation kernel, keep that *same* matrix and completion every time. -/
structure StageLaw (G : Gauge) (c : Side) (ι κ : Type*) {η : Type*} (Y : η → Type*) where
  map : Finset ι → Config G c → Tables Y → Measure (Z κ)
  cov : Finset ι → Config G c → Tables Y → Cov κ

/-- Full context-locality hypotheses.

* Order of inputs frozen across standalone and assembled. Want validity gates and
  address values `Retained` incl negative answers that could change those rules. Geometry
  should price all potential k, V and seed-list queries at their endpoints.
* `entry` means the locations determining a conditional **Z-Z covariance** between
  two used arguments are priced in the endpoint letter neighborhoods (can choose bigger within
  committed halo), EVEN when they are read by two different letters. Allows computed
  A entry stencil, principal inverses etc, but no claim of that locality for an inverse
  on all sites. Symmetric principal-window rules can meet this. Either preserve even
  off V domains or extend while preserving assembly. Actual output D' far away may be
  included in cov recipe, as long as `entry` holds there. `cross` separate finite range task.
* Costs not furnished by this locality. The product tag/Y law is not for Z.
-/
structure Cellular [Fintype κ] (X : Form G c ι κ Y) (N : StageLaw G c ι κ Y) : Prop where
  ready : Retained X.foot X.gate
  stagePos : ∀ i j, Disjoint (X.foot i) (X.foot j) → Disjoint (X.stages i) (X.stages j)
  linePos : ∀ i j, Disjoint (X.foot i) (X.foot j) → Disjoint (X.lines i) (X.lines j)
  recover : ∀ i s b V U t q z w, (∀ j, ¬Disjoint (X.foot i) (X.foot j) → (j∈s ↔ j∈b)) →
    Agrees (X.foot i) V U → Tied (X.stages i) t q → Tied (X.lines i) z w →
      X.value i s V t z = X.value i b U q w
  entry : ∀ i j s b V U t q, (∀ l, ¬Disjoint (X.foot i) (X.foot l) ∨ ¬Disjoint (X.foot j) (X.foot l) → (l∈s ↔ l∈b)) →
    Agrees (X.foot i) V U → Agrees (X.foot j) V U →
    -- ACTUAL V endpoints for a link with one site in each footprint but in neither footprint
    -- wholly: not allowed by this version unless footprints are extended. Could permit
    -- `Agrees` on the *union* instead here (legit!); this stronger gate suffices and
    -- matches separate windows at either endpoint if that construction is used.
    Tied (X.stages i) t q → Tied (X.stages j) t q → ∀ a∈X.lines i, ∀ d∈X.lines j,
      N.cov s V t a d = N.cov b U q a d
  cross : ∀ i j s V t,Disjoint (X.foot i) (X.foot j) → ∀ a∈X.lines i, ∀ d∈X.lines j,
    N.cov s V t a d = 0
  states : ∀ s V t,Says (N.map s V t) (N.cov s V t)
  symmetric : ∀ s V t i j,N.cov s V t i j=N.cov s V t j i

/-- Convenient Borel port through a (possibly dense) Gram table, NEVER pay locality or cost
from this table itself. Full Y,Z,V together, not pointwise sections. -/
structure Printed [Fintype κ] (X : Form G c ι κ Y) (N : StageLaw G c ι κ Y) : Prop where
  rootLaw : ∃ R : Finset ι → Config G c → Tables Y → κ → κ → ℝ,
    (∀ s V t,N.cov s V t=gram (R s V t)) ∧
    (∀ s i j,Measurable (fun (p : Config G c × Tables Y) => R s p.1 p.2 i j))
  stamped : ∀ i s,Measurable (fun (p : (Config G c × Tables Y) × Z κ) => X.value i s p.1.1 p.1.2 p.2)

namespace Form
variable (X : Form G c ι κ Y)
variable [DecidableEq η] [DecidableEq κ]
abbrev staged (p : Finset ι) := p.biUnion X.stages
abbrev window (p : Finset ι) := p.biUnion X.lines

/-- Conditional on all θ,Y. Reserves its actual full covariance when used in global formula,
standalone p-covariance when used by p. -/
def booth (N : StageLaw G c ι κ Y) (s p : Finset ι) (V : Config G c) (ρ : ℝ → ℝ) (t : Tables Y) :=
    ∫ z, ρ (X.roll s p V t z) ∂N.map s V t

variable [Fintype η]

/-- Full iterated conditional expectation. No V measure or normalization by output
probability inside this density. -/
def edition (N : StageLaw G c ι κ Y) (m : ∀ i, Measure (Y i)) (s p : Finset ι) (V : Config G c) (ρ : ℝ → ℝ) :=
    ∫ t, X.booth N s p V ρ t ∂Measure.pi m

end Form

namespace Cellular
variable {X : Form G c ι κ Y} {N : StageLaw G c ι κ Y}
variable [Fintype κ] (H : Cellular X N)
variable [DecidableEq κ] [DecidableEq η]

include H
omit [∀ i,MeasurableSpace (Y i)] in
private theorem resurvey {p s b : Finset ι} {V U : Config G c} {t w : Tables Y}
    (hv : Agrees (X.land p) V U) (ht : Tied (X.staged p) t w) {z z' : Z κ} (hz : Tied (X.window p) z z')
    (hh : ∀ j, ¬Disjoint (X.land p) (X.foot j) → (j∈s↔j∈b)) :
    X.roll s p V t z=X.roll b p U w z' ∧
      ∀ a∈X.window p,∀ d∈X.window p,N.cov s V t a d=N.cov b U w a d := by
  have hs (i) (hi : i∈p) : X.foot i⊆X.land p := fun _ he => Finset.mem_biUnion.mpr ⟨_,hi,he⟩
  have he (i) (hi : i∈p) : Agrees (X.foot i) V U := agrees_mono hv (Finset.coe_subset.mpr (hs i hi))
  have hr (i) (hi : i∈p) : Tied (X.stages i) t w := ht.smaller fun _ he => Finset.mem_biUnion.mpr ⟨_,hi,he⟩
  have hl (i) (hi : i∈p) : Tied (X.lines i) z z' := hz.smaller fun _ he => Finset.mem_biUnion.mpr ⟨_,hi,he⟩
  have hy (i) (hi : i∈p) (j) (hj : ¬Disjoint (X.foot i) (X.foot j)) : j∈s↔j∈b :=
    hh j (fun h => hj (Finset.disjoint_of_subset_left (hs i hi) h))
  refine ⟨Finset.prod_congr rfl (fun i h => H.recover i s b V U t w z z' (hy i h) (he i h) (hr i h) (hl i h)),?_⟩
  intro a ha d hd
  obtain ⟨i,hi,ha⟩:=Finset.mem_biUnion.mp ha; obtain ⟨j,hj,hd⟩:=Finset.mem_biUnion.mp hd
  exact H.entry i j _ _ _ _ _ _ (fun k hh => hh.elim (hy i hi k) (hy j hj k))
    (he i hi) (he j hj) (hr i hi) (hr j hj) a ha d hd

omit [∀ i,MeasurableSpace (Y i)] in
/-- Compare component to standalone. -/
theorem survey {p s : Finset ι} (h : p ⊆ s) (he : ∀ i∈s, ¬Disjoint (X.land p) (X.foot i) → i∈p)
    {V U : Config G c} {t w : Tables Y} (hv : Agrees (X.land p) V U) (ht : Tied (X.staged p) t w) :
    (∀ z z',Tied (X.window p) z z' → X.roll s p V t z=X.roll p p U w z') ∧
      ∀ a∈X.window p, ∀ d∈X.window p,N.cov s V t a d=N.cov p U w a d := by
  have hr : ∀ j,¬Disjoint (X.land p) (X.foot j) → (j∈s↔j∈p) := fun _ hx => ⟨fun hi => he _ hi hx, fun hi => h hi⟩
  exact ⟨fun _ _ hh => (H.resurvey hv ht hh hr).1,(H.resurvey hv ht (z:=0) (z':=0) (fun _ _ => rfl) hr).2⟩

variable (L : Printed X N)

include L
omit [DecidableEq κ] [DecidableEq η] H in
theorem _root_.YM.SectorNext.Reconnect.Printed.roll {s p : Finset ι} {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    Measurable (fun (q : (Config G c × Tables Y) × Z κ) => ρ (X.roll s p q.1.1 q.1.2 q.2)) := by
  apply Measurable.comp hρ (Finset.measurable_prod _ (fun i _ => L.stamped i s))
omit [DecidableEq κ] [DecidableEq η] in
theorem booth_joint (s p : Finset ι) (ρ : ℝ → ℝ) (he : Measurable ρ) :
    Measurable (fun q : Config G c × Tables Y => X.booth N s p q.1 ρ q.2) := by
  obtain ⟨R,hR,hB⟩:=L.rootLaw
  have hr (V : Config G c) (t : Tables Y) : N.map s V t=pour (R s V t) := by
    have he := H.states s V t; rw [hR] at he
    exact he.unique (pour_says _)
  simp_rw [Form.booth,hr]
  exact parameter_meas (R:=fun q : Config G c × Tables Y => R s q.1 q.2) (hB s) _ (L.roll he)

omit [DecidableEq κ] [DecidableEq η] in
theorem edition_joint [Fintype η] (m : ∀ i,Measure (Y i)) [∀ i,SigmaFinite (m i)] (s p : Finset ι)
    (ρ : ℝ → ℝ) (he : Measurable ρ) : Measurable (fun V => X.edition N m s p V ρ) := by
  exact (booth_joint H L s p ρ he).stronglyMeasurable.integral_prod_right'.measurable

end Cellular
end YM.SectorNext.Reconnect
