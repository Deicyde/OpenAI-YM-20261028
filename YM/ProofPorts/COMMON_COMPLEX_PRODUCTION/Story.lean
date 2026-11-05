import YM.Next.BOUNDARY.Coordinates
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Bath
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Intact
import YM.Push.CUTOFF_PROJECTORS.Along

/-!
Earlier remaining tasks include pointwise optional expansion & address
bijection encoded in `Census`, and per-atom integral formulas on these
objects, not disjoint-gas or prelog **answer** assumptions. Selection can
include e.g. compulsory packets and variants of incoming source addresses
(also infinite repeated E orders as ONE power option) and distinct trigger
nodes. Eligibility cross-checks and overlap footprints are full physical ones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss Pressure Bid Tree YM.Push.SectorMeasure YM.Push.LogIdentity
open Component Arrival Desk Stamp
open scoped Topology BigOperators Classical MatrixOrder Tags ENNReal
variable {G : Gauge} {n f : Side} {S : StepData n f} {V I : Type}

/-- Atom operands are read before integration (unmasked at an unforced
letter of Brush). `Story` presentation fixed on F's whole amplitude space
& on THIS StepData. Not saying component coefficients can be independently
fitted to z or to V. Empty sectors and unused choices need a prescription
too (blank letters allowed, see census below). -/
structure Story (s : Setting G S) (F : Arrival.Flock V G f) (B : Brush V G n) (I : Type) where
  A : Pasture I B
  store : Finset I → Stores S
  back : Finset I → Flock.Voucher F
  bath : Fruit → Bath G n
  extract : ∀ i : Fruit, s.Stage → (bath i).tag
  project : ∀ i : Fruit, ∀ a : Stores S, Config G n → s.Stage → Matrix (bath i).Line (s.line a) ℝ
  factor : ∀ i : Fruit, I → (bath i).tag → (bath i).Play → Config G n → ℂ

namespace Story
variable {s : Setting G S} {F : Arrival.Flock V G f} {B : Brush V G n} (T : Story s F B I)

-- permission to query true local coefficient integral
def openTo (P : BudgetPoint) (U : Config G n) (i : Fruit) : Prop :=
    i.elim (fun j => Healthy P.threshold (B.u j).zone U) (fun _ => True)

def raw (U : Config G n) (i : Fruit) (θ : (T.bath i).tag) (z : (T.bath i).Play) : ℂ := ∏ j∈T.A.bud i,T.factor i j θ z U

def legal (P : BudgetPoint) (U : Config G n) (i : Finset I) :=
    ∃ p : Finset Fruit, Pasture.valid (B:=B) (flags P.threshold U) p ∧ T.A.recovers p i

/-- Full selection at a given Store. No contribution without a
compatible decomposition. Compare to the literal expansion BEFORE any
integral with OTHER geometry in the census theorem. This IS a producer
integrity obligation, including reconstruction/reversal and answers to
queries/individual θ likelihoods, $$ scales and inverse-bond rules.
All supports already enlarged for projected footprint or branch data;
paying costs without this identity will not suffice. -/
def run (P : BudgetPoint) (U : Config G n) (a : Stores S) (i : Finset I) (θ : s.Stage) (z : Vec (s.line a)) : ℂ :=
    if h : T.legal P U i then
      B.base U * ∏ j∈h.choose, T.raw U j (T.extract j θ) (T.project j a U θ *ᵥ z)
    else 0

def slice (P : BudgetPoint) (U : Config G n) (a : Stores S) (q : Flock.Voucher F) (i : Finset I) (θ : s.Stage) (z : Vec (s.line a)) : ℂ :=
    if T.store i=a ∧ T.back i=q then T.run P U a i θ z else 0

variable [Fintype V]

/-- Still to be built on the sector/projection operations AND the chosen
true history. Quantities are *unintegrated* except for specifying the
chosen letter coefficients themselves. No price on component answers,
Tenders or Stability assumed in this identification. Hard input predicates,
shared and even zero-amplitude source calls, all V and query outcomes.
Can't test reconstruction at a Taylor proxy or flat C. We require even
singular-free approximate marginals in chargeable standalone computations.
(Bound on C itself only required later.) -/
structure Census (Q : Rep G f) (P : BudgetPoint) : Prop where
  pays : B.pay=fun i => (F i).fiat
  positive (U i) (y : (T.bath i).tag) : openTo (B:=B) P U i → ((T.bath i).cov U y).PosDef
  soft i U : Healthy P.threshold (B.u i).zone U → ∀ᶠ W in 𝓝 U,
      (B.u i).stamp.ink W = (T.bath (Sum.inl i)).readout W (T.raw W (Sum.inl i))
  hard i U : (B.d i).ink U = (T.bath (Sum.inr i)).readout U (T.raw U (Sum.inr i))
  code i U (p : Finset Fruit) : Pasture.valid (B:=B) (flags P.threshold U) p → T.A.recovers p i →
    (∀ j∈p,∃ θ z, T.raw U j θ z ≠ 0) → F.signature Q (T.back i) = ∑ j∈i,T.A.hue j
  assemble i U (p : Finset Fruit) : Pasture.valid (B:=B) (flags P.threshold U) p → T.A.recovers p i →
      Parallel (fun j : ↥p => T.bath j) U s.plan (s.mat (T.store i) U) (fun j => T.extract j)
        (fun j => T.project j (T.store i) U)
  -- θ and z on `Setting.portion` are full physical arguments with EACH
  -- price factor still present (likelihood, coupling/remainders, constants,
  -- chart, masks, etc). No expansion recomputing C from default complements.
  spell U a q : ∀ᵐ yz ∂(s.plan.prod (standard (s.line a))),
    s.portion a U Q.beta (F.peelRow Q q) yz.1 yz.2 =
      ∑' i, T.slice P U a q i yz.1 (CFC.sqrt (s.mat a U yz.1) *ᵥ yz.2)

omit [Fintype V] in
private lemma opened {P : BudgetPoint} {U : Config G n} {p : Finset Fruit}
    (hs : Pasture.valid (B:=B) (flags P.threshold U) p) {i} (hi : i∈p) : openTo (B:=B) P U i := by
  obtain i|i:=i
  · apply Finset.disjoint_left.mpr
    rw [← hs.2]; intro b hb he; obtain ⟨j,hj,h⟩:= mem_biUnion.mp he
    have hx : Disjoint ((B.u i).zone) ((B.pack j).zone) := hs.1 hi (mem_toRight.mp hj) (by simp)
    exact Finset.disjoint_left.mp hx hb ((B.pack j).property.2 h)
  trivial

namespace Census
variable {T} {Q : Rep G f} {P : BudgetPoint} (h : T.Census Q P)
include h



end Census

omit [Fintype V] in
private lemma run_eq (P : BudgetPoint) (U : Config G n) (a : Stores S) (i : Finset I) (p : Finset Fruit)
    (hp : Pasture.valid (B:=B) (flags P.threshold U) p) (hi : T.A.recovers p i) (θ z) :
    T.run P U a i θ z=B.base U * ∏ j : ↥p, T.raw U j.val (T.extract j θ) (T.project j a U θ *ᵥ z) := by
  have he : T.legal P U i := ⟨p,hp,hi⟩
  unfold run; rw [dif_pos he,T.A.known he.choose_spec.2 hi, prod_subtype p (p:=(·∈p)) (fun _ => Iff.rfl)]

/-- Auxiliary summability bill for reaching Flow. One paid point with every
needed coordinate nonzero (can be *extremely small* and list-dependent). -/
def weighing (z : V → ℂ) (P : BudgetPoint) (U : Config G n) (i : Fruit) :=
    if openTo (B:=B) P U i then ‖Stamp.beat (calls B i) z‖*(T.bath i).mass U (T.raw U i) else 0

structure Costs (z : V → ℂ) (P : BudgetPoint) : Prop where
  components (i : Fruit) (U : Config G n) : openTo (B:=B) P U i → (T.bath i).Usable U (T.raw U i)
  scale (x : V) : z x ≠ 0
  affordable U : Summable (T.weighing z P U)

omit [Fintype V] in
private lemma solvency (q : Finset Fruit → ℝ) (h : Summable q) (P : BudgetPoint) (U : Config G n) :
    Summable (fun i : Finset I => if he : T.legal P U i then q he.choose else 0) := by
  let b : Finset I→ ℝ := fun i => if he : T.legal P U i then q he.choose else 0
  change Summable b
  have he : Injective (fun i : {i // T.legal P U i} => i.property.choose) := by
    intro i j hh; apply Subtype.ext
    exact (T.A.retrieves i.property.choose_spec.2).symm.trans ((congrArg T.A.expand hh).trans (T.A.retrieves j.property.choose_spec.2))
  have hg := h.comp_injective he; rw [← Set.indicator_eq_self.mpr (show Function.support b ⊆ {i | T.legal P U i} from ?_)]
  · exact summable_subtype_iff_indicator.mp (hg.congr fun i => by change _ = b i.val; unfold b Function.comp; rw [dif_pos i.property])
  exact fun i hi => Classical.byContradiction fun h => hi (dif_neg h)


namespace Costs
variable {T} {z : V→ℂ} {P : BudgetPoint} (h : T.Costs z P) {Q : Rep G f} (H : T.Census Q P)
include h H










end Costs
end Story
end YM.ProofPorts.CommonComplexProduction
