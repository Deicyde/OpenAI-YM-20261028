import YM.MultiNext.VACUUM_STABILITY.Arrival.Through
import YM.MultiNext.VACUUM_STABILITY.Component.Pasture
import YM.MultiNext.VACUUM_STABILITY.Gaussian.Seam
import YM.MultiNext.VACUUM_STABILITY.Tune.Canonical
import YM.Next.BOUNDARY.Stage
import YM.Next.FLUCTUATIONS.Kernel
import YM.Work.A05
import YM.Work.B16
import YM.Work.B18


set_option warningAsError false

/-!
# One explicit upstream route to `Flow.crossing`

At actual `Store` cell sums/Allocation. Expose earlier occurrence-level integrity
(incl Jacobian and factor ABI, absolute budgets). Use factorization of the SINGLE centered
Gaussian on disjoint argument supports under full projected covariance identities.
Measurable factors, not differentiating flags or relying on independent events. Does not
construct either the density Jacobian or the cluster choices (incl if distinct Stores need
distinct b's). They are tasked upstream. Keep absolute integrability throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Component.Earlier
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture
open Arrival Arrival.Flock Tune Gauss Tree YM.Push.SectorMeasure Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I J V : Type} {G : Gauge} {n p : Side}

/-- Pre-integration coordinates take independent customers and a Gaussian (independence
    BEFORE applying the actual z-law transformation, not after). A primitive integrand is
    that of a sector *before* splitting into incompatible-component contributions.
    Work done per V, input Voucher, original sector. All maps/canonicalizers giving these
    formulas to agree on actual terminal P,B. -/
structure Transform (I : Type) where
  key : Type
  N : ℕ
  [ms : MeasurableSpace key]
  prior : @Measure key ms
  [probability : IsProbabilityMeasure prior]
  effect : Finset I → key × Row (Fin N) → ℂ
  init : key × Row (Fin N) → ℂ

namespace Transform
variable (D : Transform I)
instance frame : MeasurableSpace D.key := D.ms
instance actual : IsProbabilityMeasure D.prior := D.probability

def common := D.prior.prod (standard (Fin D.N))

/-- Earlier analyses: census-integrability, pointwise dictionary equality on the transformed
    coordinates *before grouping* and reorientation, etc. Fix with the actual change of
    slots given by Gaussian-sector producer (`D.init` uses those *before* dropping
    background factors!). All assertions per given V/input operand, no uniqueness of D.
-/
structure Legal (x : ℂ) : Prop where
  fee : Integrable D.init D.common
  full : x=∫ t,D.init t ∂D.common
  point : ∀ᵐ a ∂D.common,D.init a=∑' b,D.effect b a
  bills i : Integrable (D.effect i) D.common
  insured : Summable (fun i=> ∫ t, ‖D.effect i t‖ ∂D.common)

def audited (b : Finset I) := ∫ x,D.effect b x ∂D.common



/-- Independent *arguments* in one valid occurrence. Derived from using all physical
read addresses in overlap. `slot i`: product Haar and tags may be represented as one
probability space and split from the actual physical sites (need construct material record).
Gram identity enforced on the actual global standard map against local conditional maps.
Individual integration requirements used by other consumers may wish to require more than
need for Fubini here (if e.g. quoting individual densities as valid). -/
structure Closes (b : Finset I) (J : Type) [Fintype J] (w : J→ℂ) (c : ℂ) where
  slot (i : J) : Type
  [uses : ∀ i, MeasurableSpace (slot i)]
  cut (i) : Measure (slot i)
  [bought : ∀ i, IsProbabilityMeasure (cut i)]
  project (x : D.key) (i : J) : slot i
  distributes : MeasurePreserving project D.prior (Measure.pi cut)
  slots : ℕ
  space : ℕ
  core (i) : slot i → Row (Fin slots) → ℂ
  summed (x : D.key) : J → Fin slots → Row (Fin D.N)
  own (i : J) : slot i → Fin slots → Row (Fin space)
  scatter i x : Measurable (core i x)
  earned i : Measurable (fun x => ∫ y,core i x (mapRows (own i x) y) ∂standard (Fin space))
  word i : w i=∫ x, ∫ y,core i x (mapRows (own i x) y) ∂standard (Fin space) ∂cut i
  agreement x : blocksMatch (summed x) (fun i => own i (project x i))
  identity x y : D.effect b (x,y)= c * ∏ i,core i (project x i) (mapRows (summed x i) y)

namespace Closes
variable {D} {b : Finset I} [Fintype J] {w : J→ℂ} {c : ℂ} (H : D.Closes b J w c)

include H in
lemma entitled (h : Integrable (D.effect b) D.common) : D.audited b = c * ∏ i,w i := by
  letI (j : J) := H.uses j; letI (j : J) := H.bought j
  let f (i : J) (x : H.slot i) := ∫ y,H.core i x (mapRows (H.own i x) y) ∂standard (Fin H.space)
  have he (x : D.key) : ∫ y,D.effect b (x,y) ∂standard (Fin D.N) = c * ∏ i,f i (H.project x i) := by
    simp_rw [H.identity,integral_const_mul]; congr 1
    exact Gauss.bills _ _ (H.agreement x) (fun i => H.core i (H.project x i)) (fun i=>H.scatter _ _)
  unfold audited common
  rw [integral_prod _ h]; simp_rw [he,integral_const_mul]
  congr 1
  let g (x : (i : J) → H.slot i) := ∏ i,f i (x i)
  have hm : Measurable g := Finset.measurable_fun_prod _ fun i _=> (H.earned i).comp (measurable_pi_apply _)
  change (∫ x,g (H.project x) ∂D.prior)=_
  rw [← integral_map (f:=g) H.distributes.measurable.aemeasurable hm.aestronglyMeasurable,H.distributes.map_eq]; unfold g
  rw [integral_fintype_prod_eq_prod]; exact prod_congr rfl fun i _ => (H.word i).symm
end Closes
end Transform

variable {B : Brush V G n} [Fintype V]
variable (S : StepData n p) (Y : Forest S.ratio) {x W : ℝ} (D : Allocation G S x W) (F : Flock V G p) (Q : Rep G p)
    (P : BudgetPoint) (A : Pasture I B) (back : Finset I→Voucher F)

/-- Inputs on these choices. Each Y coordinate and Store counted with chosen D normalizations.
Branches represented independently of z through unscaled operands. A physical Jacobian
implementation should check `legal`, `sticker`, `closes` on its transformations (not new
slots chosen to factor an isolated answer). In particular address variants with one
choice in one `store` must not secretly contribute only a term which changes upon summing
another component across sectors/new b. -/
structure Tolls where
  data (a : Stores S) (b : Voucher F) (U : Config G n) : Transform I
  legal (a : Stores S) (b : Voucher F) (U : Config G n) : (data a b U).Legal (output D Y Q.beta (F.peelRow Q b) a U)
  store (i : Finset I) : Stores S
  pinpoint (a : Stores S) (b : Voucher F) (U : Config G n) (i : Finset I) : a ≠ store i ∨ b ≠ back i →
    let D := data a b U; D.effect i =ᵐ[D.common] 0
  closes (b : Finset I) (U : Config G n) : let d := data (store b) (back b) U
    ((d.effect b =ᵐ[d.common] 0) ∧ A.view P U 1 b = 0) ∨
    ∃ s, valid (B:=B) (flags P.threshold U) s ∧ A.recovers s b ∧
      Nonempty (d.Closes b (↥s) (fun i => consumes B P U 1 i) (B.base U))

namespace Tolls
variable {S Y D F Q P A back}




end Tolls
end YM.Multi.Vacuum.Component.Earlier
