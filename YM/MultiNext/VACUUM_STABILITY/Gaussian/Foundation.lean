import YM.MultiNext.VACUUM_STABILITY.Gaussian.Under
import YM.MultiNext.VACUUM_STABILITY.Tune.Canonical
import YM.Next.BOUNDARY.Stage

set_option warningAsError false

/-!
# ProductCost from **actual representation** chart integrals with pointwise data

At output letters of the ACTUAL first-system computation with the committed
Gaussian/tags/frozen Haar strategies, be it conditioning before holding or after. Need align
these charts with pre-integration reindexing on `Flow`. No budget after integration assumed.
`Swaps` typically exact Jacobian on local patch at the evaluated U. Verifies `ProductCost`
from pointwise charges in those SAME integrals; doesn't let a new conditional law be chosen in
the middle of each rarity estimate, no hypothesis on ∞-jets of a thresholded factor.
Still need local pointwise bounds and geometric change-of-variable & eligibility.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Gauss
open RG Lattice Wilson Filter Finset Function MeasureTheory ProbabilityTheory Text Cluster Desk Component Puff Stamp
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {U : Config G n}

/-- One cylinder integration occurrence (ambient chart at fixed U). If changing coordinates,
`backTo`, `gain` give parameter-domain & measure conversion. Use this on SAME coefficient,
formed at output by actual Flow. If keeping a set, all derivative score integrands belong
inside it. Recomputed on the same drape. finite I (output link-Lie variables counted), possibly
combining packet trigger events. -/
structure Theater where
  place : Type
  [ms : MeasurableSpace place]
  fixed : @Measure place ms
  enclave : Set place
  group : Type
  [setup : MeasurableSpace group]
  prior : @Measure group setup
  [normed : @IsProbabilityMeasure group setup prior]
  I : ℕ
  J : ℕ
  -- same centred conditional normal law with generated matrix depending on tags/group,
  -- not requiring a global split in Z in any integral. `K` channels in pointwise bound
  -- use only the required marginal.
  q : group → Fin I → Row (Fin J)
  backTo : group → Row (Fin J) → place
  gain : group → Row (Fin J) → ℝ
  gain_pos i y : 0 ≤ gain i y

namespace Theater
variable (T : Theater)

instance placeMs : MeasurableSpace T.place := T.ms
instance groupMs : MeasurableSpace T.group := T.setup
instance probability : IsProbabilityMeasure T.prior := T.normed

def roll (f : T.place→ℂ) (i : T.group) (y : Row (Fin T.J)) := T.gain i y • f (T.backTo i y)

structure Swaps : Prop where
  eq f : Integrable f T.fixed → (∀ x : T.place, f x ≠ 0 → x ∈ T.enclave) →
      ∫ a,f a ∂T.fixed = ∫ i, ∫ y,T.roll f i y ∂standard (Fin T.J) ∂T.prior

structure Affords (K H d u : ℝ) (p : ℕ) (g : T.place → ℂ) : Prop where
  tall : 1+(T.I:ℝ) ≤ H*(1+d)
  measurable i : AEStronglyMeasurable (T.roll g i) (standard (Fin T.J))
  collate : AEStronglyMeasurable (fun i => ∫ y,T.roll g i y ∂standard (Fin T.J)) T.prior
  -- if needed use measure qualifications; annulus and crushing estimates
  -- required exactly at every healthy point for smooth-system uses
  lives i : adjBound (T.q i) K ∧ ∃ (w : Row (Fin T.I)) (W c b : ℝ) (S : Finset (Fin T.I)),
      (∀ i,0≤w i ∧ K*w i ≤ 1/8) ∧ ∑ i,w i ≤ W ∧ 0 ≤ c ∧ c * Real.exp (-coin K*b + 2*K*(W+S.card*coin K)) ≤ u ∧
      ∀ᵐ y ∂standard (Fin T.J), T.roll g i y≠0 →
        let z:=mapRows (T.q i) y
        ‖T.roll g i y‖ ≤ c*(1+squares z)^p * Real.exp (pay w z) ∧ b ≤ ∑ i∈S,z i ^2

lemma procured {K H d u : ℝ} {p : ℕ} {f : T.place → ℂ} {x : ℂ} (h : x=∫ a,f a ∂T.fixed)
    (hT : T.Swaps) (hf : T.Affords K H d u p f) (hv : Integrable f T.fixed) (hg : ∀ i, f i≠0 → i∈T.enclave) :
    Nonempty (Pays K H p d u x) := by
  refine ⟨{ fiber:=T.group, binder:=T.prior, I:=T.I, J:=T.J, chart:=T.roll f, body:=hf.tall
            writes:=hf.collate,line:=h.trans (hT.eq f hv hg),earns:=?_ }⟩
  intro i; obtain ⟨hh,w,W,c,e,K,H⟩:=hf.lives i
  exact ⟨hf.measurable _,T.q i,w,W,c,e,K,hh,H⟩
end Theater

/-- Actual computation of one regular term around U. Extension verified, chart score
return and kernel dependencies use this data. -/
structure Window (f : Config G n→ℂ) (U : Config G n) (p : ℕ) where
  stage : Theater
  core : stage.place → Config G n → ℂ
  read : Implanted stage.fixed U p core f
  Swap : stage.Swaps
  mark (l : List (Directions G n)) : l.length ≤ p → ∀ i,
      leftDerivs (core i) l U≠0 → i ∈ stage.enclave

namespace Window
variable {f : Config G n → ℂ} {k : ℕ} (s : Window f U k)

def entry (z : ℂ) (l : List (Directions G n)) := fun i => z * leftDerivs (s.core i) l U

lemma land {z : ℂ} (l) (hl : List.length l ≤ k) {K H d C : ℝ} (p) (h : s.stage.Affords K H d C p (s.entry z l)) :
    Nonempty (Pays K H p d C (leftDerivs (z • f) l U)) := by
  refine Theater.procured _ (f:=s.entry z l) ?_ s.Swap h ?_ ?_
  · rw [scaled_left,s.read.done l hl U s.read.inside]; unfold entry; rw [integral_const_mul]
  · obtain ⟨b,hb,hF,H⟩:=s.read.cuffs l hl
    exact (hb.mono' (hF _ s.read.inside) (H.mono fun j hj => hj _ s.read.inside)).const_mul _
  intro j h; exact s.mark l hl j (right_ne_zero_of_mul h)

end Window

structure Walls (f : Config G n → ℂ) (U : Config G n) where
  stage : Theater
  core : stage.place → ℂ
  Swap : stage.Swaps
  read : f U = ∫ i,core i ∂stage.fixed
  int : Integrable core stage.fixed
  mark i : core i ≠0 → i∈stage.enclave

namespace Walls
variable {f : Config G n → ℂ} (s : Walls f U)

def entry (z : ℂ) := fun i => z*s.core i
lemma land {z : ℂ} {K H d C : ℝ} (p) (h : s.stage.Affords K H d C p (s.entry z)) :
    Nonempty (Pays K H p d C (z*f U)) := by
  refine Theater.procured _ (f:=s.entry z) ?_ s.Swap h (s.int.const_mul _) fun i he => s.mark _ (right_ne_zero_of_mul he)
  unfold Walls.entry; rw [s.read,integral_const_mul]
end Walls

section grade
variable {I V : Type} {B : Brush V G n} (A : Pasture I B) (P : BudgetPoint)

/-- With the actual output stamp computations. No choosing another representative
from the cost inequality to prove existence. -/
structure Charts (B : Brush V G n) (P : BudgetPoint) where
  soft (i U) : Healthy P.threshold (B.u i).zone U → Window (B.u i).stamp.ink U P.order
  packet (i U) : Walls (B.d i).ink U

namespace Charts
variable (T : Charts B P)

include T in
lemma regular (i) (hj : LocalOn (B.u i).zone (B.u i).stamp.ink) (hm : Measurable (B.u i).stamp.ink)
    (hg : GaugeInvariant (B.u i).stamp.ink) : P.Regular (B.u i).zone (B.u i).stamp.ink := by
  -- spots include all health incl equality
  have ht U (hu) := Implanted.edge (T.soft i U hu).read
  exact ⟨hj,hm,hg,ht,fun U hu A l hl => ((into P.order _ (ht U hu)).line l hl A).hasDerivAt⟩

variable [Fintype V]

/-- Earlier score tests. In an overlap expansion, may strengthen with actual Ω and branch
 identities *there*. Keep mask, all-L/root footprint, κ on forced species. Pays point
score after held kernels etc. All uses for one vertex selection commit the data T. -/
structure Covered (z : V→ℂ) (K H C κ : ℝ) (k l : ℕ) (f : I→ℝ) : Prop where
  regular_score (i U) (hh : Healthy P.threshold (B.u i).zone U) (v : List (Directions G n)) : v.length ≤ P.order →
    (∀ a∈v,P.dirBound (B.u i).anchor a) → let W:=T.soft i U hh; W.stage.Affords K H (Live.bill A P.B (.inl i))
        (C*A.feast f k P.B (.inl i)) l (W.entry (beat (B.u i).stamp.name z) v)
  hard_score (i U) : let W := T.packet i U
                     W.stage.Affords K H (Live.bill A P.B (.inr i)) (κ*(C*A.feast f k P.B (.inr i))) l
                       (W.entry (beat (B.d i).name z))

lemma authorized {z K H C κ k l f} (h : Covered A P T z K H C κ k l f) : Live.Form A P z K H C κ k l f :=
    ⟨fun i U hu v hv ht => (T.soft i U hu).land v hv l (h.regular_score i U hu v hv ht),
     fun i U => (T.packet i U).land l (h.hard_score i U)⟩

/-- Gets all the quantitative post-integration prices from earlier estimates on actual
per-occurrence data. -/
theorem transfers (z : V→ℂ) {K H C κ} (hh : 0 ≤ K) (hH : 1 ≤ H) (hC : 0 ≤ C) {k l f} (h : Covered A P T z K H C κ k l f)
    {c r t : ℝ} (hr : 0≤r) (ht : 0≤t) (hx : Cluster.siteUnit P.B*t ≤ 1) (hf : Ac.Hit A.sites P.B f (r+2) t)
    (hd : coat K H l*C*(Component.Pasture.sizeTax (l+k)*(Real.exp t-1)) ≤ c) : A.ProductCost P z c r κ :=
    Live.open_for A _ z hh hH hC (authorized A P T h) hr ht hx hf hd
end Charts
end grade
end YM.Multi.Vacuum.Gauss
