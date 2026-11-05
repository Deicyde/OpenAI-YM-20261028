import YM.Further.STRONG_STARTUP_CREDIT.Pricing


set_option warningAsError false

/-!
# Oust and stronger startup, on the SAME B

These statements are both directly on the actual startup rep before
asking for Kin.Planned etc, and on B's for which it is the approved
startup. Always use the WilsonStartup top path (the alternative
*local* prescription). We pay all p/N from prepriced inputs. A
consumer can use e.g. `rapid` AND the Oust field on the B selected by
`selecting`. Don't assume arbitrary Gate choices just pass or replace
the selected B later. `Advancing` remains an **input**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.StrongStartup
open Filter Function Lattice Wilson RG RG.Shoot Source WilsonStartup WilsonStartup.Start Precision Pressure
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Supply.Sheet G} {D : Supply.Rolls C} {Z : Supply.Protection D} {V : Supply.Delays Z}
    {Y : Supply.Bar V} {I : Supply.Wait Y} {F : Labels.Frames G}

/-- Full countable reserve on the actual addressed vacuum; these numbered
unused addresses are free even at the expanded payments. For any footprints
with allowed nonempty inventory etc. Exact predicates kept. -/
structure Dormant {n : Side} (R : Rep G n) (f : ℕ → ℝ) : Prop where
  blank : Injective (fun p : Blank n × ℕ => reserveE p.1 p.2)
  forced : Injective (fun p : Foot n × ℕ => reserveK G p.1 p.2)
  e (q : Blank n) j : let A := R.activities; let x := reserveE q j
    (A.reg x).site=q.val.1 ∧ (A.reg x).support=q.val.2 ∧ A.E x=0
  k (q : Foot n) j : let A := R.activities; let x := reserveK G q j; let a := A.forced x
    a.support=q.val.1 ∧ a.inventory=q.val.2 ∧ (∀ U,a.eligible R.p.threshold U ↔ q.val.1 ∩ flags R.p.threshold U=q.val.2) ∧
      A.K x=0 ∧ f x=0



structure Bill (A : Levels G) (T : Tariffs) (N p : ℕ) : Prop where
  rates : Escrow A N (T.extra (A.clock.J N)) (T.nonnegative _)
  bonds : BondFuel A N (T.rim (A.clock.J N))
  stable : Curve (stretch (A.budget N) (T.extra (A.clock.J N)) (T.nonnegative _)) (layout A N p) (band A N)
  valid : ∀ β∈ band A N, let R := layout A N p β; let e := T.extra (A.clock.J N)
    (R.v=0 ∧ R.eval = bare R.beta ∧ R.beta=β ∧ Wide R ∧ Dormant R (topPrice A N p)) ∧
      R.activities.Valid (stretch R.p e (T.nonnegative _)) (A.clock.allowance N) (grant A N) ∧
      (∀ i, 0 ≤ topPrice A N p i ∧ ∀ U, ‖R.activities.K i U‖ ≤ topPrice A N p i) ∧
      Ac.Hit (fun i => (R.activities.forced i).support) R.p.B (topPrice A N p) (R.p.supportExponent+e+1) (grant A N)





open Input
variable {O : ChartRatio G} {K : MapPrices} {Q : PostCost D}
structure Opening (B : Directed G I O K Q) (T : Tariffs) : Prop where
  bids : ∀ N p, Bill B.a T N p
  alone : ∀ N p u, B.bake.first N p u → u = layout B.a N p u.beta
  oven : ∀ N p, Bid.Oust B N p

variable {B : Directed G I O K Q} {T : Tariffs}
















end YM.Further.StrongStartup
