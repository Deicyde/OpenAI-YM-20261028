import YM.Climb.Beams
import YM.Dash.Quot
import YM.Extraction.Harvest
import YM.Fields.Tall
import YM.Overlay.Assembly
import YM.Phase.Square
import YM.Spec.Closed






/-!
# Building through extraction; input mission

INTERSECTIONS in single existence obligations because choices COULD otherwise
be incompatible.

A schedule chosen merely for getting Metered needn't work
for producing any further UV hypotheses.

A representation packing addresses for
λ-orders may need SPECIFIC choices from bake/tapes produced in History campaign.

Distinguish simultaneous input mission (YU) from conditional continuum theorems
(consumers of contextual receipts).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Org
open Function Set Filter MeasureTheory RG RG.Supply RG.Shoot Stock Input Precision Overlay Spec Table
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

/-- Stage before choice of *any* block ratios. Can include future pre-L
constants in floors. -/
structure Metals (G : Gauge) where
  p : Sheet G
  K : MapPrices
  O : ChartRatio G
  oga : LocalRatio O

/-- Θ & waits *after* L (L entire list still respecting support order).

Do not chase flags using
path approximations of different instances. -/
structure Alloy {G : Gauge} (M : Metals G) (D : Rolls M.p) where
  post : PostCost D
  θ : Protection D
  delay : Delays θ
  bar : Bar delay
  asks : Wait bar
  prices : Priced delay
  B : Directed G asks M.O M.K post
variable {G : Gauge} {M : Metals G} {D : Rolls M.p} {A : Alloy M D}

structure Bolt (A : Alloy M D) where
  program : A.B.Program
  history : ℕ → ∀ i, Trail A.B.a i
  sticks : A.B.bake.Stays history
  choice : (A.B.bake.make history).Selected
  moves N m p : m < N → A.B.Move N m p (history N p m) (history N p (m+1))

structure Assembly (B : Bolt A) (C : Family G) : Prop where
  imported : C.path=A.B.bake.make B.history
  metered : Metered C  

lemma winning (h : G.Simple) (P : A.B.Program) : Nonempty (Bolt A) := by
  obtain ⟨T,hT,hW,H⟩ := A.B.holding h P
  exact ⟨⟨P,T,hT,hW,H⟩⟩
namespace Assembly
variable {B : Bolt A} {C : Family G} (X : Assembly B C)
include X
lemma stamp : C.Makes := X.metered.stamp
lemma wcmain (h : G.Simple) : Extraction.Wcmain C :=
    X.metered.rootwise h (by rw [X.imported]; exact Stock.consumes A.B.valid A.prices)
lemma port (h : G.Simple) (f : Extraction.Order) : Extraction.CenterPort C f := (X.wcmain h).projects C f X.stamp

end Assembly

open Extraction Dash

structure Arrives (C : Family G) (F : Order) (S : Table C.book) (P : ℕ → Table C.book) : Prop where
  census : RawLimits C F S P
  born : Live S
  pin : ∃ T : Bin S, Spans born T F

variable {C : Family G} {F : Order} {S T : Table C.book} {P : ℕ → Table C.book}

structure Cleaner (S : Table C.book) (P : ℕ → Table C.book) (T : Table C.book) (W : DiffPlan T) (F : Order) : Prop where
  sharp : matchReg S T
  mesh : RawLimits C F T P
  basic : T.Basic
  smooth : T.Smooth
  ready : W.Inclusions T
  tilt : W.Derivatives T

namespace Arrives
variable (H : Arrives C F S P)
include H
lemma serves (h : C.Makes) (h' : CenterPort C F) : ∃ T : Table C.book,∃ W : DiffPlan T, Cleaner S P T W F := by
  obtain ⟨R,hR⟩ := H.pin
  obtain ⟨Y,hY⟩ := lifts_model H.born H.census.integral R hR
  obtain ⟨T,ht,hT⟩ := awake S H.born H.census.regular hY.through_ties
  have hx := H.census.ready (Around.size_done h (h'.book _ _)) hT fun n w x hx => (ht _ _ hx).symm
  have hb := Extraction.Order.limits_basic h hT (f:=F) ⟨P,hx.mesh,hx.volume⟩
  have hv : Live T := fun n v t => Test.smearing t (T.smooth_read hT v).continuousOn
  have hi := sameWake (p := hv) ht hY
  exact ⟨T,Y.descends hv hi hT hb.toSymmetric,ht,hx,hb,hT,Y.readies hi hT hb.toSymmetric,Y.tilts hi hT hb.toSymmetric⟩
end Arrives

variable {W : DiffPlan T}
lemma Cleaner.stay (h : C.Makes) (X : Cleaner S P T W F) (hx : T.Capped) : T.Hierarchy :=
    Extraction.Order.assembles X.mesh.integral ⟨P,X.mesh.mesh,X.mesh.volume⟩ h X.smooth hx

open OS Climb

/-- arbitrarily fine GRID anti approximants . This is weaker in requested
operations (anti pairs alone), requires genuine all fine h clusters for
h's indicated (cofinal per weight).  text, implementation issue in dossier. -/
def Grill (C : Family G) (F : Order) := ∀ d m : ℕ, ∃ k : ℕ, m≤k ∧ ∀ n : ℕ, ∀ v : Fin n → C.book.Token,
    (∀ i,(v i).fst ≤ d) → Grid.plain (C := C) v → ∀ x : Fin n→ Lattice.Cover, Order.grid C k x ∈ generic n →
    ∃ P : Grid.Covering (C:=C) k v x, Grid.Covering.Works k v x P F

/-- Defect parameter type, uses actual map labels. -/
def orients (k : Signed) (u : Ortho.Skew) : Ortho.Skew :=
  ⟨k.ortho.val*u.val*star k.ortho.val,by
    change star _ = -_
    have H : star u.val= -u.val:=u.property
    simp only [star_mul,star_star,H,neg_mul,← mul_assoc,mul_neg]⟩

def bracket (u v : Ortho.Skew) : Ortho.Skew := ⟨u.val*v.val-v.val*u.val,by
    change star _ = -_
    have h : star u.val= -u.val:=u.property
    have H : star v.val= -v.val:=v.property
    rw [star_sub,star_mul,star_mul,h,H,neg_mul_neg,neg_mul_neg,neg_sub]⟩

abbrev Two {L : Register G} (S : Table L) (d : ℕ) := Ortho.Skew→ₗ[ℝ] Ortho.Skew→ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)

/-- whole finite-level family, not enough mark just K label J -/
structure Winds {L : Register G} {S : Table L} (H : S.RealSpin) (P : DiffPlan S) (d : ℕ) (T : Two S d) : Prop where
  polar (g : Signed) : g.matrix.det = 1 → ∀ u v x, S.mirror H d g (T u v x)= T (orients g u) (orients g v) (S.mirror H d g x)
  real u v x : S.conj H d (T u v x)= T u v (S.conj H d x)
  unit u v : T u v (S.unit d)=0
  alt u : T u u=0
  rises (k : ℕ) (hv : k ≤ d) u v x : T u v (P.rise hv x)∈LinearMap.range (P.rise hv)

/-- Vanishing Ward kernel internal test . -/
def erases {L : Register G} {S : Table L} (H : S.RealSpin) (P : DiffPlan S) : Prop :=
    ∃ n : ℕ, ∀ d ≥ n,∀ T : Two S d, Winds H P d T →
      (∀ (m : ℕ) (x : Points m), x∈conf _ → ∀ u v (w : Fin m→S.Field d),
        (∑ i, Ward.disc (Function.update (Climb.column w) i (⟨d,T u v (w i)⟩ : S.Tag)) x)=0) → T=0

/-- Lighthouse calibrated to (same) Maxwell weak/stress output,
including REQUIRED readiness for matrix classification & internal
identification. Not proven. Use that exact E-normalized choice below,
not ANY fake stress. τ folded into chosen J.
`Cuts` embedded. Includes internal rows. -/
structure MaxwellData (C : Family G) where
  T : Lighthouse C.book
  hT : Table.Hierarchy (Bel C.book)
  lit : T.Goes C.book hT.spin
  vacuum : Boundary.Spins (Bel C.book)
  rolls : vacuum.Descends T.K hT.spin
  -- Casimir polynomial half
  optic : _root_.YM.Spin.rel T.K.lie
  marks (d : ℕ) : ∃ z : List ℝ, _root_.YM.Spin.Works z (_root_.YM.Spin.attach T.K d)
  -- free internal row kernel (still an actual free obligation, with G.Simple;
  -- not obtained from cuts, which tests vector-map rows).
  frames : erases hT.spin T.W

structure IR (S : Table C.book) where
  J : S.Stress -- unnormalized
  p : Climb.Parts S
  Y : Ward.SpinRows S

structure UV (C : Family G) (F : Order) (S : Table C.book) (W : DiffPlan S) (T₀ : MaxwellData C) (I : IR (C:=C) S) : Prop where
  -- Cap producer (already after matchReg). Doesn't require IR/Phase. Seed.
  basis : Seed C F S
  aligned : W.Orientation basis.kernel.spin
  -- factory production of weak systems. No *uniform in N* in Track at continuum.
  -- In implementation will need deeper marker etc A charges proving both this and widths.
  planet : Climb.Pre basis.kernel W I.J I.p I.Y
  weak : ActLaw W T₀.T I.J basis.kernel.spin T₀.hT.spin
  -- grid input
  tables : Grill C F

/-- YU input mission (one combined producer, not a ticket). Red ledger breaks
it vertically *through these witnesses* plus Roof allowances/waits.
We use universal L satisfying floors & Large; if instead *need*
interdependence on previous ratios (identify precisely) this mission needs
redesign -- keystone gate; don't first freeze A then pretend can select L
for the estimates. `Arrives` used on f itself (can be a fine/period refinement
of that produced in crops proof). -/
def YU : Prop := ∀ (G : Gauge), G.Simple → ∃ M : Metals G, ∀ D : Rolls M.p,
    ∃ (A : Alloy M D) (B : Bolt A) (C : Family G), Assembly B C ∧
    ∃ (F : Order) (S₀ : Table C.book) (P : ℕ → Table C.book), Arrives C F S₀ P ∧
    ∃ (S : Table C.book) (W : DiffPlan S), Cleaner S₀ P S W F ∧
    ∃ (T₀ : MaxwellData C) (I : IR (C:=C) S), UV C F S W T₀ I
end YM.Org
