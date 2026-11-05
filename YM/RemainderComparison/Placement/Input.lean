import YM.RemainderComparison.Dove.Court
import YM.RemainderComparison.Sagas.Currency
import YM.RemainderComparison.Aria.Sprig
/-!
# Input stencil positions for a substantive MARK test

Each LOG Mark type receives a port at its issuance root on the fine lattice.
Use ordinary powers of the *unscaled* curvature quadrupoles, no inverse g
funded at payload. Budget over arbitrary alpha can test marked amplitudes jointly.
General calibrator/re-entry Curtain retains its OWN pricing. Later Shape obligations
will inspect these literal supports and masks even under changing appointment epochs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Placement
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus Sienna Fare
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
open AnalyticBridge VerifiedReset Next.Scheduling Extra.Iteration Song
variable {G : Gauge} {f L: Side} {P:Teller G} {q e j:ℕ}
variable {ι:Type}{α:Type*}{A:ℝ}

/-- The same cover-based input at each mark, for arbitrary stencil rank and a
    declared shape length. In this example the radius budget can be constant, since
    we do not sum over increasing cardinality of input stencils or normalize here.
    For Ω give all α-tests *before* AP receipts. -/
structure Tile (G:Gauge)(α:Type*) (q e:ℕ)(A:ℝ) where
   stamp : α→ RG.Atom G q
   bound : ∀ a,(stamp a).magnitude ≤ A
   length : ∀ a,(stamp a).length ≤ e
   gauge : ∀ a,(stamp a).Invariant

namespace Tile
variable (D:Tile G α q e A) (u:Site f)(a:α)
set_option quotPrecheck false
local notation "Aa"=> D.stamp a

def aperture (u:Site f)(e:ℕ): RegularAddress f:=⟨u,neighbors e u,(neighbors_mem ..).mpr (by rw [separation_self]; omega)⟩
local notation "S" x:max=> aperture x e

def read (V:Config G f):= (D.stamp a).unmasked V u
lemma slotLength (s:RG.Slot)(i:Site f) (h:i∈Wages.walkCuts s u) : i∈ neighbors s.length u:=by
   rw [neighbors_mem,separation_comm]; exact VerifiedReset.slot_length s u h
lemma reach : (Aa).footprint u⊆neighbors e u:=by
   intro y hy; obtain ⟨z,ht,rfl⟩:=Finset.mem_image.mp hy
   rcases mem_insert.mp ht with hh|ht
   · subst z; simp [neighbors_mem]
   obtain ⟨i,_,hk⟩:=mem_biUnion.mp ht
   rw [neighbors_mem]; exact ((neighbors_mem ..).mp (Tile.slotLength u ((Aa).leg i) _ (mem_image_of_mem _ hk))).trans ((Finset.single_le_sum (fun i _=> Nat.zero_le ((Aa).leg i).length) (Finset.mem_univ _)).trans (D.length a))
lemma position {x z:Site f} {r s:ℕ} (hr:r ≤ s)(h:z ∈ neighbors r x): z∈ neighbors s x:=(neighbors_mem ..).2 (((neighbors_mem ..).1 h).trans hr)
-- Build packet.Bus from one atom on a seat at root (D independent of θ)
variable (v:α)
include D v in
lemma funds : 0 ≤ A:=by
   refine le_trans ?_ (D.bound v); unfold RG.Atom.magnitude; positivity
structure Ready (R:Rep G f) (j:ℕ) : Prop where
    address : R.activities.reg j=S u
    ink : R.activities.E j=0

-- avoid inverse-g cast in numerical funding.L Symbol 
def script (v:α): Sagas.Packet G f α:=by
   let x : Seat f:=(1,u)
   refine {rank := q
           grade := q
           length := e
           weight := A
           terms := 1
           data := fun a _ => D.stamp a
           stage := fun _ => rfl
           seat := fun _=> x
           postage := S u
           travels := fun a _=> ?_
           suspension := Tile.funds D v
           ample := fun a _=> D.length a
           allot := fun a=> by simpa using D.bound a
           invariants := fun a _=> D.gauge a }
   intro y hy; obtain ⟨i,hi,rfl⟩:= Finset.mem_image.mp hy
   change affine 1 u i ∈ _; change _∈ neighbors e u
   rw [show neighbors e u= neighbors e (affine 1 u 0) from by simp [Lattice.affine], Turn.circle_wind]; exact mem_image_of_mem (affine 1 u) (Tile.reach D (0:Site f) a hi)

lemma translated (x y:Site f) (U:Config G f): Tile.read D y a (pull 1 x U)=Tile.read D (affine 1 x y) a U:=by unfold read RG.Atom.unmasked RG.Slot.atSite; simp_rw [expandAt_pull]; rw [Lattice.pull_one]; rw [show ∀ W:CoverConfig G, Lattice.translate 0 W=W from fun W=> funext fun i=> by simp [Lattice.translate] ]

variable (p:BudgetPoint)(β:ℝ)
local notation "Vx"=> Tile.script D u v
lemma writes : Sagas.Packet.grant (Vx) a= Tile.read D u a:=by
   funext Z; unfold Sagas.Packet.grant; change (∑ i:Fin 1,(Aa).unmasked (Seat.view ((1,u):Seat f) Z) 0)=_; rw [Fin.sum_univ_one]; change Tile.read D 0 _ (pull 1 u Z)=_; rw [Tile.translated]; simp [Lattice.affine]

lemma delivers (hb:0<β) : Sagas.Packet.send β (Vx) a=Tile.read D u a:=by
    unfold Sagas.Packet.send Herbal.worn
    funext Z; have h:= pow_pos (Fare.gS _ hb).1 q
    rw [Tile.writes]; change gStep β ^ q * (gStep β ^ q)⁻¹ * _=_
    rw [mul_inv_cancel₀ h.ne', one_mul]

def peso (G:Gauge)(q e:ℕ) (A:ℝ)(p:BudgetPoint):ℝ:= p.threshold^q * (Collection.turnFee p * Wages.startup G q p.power p.order * (1+(e:ℝ))^ Wages.grade q p.power p.order ) * A
lemma enumerates (hb:0<β) : Sagas.Packet.eats β (Vx) p=Tile.peso G q e A p:=by
    unfold Sagas.Packet.eats
    rw [div_eq_mul_inv,mul_pow,inv_pow]; change gStep β^q * (p.threshold^q*(gStep β^q)⁻¹) * (Collection.turnFee p * Wages.startup G q p.power p.order * (1+(e:ℝ))^ Wages.grade q p.power p.order ) * A= _
    unfold peso; have h:= (pow_pos (Fare.gS _ hb).1 q).ne'; rw [mul_left_comm (gStep β^q),mul_inv_cancel₀ h,mul_one]

end Tile
end YM.RemainderComparison.Placement
