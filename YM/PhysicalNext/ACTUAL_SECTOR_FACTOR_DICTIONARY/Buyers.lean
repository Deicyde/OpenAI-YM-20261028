import Mathlib.RingTheory.Nilpotent.Exp
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Score
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Casting



/-!
# Local Income, with same Seen for Extra entries

Earn charges on each factor w.r.t the *same Z & y*, with joint lease on
Z endpoints including those used already by the bulk component & K's.
Mortgage from these already-verified multiplier theorems on one (local)
marginal; then transfer to Cards and Hers costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Hotel
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.Push.SectorMeasure
open Wires Geo Notify Shipment  Lobbies SectorNext.Reconnect SectorNext.Reconnect.Fleet
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art I D) (h : Lit D) (F : Forest S.ratio)
    (k₀ k : S.Choices) (V : Config G c) (s : ℝ) (i : Ensign S I)
    (hp : privilege D Z F V i)
local notation "A"=>Route.patch D.betaHat V (Shipment.station i)
local notation "K"=> Shipment.key D Z i
local notation "H₀"=>chosen D F k₀ A k
local notation "L₀"=>stars D F k₀
local notation "P"=>Native.kinetic D.tube F k₀ D.betaHat
local notation "N"=>Route.Badge.offer D F P A k K h.toApp
local notation "H"=>theater D Z h F k₀ V

abbrev Actors := Route.Badge.Person D F A K
abbrev Crowd := Notice.Component G ((K).Hues D F A) ((K).Cool D F A)
abbrev Guests := Casting.Alien (D:=D) («A» :=A) (a:=i) (F:=F)
abbrev Titles := ↥(Lobbies.paper D i A F)
abbrev Options := ↥(Lobbies.everyday i)

abbrev cast : Casting D Z i F A := Casting.crew h F V i k hp
abbrev forAll := showtime D Z s h (cast D Z h F k V i hp) k₀ k
abbrev original := Casting.port (cast D Z h F k V i hp) k₀ k h s

local notation "Q"=> original D Z h F k₀ k V s i hp
local notation "C"=>Crowd D Z F V i
local notation "X"=>Actors D Z F V i
local notation "Y"=>Guests D F V i
local notation "R"=>Titles D F V i

-- Core *can* be all purchased rows, never the unpurchased ones. We will
-- also demonstrate portability of the actual retained wide prerequisites.


abbrev seats (i : Ensign S I) := (Fleet.addSet i).toRight.toRight
abbrev Escorts := (↥(seats i)) ⊕ ↥(kSet i\(vacuum i))

def attendants : Escorts i ↪ Bill S I := ⟨Sum.elim (fun i=>suggest (.inr (.inr i.val))) (fun j=>known j.val),by
    rintro (i|i) (j|j) h <;> simp only [suggest,known,Sum.elim_inl,Sum.elim_inr,Sum.inr.injEq,Sum.inl.injEq,
      reduceCtorEq, Subtype.val_inj] at h ⊢ <;> first|exact h|exact h.elim⟩
local notation "T"=>Tariff
local notation "O"=>Options i
local notation "E"=>Escorts i
local notation "D0"=>forAll D Z h F k₀ k V s i hp

def avatar (W : Config G c) (l : E) (p : X) : ℝ :=
    ‖shutter D Z s (attendants i l) i F A (kSet i) k W ((K).embed D F A p)‖

def farther := Casting.tax D Z s k V F A i ∘ (K).embed D F A



-- Equivalent joint multiplier using accepted Lease calculus with one
-- portal per extra raw requirement on this SAME component.
def deposits : Varying (Y⊕E) R O (X) :=
  ⟨Sum.elim ((D0).marked V).first (avatar D Z F k V s i V),((D0).marked V).kept,((D0).marked V).optional⟩

local notation "fees"=> deposits D Z h F k₀ k V s i hp



/-- The analytic sales inputs. This formulation allows joint discounted
portals on additional entries as well, from per-entry costs ONLY. λ area
shared with other letters, never two stakes from the same witnesses. -/
structure Inputs (b : T (Y⊕E) R O (C)) : Prop where
  -- pane intrinsic even on unused Extensions w.Clear (derived below)
  bought : Peak ((N).C V) b.capacity
  leased : b.Lease
  owns (t : R) : t∈b.core → ∃ q:RowPosts c f,t.val=Voice.Legend.row q
  price p : (D0).HeldAt V p → (farther D Z F k V s i p≠0) → Tariff.Earn fees p b p.2



include hp
 
end YM.PhysicalNext.Dictionary.Hotel
