import YM.RG05Readout.Offsets.DelayPort
import YM.RG05Readout.Offsets.Within
import YM.RG05Readout.Offsets.Null
import YM.UVExtension.Harvest.Barn
import YM.UVExtension.Flake.Hulls
/-!
# Off-center PPX invoices on the common UV family
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.UV
open YM.UVExtension UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Bid Planned.GuardedAtom Guard Motion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Roost.Factor A}
    (S:Uses X hG) (v:Keys S) {C:ℕ→ℝ}{W:Worth}(R:Legato.Bandage X C W) (d N m n:ℕ)
set_option quotPrecheck false
local notation "F₀"=> (frames G).level d
local notation "z₁"=> v N n
local notation "Φ"=> A.B.a
local notation "i₁"=> A.B.a.clock.J (m+1)
local notation "H"=> Orchard.Path S v
variable (hm:m<N)(hd:d+3≤ A.B.a.clock.J m)
local notation "a₁" => A.B.a.budget (m+1)
local notation "b₁" => A.B.a.budget m
local notation "K₁" => (ray S N n m z₁ hm).body

open Next.Free Planned.PrimaryIntegral295 PPX
include hm hd
set_option maxHeartbeats 1400000 in
lemma positions (hX:Cub.Moved R) : ∃ (T:Heading F₀)(a:ℝ),
    Pricing (localSection G d) H N n m (hol G) (Orchard.roof S v N n m hm) T a (C i₁)
      (Doors.rate (A.B.a.S.block m))
      (2*(Real.exp ((H).rep N n (m+1)).p.supportExponent*Cub.title G (A.B.a.params (m+1)))) ∧
    Push.Local.triangularPrice F₀ a ≤ C i₁:=by
    have hp:= A.B.valid.pays m
    obtain ⟨a⟩:= hX _ _ hp _ d (first_le A.B.valid m) (step_paid _ m) hd
    let X₀ := K₁
    have hc : (H).Conv N n m := (Orchard.selected S v).represents N n m hm.le
    have hs:=RG05_price (jV:=(H).rep) hm R.songs R.PStage R.wait (Graces.feet hd R.clock) (housed S v) R.r X₀ beam0
      (ponds S N n m z₁ hm) rfl hc hG R.tunes R.furthering R.corners R.shape R.clock R.stamp (readC S R d N m n z₁ hd) (slots1 S N m n z₁ hm) (Keeper.sufficient (slots0 S N m n z₁ hm)) a hd
    rw [Push.PriceCompiler.block_eq A.B.valid m, Push.PriceCompiler.params_eq A.B.valid (m+1)]
    exact hs

omit hm hd

variable (F:Family G) (D:∀ N p m,m<N→GaugeDoor (F.path.rep N p (m+1)) (F.path.rep N p m))
structure Certified (W:Worth) : Prop where
    cost : ∃ (b:ℕ→ℝ),Doors.Budget F.path.levels b W ∧
       ∀ (d N p m:ℕ), ∀ (_:d+3≤ F.path.levels.clock.J m)(h:m<N), ∃ (T:Heading (F.labels.level d)) (a:ℝ),
          Pricing (F.localSection d) F.path N p m F.params (D N p m h) T a (b (F.path.levels.clock.J (m+1)))
            (Doors.rate (F.path.S.block m)) (2*(Real.exp (F.path.rep N p (m+1)).p.supportExponent*Cub.title G (F.path.levels.params (m+1)))) ∧ Push.Local.triangularPrice (F.labels.level d) a ≤ b (F.path.levels.clock.J (m+1))

lemma cellar_priced {t:ℕ→ℕ} {B:Org.Bolt A} (a:Upland.Arc X S B) (h:Lisle t A.B.a) (hx:Cub.Moved R) :
    let p:=cellar S R a t h
    Certified (Mast.Cellar.yard v p) (Orchard.roof S v) W:=by
    intro p
    exact ⟨C,R.clock, fun d N n m h hm=> positions S v R d N m n hm h hx⟩
end YM.RG05Readout.UV
