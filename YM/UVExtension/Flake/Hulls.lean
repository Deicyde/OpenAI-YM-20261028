import YM.UVExtension.Flake.Plaza
import YM.UVExtension.Crown.Tab
import YM.UVExtension.Rainfall.Planet
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Flake
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Fitted
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ)(b:Shade)
set_option quotPrecheck false
local notation "H"=> S.fits N n
local notation "V"=> S.cart N n
local notation "τ"=> S.grove.coins
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "J₀"=> A.B.a.clock.J m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Δ"=> P.L J
set_option quotPrecheck false
abbrev cumulus (b:Shade):= (S.fits N n).courseA (S.cart N n) S.grove.coins m b.val
noncomputable def wakeB (m:ℕ): History G:= History.mk A.B.a (fun N n=> cumulus S N m n b)
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)
local notation "X!"=> (H).zoomH V (S.token N n) τ m hm.le m le_rfl hm b
abbrev duetB := X!
noncomputable abbrev onB := (H|>.zoomK V (S.token N n) τ m hm.le m le_rfl hm b).some
local notation "X0"=> (cumulus S N m n b) m
local notation "X1"=> (cumulus S N m n b) (m+1)
local notation "φ"=> H.sprig
include hm
lemma fairs (Q: duetB S N m n b hm): (cumulus S N m n b) m = Q.body.result beam0:= (((H).sprig V (S.token N n) τ m hm.le b).passes m le_rfl hm).trans (Q.pay beam0).symm
lemma fairer: (wakeB S b m).Conv N n m := by
   have h:=H|>.rooted (H|>.sprig V (S.token N n) τ m hm.le b); obtain ⟨h₁,h₂⟩:= h.1.prices m le_rfl hm.le; exact ⟨h₁.point,h₁.clip,h₁.valid,h₂⟩
lemma pins0 : HasSlots (X0).p (X0).activities:= (H).protector ((H).sprig (V) (S.token N n) τ m hm.le b) m le_rfl hm.le
lemma pins1 : HasSlots (X1).p (X1).activities:= (H).protector ((H).sprig (V) (S.token N n) τ m hm.le b) (m+1) m.le_succ hm
variable (Q:duetB S N m n b hm)
lemma pinsQ : HasSlots ((Q.body.result beam0).p) ((Q.body.result beam0).activities):=by rw [← fairs]; exact pins0 S N m n b hm
include hd R
omit hm in
lemma readB : Push.Local.Readable (hol G) π (A.B.a.budget (m+1)) (A.B.a.S.side (m+1) n) (title G (M.p.profile (A.B.a.clock.J (m+1)))):=by
   have hj:d ≤ J:= (by omega : d ≤ J₀).trans (step_paid A.B.a m).1
   rw [show title G (M.p.profile (J))=authors A.B.a (m+1) by unfold title authors; rw [params_eq A.B.valid] ]; exact lively R.clock hj (n:=n)
local notation "L'"=> Lacing.Banner A.B.a ((frames G).level d) (hol G) n m
local notation "hG0"=> Keeper.sufficient (pinsQ S N m n b hm Q)
local notation "hp1"=> pins1 S N m n b hm
-- check readB doesn't include hm: include hm yes def?
local notation "he1"=> readB R d m n hd
set_option maxHeartbeats 800000 in
lemma polar : ∃ a :L', Waged Q.body beam0 he1 hp1 hG0 a:=by
   exact galaLoop hm R.r Q.body beam0 (fairs ..) (show ((wakeB S b m).rep N n (m+1))=(X1) from rfl) (fairer S N m n b hm) hG R.tunes R.furthering R.clock R.stamp _ _ _ hd
open Bid Next.Free Planned.PrimaryIntegral295 PPX
local notation "w"=> C (A.B.a.clock.J (m+1))
local notation "t"=> Doors.rate Δ
omit hm
lemma vision : Blend 2 (A.B.a.budget (m+1)).threshold (A.B.a.budget m).threshold:=by
    have hF:= step_paid A.B.a m; obtain ⟨T'⟩:= R.corners _ _ (A.B.valid.pays m) (J₀) d (first_le A.B.valid m) hF hd; exact T'.scaleP _ _ rfl (Circlet.shifting (A:=A) (m:=m)).1 -- needs namespace
set_option quotPrecheck false
noncomputable def leadF: Heading ((frames G).level d):= Seal.donne π (sound G d) M.p.kernel.penalty_pos (A.B.a.clock.adm m) (Next.Foundations.valuation G d) (Warehouse.flight (Orchard.Path S (fun _ _=> Orchard.rose0 S)) N m) ((le_trans (by omega : d ≤ J₀) (step_paid A.B.a m).1)) (vision R d m hd)
include hm
set_option maxHeartbeats 1000000 in
lemma tum {a:L'} (h: Waged Q.body beam0 he1 hp1 hG0 a): let T':= leadF S R d N m hd; (∀ x, (F).coeffSize (T'.map x) ≤ w* (F).coeffSize x ∧ (F).coeffSize (T'.map.symm x)≤ w* (F).coeffSize x)∧ Tips a Δ T' t w ∧ ∀ i:(F).Index,i≠0 → sparkT Q.body beam0 (Circlet.lark (X1) i he1 hp1) d:= by
    have hh :=(housed S (fun _ _=> Orchard.rose0 S)); intro T'
    have hC : Buys (wakeB S b m) F W m w (Doors.rate (A.B.a.S.block m)):= R.clock.fits (wakeB S b m) rfl m d (by omega)
    exact palmLoop hm R.songs R.PStage R.wait (Graces.feet hd R.clock) hh R.r Q.body beam0 (fairs ..) (show ((wakeB S b m).rep N n (m+1))=(X1) from rfl) (fairer S N m n b hm) hG R.tunes R.furthering R.corners R.shape R.clock R.stamp _ _ _ h hd (zero_le_one.trans hC.cost) (vision R d m hd) (A.B.a.clock.adm m) ((le_trans (by omega : d ≤ J₀) (step_paid A.B.a m).1))
end YM.UVExtension.Flake
