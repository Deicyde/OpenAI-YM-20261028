import YM.FullVolume.Gables.Crown
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}(hG:G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) {Y:Bolt A}
open YM.MergeProof
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
open RG.Shoot Lark Rain Blush Motion FullVolume.Shadow
variable {N p k r d:ℕ}{q:ℕ→∀ p,Shoot.Trail A.B.a p}
variable {D:∀ m,Desk G (A.B.a.S.side m p)} (hz:Nest X Y)(hc:∀ i,Boutique.Feeling A i p (D i))(hR:k ≤ r)(ht:d+3≤A.B.a.clock.J r)(B':Branch X q N p k)
open Boutique
set_option quotPrecheck false
local notation "F"=> (Labels.frames G).level d
local notation "H"=> A.B.bake.make q
namespace Branch
variable (V : TransferData ((Labels.frames G).level d) (A.B.bake.make q) N p)(hv:∀ h:r≤N, Piano b B' hc hR ht V h)
include b hc B' hR ht hv
def arrive (m:ℕ) (h:r ≤ m) (hx:m≤ N) := reading b hc hR ht B' m h hx ((hv (h.trans hx)).choose_spec)
def cargo (m:ℕ) : Gram ((Labels.frames G).level d) (hol G) (D m) (A.B.a.params m).columns := if h:r ≤ m ∧ m≤ N then arrive b hc hR ht B' V hv m h.1 h.2 else gramZero F (hol G) (D m) (zero_le_one.trans (A.B.a.params m).columns_ge)
variable (m:ℕ)(hm:r ≤ m)(hx:m≤N)
local notation "Q"=> cargo b hc hR ht B' V hv m
local notation "R₁"=> cargo b hc hR ht B' V hv (m+1)
include hm hx
lemma trim : Q=arrive b hc hR ht B' V hv m hm hx:=dif_pos ⟨hm,hx⟩
lemma capitals (x:(F).Coeff): Coin.uses ((Q).g (V.entries m x).x)= capture (V.entries m x) (Keeper.sufficient (B'.slots m (hR.trans hm) hx)):= by
    rw [trim b hc hR ht B' V hv m hm hx]; let S:=(hv (hm.trans hx)).choose; have ht':= (hv (hm.trans hx)).choose_spec
    have hb:= B'.sungAt b hc hR ht m hm hx ht'
    let K:= Keeper.sufficient (B'.slots m (hR.trans hm) hx)
    let hB:= B'.notices hc (hR.trans hm) hx; have he (x): V.entries m x=(S.tone m).plays x:=by rw [ht'.2.1]; rfl
    rw [he,hb.currents x]; let y:= (S.tone m).index; exact (notations hb K hB (y x)).trans ((congr_arg (fun v:(F).Coeff=> capture ((S.tone m).plays v) K) (y.symm_apply_apply x)))
omit hx
include hG hz
local notation "P'"=> tuition hG b hz hc hR ht B' m hm
lemma tallies (he:m<N) : Q=(P').flow R₁ ∧ ∀ x,(V.entries m x).x=(P').leanings R₁ (V.entries (m+1) x|>.x):=by rw [trim b hc hR ht B' V hv m hm he.le,trim b hc hR ht B' V hv (m+1) (hm.trans m.le_succ) he]; exact B'.veering hG b hz hc hR ht m hm he (hv (hm.trans he.le)|>.choose_spec)
end Branch
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.tallies
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.capitals
