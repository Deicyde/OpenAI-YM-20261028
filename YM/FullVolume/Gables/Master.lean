import YM.FullVolume.Gables.Pole
import YM.FullVolume.Gables.Gates
/-!
# Strong mark accumulation at the ORIGIN before projection memory.
Entitles ℓ¹ uniform one mark for any calibrated traces; `term` is inverse at reference r, not a fit from expectations! Actual sums retain both tags and valuations. For other sites use TRANSLATION of these not reissuance. -/
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
variable {N p k r d:ℕ}{q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p}{f:ℕ→ℕ}
variable {D:∀ m,Desk G (A.B.a.S.side m p)} (hz:Nest X Y)(hc:∀ i,Boutique.Feeling A i p (D i))(hR:k ≤ r)(ht:d+3≤A.B.a.clock.J r)(B':∀ n,Branch X (q n) (f n) p k)
open Boutique
set_option quotPrecheck false
local notation "F"=> (Labels.frames G).level d
local notation "H"=> fun i=> A.B.bake.make (q i)
namespace Branch
variable (L':Helmet A p f q k)(hZ:Jams.Wild X.shape A.delay)
local notation "T'"=> schedule hG b hz hc hR ht B'
variable (V:∀ n, TransferData ((Labels.frames G).level d) (A.B.bake.make (q n)) (f n) p)
variable (hV: ∀ n, ∀ h:r ≤ f n, (B' n).Piano b hc hR ht (V n) h)(he:∀ n:ℕ, r ≤ f n → (V n).Based (hol G) (localSection G d) r)
abbrev divers (m:ℕ)(n:ℕ):= (B' n).cargo b hc hR ht (V n) (hV n) m
local notation "W"=> divers b hc hR ht B' V hV
include hG b hz hZ B' hR ht V hV hc L'
lemma cheerful : Matric.Gear (k:=r) T' W:= by
    refine ⟨Branch.tiers hG b hz hc hR ht B' L' hZ,fun i h=>?_⟩; filter_upwards [L'.sails.eventually (eventually_gt_atTop i)] with n hn; exact ((B' n).tallies hG b hz hc hR ht (V n) (hV n) i h hn).1
variable (y:(Labels.frames G|>.level d|>.Coeff))
def forward (m n:ℕ): (F).Coeff:= ((V n).entries m ((V n).terminal.symm y)).x
local notation "y'"=> Branch.forward (A:=A) V y
include he
lemma winds (m:ℕ) (h:r≤ m): CauchySeq (fun n=> y' m n) :=by
     have h' (i:ℕ)(h:r ≤ i): ∀ᶠ n in atTop,y' i n=(T' i h n|>.leanings (W (i+1) n)) (y' (i+1) n):=(L'.sails.eventually (eventually_gt_atTop i)).mono fun n hn=> ((B' n).tallies hG b hz hc hR ht (V n) (hV n) i h hn).2 _
     apply (Matric.Gear.spends (cheerful hG b hz hc hR ht B' L' hZ V hV) _ h' m h)
     have hh:Tendsto (fun _ : ℕ=> y) atTop (𝓝 y):= tendsto_const_nhds
     apply Tendsto.cauchySeq (x:=y) (hh.congr' ?_); filter_upwards [L'.sails.eventually (eventually_ge_atTop r)] with n hn; exact ((he n hn).reads _ |>.trans ((V n).terminal.apply_symm_apply _))|>.symm
/-- all authorized. -/
lemma stays (m:ℕ)(hm:r≤ m): let z n:= (V n).entries m ((V n).terminal.symm y)
     CauchySeq (fun n=> (z n).x) ∧ ∃ T:ℕ→ Coin ((Labels.frames G).level d) (hol G) (D m),CauchySeq T ∧ ∀ n:ℕ,∀ h:m≤ f n,Coin.uses (T n)=capture (z n) (Keeper.sufficient ((B' n).slots m (hR.trans hm) h)):=by
    intro z; let T n:= (W m n).g (y' m n)
    have he:= winds hG b hz hc hR ht B' L' hZ V hV he y m hm; exact ⟨he,T,(cheerful hG b hz hc hR ht B' L' hZ V hV).hides m hm _ he, fun n h=> (B' n).capitals b hc hR ht (V n) (hV n) m hm h _⟩
end Branch
end Bandage
end YM.PhysicalNext.Repeat.Legato
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Branch.stays
