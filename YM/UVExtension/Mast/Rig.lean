import YM.UVExtension.Mast.Braid
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "V!"=> Voice F H n
local notation "μ!"=> Music F H N n
local notation "sT"=> Legato.Bandage.waybill (A.B.a)

open Eyelet

-- analytic extension numbers and towers may depend on r chosen before coupling.
-- `Ledger` universal on REAL. Later augment with Contour spec.
structure Cellar (S: Uses Q hG)(t:ℕ→ℕ)(R:Legato.Bandage Q C W) where
   line (d n i N:ℕ) (_z:Orchard.Rose S): Lacing.Banner A.B.a ((frames G).level d) (hol G) n i
   toll (d n:ℕ) : ℕ→ℝ
   vane : ℕ → ℕ→ℕ→ℝ
   lidS : ℕ→ℕ→ℕ→ℝ
   column : ℕ→ℕ→ℕ→ℝ
   posts i: i+3 ≤ A.B.a.clock.J (t i)
   pay (v:Keys S) (d n m:ℕ) (h:t d ≤ m): Ability S d n R m (fun i=> line d n m i (v i n)) (toll d n m) (vane d n m) (lidS d n m) (column d n m) (column d n (m+1)) v
   flow (d n:ℕ)(v:Orchard.Keys S) (b:Orchard.Rose S) : Tendsto (fun i=> (v i n).val) atTop (𝓝 b.val) → ∀ i:ℕ, t d ≤ i→ Course (fun j=> line d n i j (v j n))

variable {t:ℕ→ℕ}

namespace Cellar
variable (U:Cellar S t R)

def paths (d n:ℕ)(i j:ℕ): Lacing.Banner A.B.a ((frames G).level d) (hol G) n i:= U.line d n i j (v j n)

variable {S R}
def cantors (U:Cellar S t R) (d n:ℕ): Pans S v d n (t d) W (paths S v R U d n):= Nonempty.some (banded S v R d n (U.posts d) (U.pay v d n))

section factory
variable (U : Cellar S t R)
-- Engage any tour below Actual.Edits.Witness.
lemma launch (d N n:ℕ) : ∃ T : TransferData ((frames G).level d) (Orchard.Path S v) N n, t d ≤ N → T.Based (hol G) (localSection G d) (t d) ∧ T.entries=((cantors v U d n).song N|>.draft (Orchard.Path S v)).inits:=by
   by_cases hp:t d ≤ N
   · let z:=U.cantors v d n; let X:=z.song N; have h:= (z.lyr N hp).earned
     obtain ⟨T,hT,hA⟩:= Work.G08.answer W H R.clock.room R.clock.bank N n d (t d) ((frames G).level d) (X.draft (Orchard.Path S v)) (localSection G d) (hol G) (Sung.clocks (localSection G d) H N n (hol G) W (t d) X h); exact ⟨T,fun _=> ⟨hA,hT⟩⟩
   exact ⟨⟨fun _ v=>Extra.Histories.primary 0 v,LinearEquiv.refl _ _⟩,fun he=> False.elim (hp he)⟩

-- definite prescription; no retuning of offsets.
def gate (d N n:ℕ):= (launch v U d N n).choose
def yard : Family G:= Family.mk (Orchard.Path S v) (hol G) (frames G) (localSection G) t (gate v U)

lemma intakeV : Vintage.YM.Family.Makes (yard v U) :=by
   have h := Issue.refer H W C t R.clock U.posts
   refine ⟨Orchard.selected .., h.gets,h.order,h.fits,fun d N _ hi o q=>h.loaded d N hi _ rfl rfl _ o q,fun d N p hi=> ((launch v U d N p).choose_spec hi).1⟩
lemma freed (d N p:ℕ)(hi:t d ≤ N): Vintage.YM.PhysicalNext.Repeat.Legato.Bandage.Freight (ministry S v) (housed S v) N p d (gate v U d N p) (t d) W (roof S v N p):=by
   let V:= U.cantors v d p; let X:= V.song N; have hx:=V.lyr N hi
   refine ⟨X,hx.head,((launch v U d N p).choose_spec hi).2,hx.earned,fun i he ht=>⟨(hx.comes i he ht).1,(hx.comes i he ht).2.1⟩⟩

-- committed actual fields
lemma hardy (v':Orchard.Keys S) : Spec.Calibrated (yard v' U):= ⟨M.p,P,A.θ,A.delay,A.bar,A.asks,M.O,M.K,A.post,A.B,(ministry S v').history,(ministry S v').sticks,rfl,(ministry S v').moves⟩
end factory
end Cellar
end YM.UVExtension.Mast
#print axioms YM.UVExtension.Mast.Cellar
#print axioms YM.UVExtension.Mast.Cellar.freed
