import YM.UVExtension.Flake.Hulls
import YM.UVExtension.Flake.Twist
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
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)
local notation "Hut"=> (S.fits N n).Hut
open Camp Camp.Cart
variable (v:Rose S)
open Dales Guild
variable (he: (b.val:ℂ)=ink S N m n hm.le (v.val:ℂ))
-- avoid coercions.Be generic FLOAT.Keeper in Waged. vary H along fixed path.
private lemma script {f f':(S.fits N n).Home (m+1)} {p p' z z':ℝ} (hf:f=f')(hp:p=p')(hz:z=z') (h:Reality A.B.a (m+1) n ((S.fits N n).W (m+1)) f p) (h':Reality A.B.a (m+1) n ((S.fits N n).W (m+1)) f' p') (Q:Dales.floatX X ((S.fits N n).charts m hm) ((S.fits N n).W (m+1)) f p z h)
    (hr:HasSlots (A.B.a.budget (m+1)) (Dales.mount X N (m+1) n f.val p z).activities)(hr':HasSlots (A.B.a.budget (m+1)) (Dales.mount X N (m+1) n f'.val p' z').activities)
    (θ:Push.Local.Readable (hol G) (localSection G d) (A.B.a.budget (m+1)) (A.B.a.S.side (m+1) n) (title G (M.p.profile (A.B.a.clock.J (m+1))))) (L':Lacing.Banner A.B.a ((frames G).level d) (hol G) n m)
    (hs:HasSlots ((Q.body.result beam0).p) ((Q.body.result beam0).activities)) (hk:Waged Q.body beam0 θ hr (Keeper.sufficient hs) L') : ∃ Q': floatX X ((S.fits N n).charts m hm) ((S.fits N n).W (m+1)) f' p' z' h', ∃ hs':HasSlots ((Q'.body.result beam0).p) ((Q'.body.result beam0).activities), Waged Q'.body beam0 θ hr' (Keeper.sufficient hs') L':=by
    subst f p z; exact ⟨Q,hs,hk⟩
local notation "TE"=> pins1 S N m n b hm
local notation "hF"=> readB R d m n hd
local notation "Tv"=> tide S R d N m n v -- qualify
open UVExtension.Mast
include he
lemma tents: ∃ Q:duetB S N m n b hm, Waged Q.body beam0 hF TE (Keeper.sufficient (pinsQ S N m n b hm Q)) (tide S R d N m n v):=by
   obtain ⟨h₁,h₂,h₃⟩:= plumes S N m n b hm v he _ m.le_succ hm
   have hv := H|>.acts V (S.token N n) τ v.2
   have hP:= H|>.sprig V (S.token N n) τ m hm.le b
   obtain ⟨Q,hx,ht⟩:= script S d N m n hm h₁.symm h₂.symm h₃.symm (hv.1.alive _ hm) (hP.alive _ m.le_succ hm) (ray S N n m v hm) (Mast.slots1 S N m n v hm) (pins1 S N m n b hm) hF (tide ..) (Mast.slots0 S N m n v hm) (Mast.follows S R d N m n v hm hd); exact ⟨Q,ht⟩
-- INTERPOLATED realization on diameter.W. every real ALL
omit he
local notation "L'"=> Lacing.Banner A.B.a ((frames G).level d) (hol G) n m
lemma wire : ∃ (Q: duetB S N m n b hm)(a:L'), Waged Q.body beam0 hF TE (Keeper.sufficient (pinsQ S N m n b hm Q)) a ∧ ∀ (u:Rose S),(b.val:ℂ)=ink S N m n hm.le (u.val:ℂ)→ tide S R d N m n u=a:=by
    by_cases h:∃ u:Rose S,(b.val:ℂ)=ink S N m n hm.le (u.val:ℂ)
    · obtain ⟨u,hu⟩:=h; obtain ⟨Q,hP⟩:= tents S R d N m n b hm hd u hu; exact ⟨Q,_,hP,fun v hv=> by rw [pigment S N m n b hm u hu v hv]⟩
    let Q:= onB S N m n b hm; obtain ⟨a,ha⟩:= polar S R d N m n b hm hd Q; exact ⟨Q,a,ha,fun v hv=> (h ⟨v,hv⟩).elim⟩
end YM.UVExtension.Flake
