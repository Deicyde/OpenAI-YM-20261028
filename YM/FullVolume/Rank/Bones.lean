import YM.FullVolume.Rank.Brunch
import YM.FullVolume.Rank.Setup

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
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
namespace Boutique
set_option quotPrecheck false
variable {q:ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {f:ℕ→ℕ} {p m:ℕ}
local notation "Z₀"=> (A.B.a.S.oneStep m p).exact_size
local notation "z"=> A.B.a.S.side m p
local notation "Z"=> A.B.a.S.side (m+1) p
local notation "W!"=> A.B.a.clock.op m p
local notation "Q"=> A.B.a.budget m
local notation "t'"=> A.B.a.budget (m+1)
open RG.Shoot Lark Rain Blush
local notation "W₁"=> FullVolume.Urns.layout G Z t'
variable {q':ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {g:ℕ→ℕ} (U:Stack X m p q f) (V:Stack X m p q' g)
variable {D:Desk G (A.B.a.S.side m p)}{d:ℕ}{L:ℕ→ℝ} {K':Bid.Worth}
variable (hU:∀ i, (A.B.bake.make (q i)).Selected) (hV:∀ i,(A.B.bake.make (q' i)).Selected) (hd:d+3 ≤ A.B.a.clock.J m)
variable (he:Stationary.Artes.Cadre A.post A.B.kin)(hv:Next.Free.Amplify A.B.M)(hX: Jams.Wild X.shape A.delay)(hh:Lark.Near A m f)(hG':Lark.Near A m g)(ht:Tendsto f atTop atTop)(hl:Tendsto g atTop atTop)
open FullVolume.Shadow
local notation "φ"=> fun n=> (A.B.bake.make (q n)).rep (f n) p m
local notation "φ'"=> fun n=> (A.B.bake.make (q' n)).rep (g n) p m
variable (hc:Echo U V)
variable (hW:∀ n, Well ((A.B.bake.make (q n)).rep (f n) p m) D (Real.sqrt (A.B.a.clock.forcedAllowance m)))(hW':∀ n, Well ((A.B.bake.make (q' n)).rep (g n) p m) D (Real.sqrt (A.B.a.clock.forcedAllowance m)))
open FullVolume.Paint.Rank
local notation "Q₁"=> A.B.a.clock.J (m+1)
local notation "Fa"=> (Labels.frames G).level d
include b hU hV hd hW hW' hG he hv hX hh hG' ht hl hc U V
local notation "T₀"=>fun n=>((U n).castT b (hU n) hd).plate
local notation "T₁"=>fun n=>((V n).castT b (hV n) hd).plate
set_option quotPrecheck false
variable {E:Desk G (A.B.a.S.side (m+1) p)} (ha:∀ i,Well ((A.B.bake.make (q i)).rep (f i) p (m+1)) E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))) (ha':∀ i,Well ((A.B.bake.make (q' i)).rep (g i) p (m+1)) E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))))
variable (x: Coin ((Labels.frames G).level d) (hol G) E)
local notation "r"=> E.orient
local notation "p'"=> (r).p
include ha ha'
lemma perfume (i: ℕ):
     let f:= (Coin.uses x).1 i
     Shift D (fun n=>(T₀ n).tint i f) (fun n=>(T₁ n).tint i f):=by
    intro f'; let s:= mapSeat (n:=Z) i; obtain ⟨a,c,hP,hL⟩:= rem_tabs.mp (Coin.wealth x|>.2); obtain ⟨w,-,hw⟩:= hP.regular; let hp : ((Matric.book (0:(Fa).Coeff) (Coin.uses x))).Format 0 (hol G) r:= (Coin.wealth x).1
    let t:= w i; have hX {q n}(U: Boutique X q n p m)(h: Well U.player E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))))(hU:(A.B.bake.make q).Selected): let Z':= U.castT b hU hd
         ∃ (F:Cloud U.player), Z'.plate.tint i f'= Cub.prepare U.stock center U.down F∧ (F.live.turn=.logKey (Blush.found 0 s (spot _ _))) ∧ F.live.weight ≤ t∧ (F.live.ingredient= Complex.reCLM ∘ masked (p').threshold s f' ∧ F.pale.ingredient=Complex.imCLM ∘ masked (p').threshold s f')∧Cub.Tyne U.stock center q F d:=by
       intro Z'; let P:= U.player;let V:= Matric.book (0:(Fa).Coeff) (Coin.uses x); have hs:= along_format V h.alongside hp
       have hk:P.p.supBounds 0 s f' t:=by rw [← show p'=P.p from h.alongside.price]; exact hw i
       have hh: RegFit P 0 d (hol G) (mapSeat i) f':=⟨hs.smooth i,hs.origin i,hs.identity_null i,hs.projects i⟩
       obtain ⟨c,hc,hK,hY⟩:= grave U.stock center U.down U.up i _ hh hk; let F:= float U.player 0 s (spot _ _) f' c hh.smooth hK U.up; obtain ⟨x,y,s',h',hQQ,hT,-⟩:= regularJ hG U.hx U.down b.r b.tunes b.furthering hd b.clock b.stamp U.stock center rfl U.taught U.up s c f' hh hK
       refine ⟨F,hY,rfl,hc,⟨?_,?_⟩,h'.1,x,y,s',hT⟩ <;> rw [h.alongside.price] <;>rfl
    choose F hE hZ hG₀ hT h₀ using fun i=>hX (U i) (ha i) (hU i); choose S hV' hU' hG₁ hT' h₁ using fun i=> hX (V i) (ha' i) (hV i)
    simp_rw [hE,hV'] -- syntax
    exact brioche hG b U V hU hV hd he hv ‹_› hh hG' ht hl hc hW hW' F S ⟨⟨hZ,hU'⟩,⟨t,hG₀,hG₁⟩,fun i=> ⟨(hT i).1.trans (hT 0).1.symm,(hT i).2.trans (hT 0).2.symm⟩,fun i=> ⟨(hT i).1.trans (hT' i).1.symm,(hT i).2.trans (hT' i).2.symm⟩⟩ h₀ h₁
-- port at CAS before. need fixed cart for union step.src.s.
open MergeProof.Matric
lemma verdun (i:(Fa).Index)(k:ℕ): let x':=Coin.uses x; let Y:= Matric.book (Size.axis Fa i) x'
    Shift D (fun n=> (T₀ n).ink k (stowK ((U n).castT b (hU n) hd).up Y k)) (fun n=> (T₁ n).ink k (stowK ((V n).castT b (hV n) hd).up Y k)):=by
    intro x' Y'; let K':= Keeper.sufficient (U 0).up; let R:=(U 0).player; let Z':=stowK K' Y'; let f:= Z' k; have heq {q g}(U:Boutique X q g p m)(hP: Well U.player E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))): stowK (Keeper.sufficient U.up) Y'= Z':=by
       unfold Z' stowK
       have hp : U.player.activities.forced=R.activities.forced:= hP.alongside.force.symm.trans (ha 0).alongside.force; have he : profile U.player.activities Y'.forced= profile R.activities Y'.forced:=by unfold profile barcode; rw [hp]
       exact congr_arg (fun f:Box (Z)→ Config G Z→ℂ => Function.extend (cart K') (f ∘ Subtype.val) 0) he
    have hA₁(n): stowK (U n|>.castT b (hU n) hd|>.up) Y' k=f:=congr_fun (heq (U n) (ha n)) k; have hA₂(n): stowK (V n|>.castT b (hV n) hd|>.up) Y' k=f:=congr_fun (heq (V n) (ha' n)) k
    simp_rw [hA₁,hA₂]
    have h:=(granted (ha 0) (hol G) (Size.axis Fa i) x).2; obtain ⟨s,t,hv₀,hv₁⟩:= rem_tabs.mp (keeps K' Y' h); obtain ⟨dC,hC,hD⟩:= hv₀.forced
    let y:=dC k; have ht' V:‖f V‖ ≤ y:= (hD k).2 V
    by_cases hy:f=0
    · have hf{q n}(U:Boutique X q n p m)(h:(A.B.bake.make q).Selected): ((U.castT b h hd).plate.ink k f)=0:=by rw [hy]; change Cub.trick U.stock center U.down k 0 (d:=d)=0; unfold Cub.trick; rw [dif_neg (fun ⟨_,rk,_⟩=>rk rfl)]
      simp_rw [hf]; let f:=Matric.book (0:(Fa).Coeff) (0:File G z); let P:= (0:Coin Fa (hol G) D); have hp:= Coin.wealth P; have hh : f.Format 0 (hol G) D.orient:= hp.1; exact same (0:Pin Fa z) D ⟨_,hp.2⟩ hh
    have hz{q n}(U:Boutique X q n p m)(hp: Well U.player E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))))(hU:(A.B.bake.make q).Selected): let Z':= U.castT b hU hd
         ∃ (F:Cloud U.player), Z'.plate.ink k f= Cub.prepare U.stock center U.down F∧ F.live.turn=.gasKey k ∧ F.live.weight≤y ∧ (F.live.ingredient= Complex.reCLM ∘ f ∧ F.pale.ingredient=Complex.imCLM ∘ f) ∧ Cub.Tyne U.stock center q F d:= by
        intro P; let R:=U.player; have hV:P.up=Keeper.sufficient U.up:=rfl
        have hx:(rack P.up Y').Format 0 (hol G) R:= rack_format P.up Y' ((granted hp (hol G) (Size.axis Fa i) x).1)
        have hP: SlotFit R 0 k f:= (show (rack P.up Y').forced k=f from congr_fun (heq U hp) k) ▸ (show SlotFit R 0 k ((rack P.up Y').forced k) from ⟨hx.invariant k,hx.borel k,hx.supported k,hx.carried k,hx.forcing k⟩)
        obtain ⟨v,hv,hv',hξ⟩:= haunted U.stock center U.down k f hy hP ht' (d:=d)
        exact ⟨fan R 0 k f v hv' hP,hξ,rfl,hv,⟨rfl,rfl⟩, Graces.savvy hG U.hx U.down hU b.r U.stock center U.taught rfl b.clock b.stamp ((Nat.le_add_right d 3).trans hd) k f v hy hP hv'⟩
    choose F hF hX₀ hx₀ hS hZ using fun n=> hz (U n) (ha n) (hU n);choose q hq hX₁ hx₁ hD hE using fun n=> hz (V n) (ha' n) (hV n)
    simp_rw [hF,hq]; exact brioche hG b U V hU hV hd he hv hX hh hG' ht hl hc hW hW' F q ⟨⟨hX₀,hX₁⟩,⟨_,hx₀,hx₁⟩,fun i=>⟨(hS i).1.trans (hS 0).1.symm,(hS i).2.trans (hS 0).2.symm⟩,fun i=>⟨(hS i).1.trans (hD i).1.symm,(hS i).2.trans (hD i).2.symm⟩⟩ hZ hE
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
