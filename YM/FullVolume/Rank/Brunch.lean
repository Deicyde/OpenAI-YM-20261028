import YM.FullVolume.Rank.Lyrics
import YM.FullVolume.Rank.Lucid
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
lemma brioche (F:∀ i,Cloud (heroB U i))(T:∀ i,Cloud (heroB V i)){k:Wing}(hx:Voicelet U V F T k) (hθ:∀ i,Cub.Tyne (U i).stock center (q i) (F i) d)(hθ':∀ i,Cub.Tyne (V i).stock center (q' i) (T i) d):
     Shift D (fun i=> Cub.prepare (U i).stock center (U i).down (F i) (d:=d)) (fun i=> Cub.prepare (V i).stock center (V i).down (T i) (d:=d)):=by
    let p':=φ; let m':=φ'; obtain ⟨X,Y,hA,hB⟩:= micro (d:=d) hG U V hU hV he hv hX hh hG' ht hl hc F T hx hθ hθ'
    let S:= Blush.scope (U 0).sale (F 0) 0; let D₀ i:= Cub.innerT (U i).stock center (F i) (d:=d); let D₁ i:= Cub.innerT (V i).stock center (T i) (d:=d)
    let K i:= Keeper.sufficient (U i).down; let R i:= Keeper.sufficient (V i).down; let Z₁ i:=gala (K i) (localSection G d) (hol G) (D₀ i) S; let Z₂ i:=gala (R i) (localSection G d) (hol G) (D₁ i) S
    have ht₀ : D.orient.p= Q:= (hW 0).alongside.price.trans (hU 0|>.represents _ _ _ (U 0|>.hx.le)|>.vac); let w:= authors A.B.a m
    have hP: Push.Local.Readable (hol G) (localSection G d) D.orient.p z w:= ht₀.symm ▸ livelyCard b.clock ((Nat.le_add_right d 3).trans hd)
    have ht: SeatE (fun n=>(D₀ n).bulk) (fun n=>(D₁ n).bulk) D.orient.p S:= ht₀.symm ▸ hA
    have hΔ n:= (hW n).alongside; have hp n:= (hW' n).alongside
    have hD₀ n:Have (p' n) (D₀ n) S (localSection G d) (hol G) w (A.B.a.clock.forcedAllowance m) D.k:=by rw [(hW n).paid,← show Blush.scope _ _ _= S from X n]; exact hθ _
    have hD₁ n: Have (m' n) (D₁ n) S (localSection G d) (hol G) w (A.B.a.clock.forcedAllowance m) D.k:=by rw [(hW' n).paid,← show Blush.scope _ _ _= S from Y n];exact hθ' _
    have heq : Shift D Z₁ Z₂:=by
        let R₀(n):=(hU n|>.represents _ p _ (U n|>.hx.le)).good; -- Direction shapes.C standardized.Z. use explicit equality to Calendar params for `∀ i` binder.
        have hX n : (p' n).Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m):= R₀ n
        have hY n: (m' n).Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m):= (hV n|>.represents _ _ _ (V n|>.hx.le)).good
        refine ⟨Col.minted hΔ hp hP ht (K:=K) (K':=R) (by change Tendsto (fun (_:ℕ)=> (0:(Fa).Coeff)-0) atTop _; simp), Col.collected hΔ hp hP ht hX hY K R hD₀ hD₁, Col.carried hΔ hp hP ht hB hc.tips hX hY K R hD₀ hD₁ («Z»:=cart (K 0)) (fun _=>rfl) (fun _=>rfl)⟩
    suffices ha:(fun i=>Cub.prepare (U i).stock center (U i).down (F i) (d:=d))=Z₁∧ (fun i=> Cub.prepare (V i).stock center (V i).down (T i) (d:=d))=Z₂ by rw [ha.1,ha.2]; exact heq
    exact ⟨funext (fun i=>congr_arg (gala (K i) (localSection G d) (hol G) (D₀ i)) (X i)),funext fun i=>congr_arg (gala (R i) (localSection G d) (hol G) (D₁ i)) (Y i)⟩
local notation "T₀"=>fun n=>((U n).castT b (hU n) hd).plate
local notation "T₁"=>fun n=>((V n).castT b (hV n) hd).plate
variable (x: Config G (A.B.a.S.side (m+1) p)→ℂ)
section main
-- Budget. `budgetCard` no E.Start true.Hearing.
lemma graces (hz:Nest X Y)(i:((Labels.frames G).level d).Index)(hi:i≠0): Shift D (fun n=>(T₀ n).main i) (fun n=>(T₁ n).main i):=by
   -- choose headings only for `a≤`. Tare existence emissions needed: budgetJ not even requiring E.Result.Coll
   let s:= Cub.title G (M.p.profile Q₁)
   have hS : Heir.Release.accepts (X.span Q₁ (A.B.a.clock.J m)) (M.p.profile Q₁).supportExponent ((M.p.profile (A.B.a.clock.J m)).supportExponent+2) (P.L Q₁):= (b.tunes _ _ _ (Graces.feet hd b.clock) _ (P.large _).need).1
   have hX {g M₀}(U:Boutique X M₀ g p m)(h:(A.B.bake.make M₀).Selected): let F:= lark U.player i (U.okC b h hd) U.up; let t:=(U.castT b h hd).plate
    Cub.Tyne U.stock center M₀ F d∧ t.main i= Cub.prepare U.stock center U.down F:=by
       intro F p; refine ⟨?_ ,if_neg hi⟩ -- if_neg
       obtain ⟨a,b,x,hv,hH,hG⟩:= budgetJ U.hx b.songs b.PStage b.wait (Graces.feet hd b.clock) hz b.r U.stock center (U.okC b h hd) U.up i hi hG U.taught rfl U.down hd b.shape b.clock b.stamp hS
       exact ⟨hv.1,a,b,x,hG.1⟩
   have hh₀ n:=hX (U n) (hU n); have hh₁ n:= hX (V n) (hV n)
   let F n:= lark (heroB U n) i (okC b (U n) (hU n) hd) (U n).up; let W n:=lark (heroB V n) i (okC b (V n) (hV n) hd) (V n).up
   simp_rw [fun n=> (hh₀ n).2,fun n=> (hh₁ n).2]; refine brioche (k:=.logKey (Circlet.badge G Z d)) hG b U V hU hV hd he hv ‹_› hh hG' ht hl hc hW hW' F W (?_) (fun n=>(hh₀ n).1) (fun n=>(hh₁ n).1)
   let k:= (Blush.found (0:Site Z) ((localSection G d).footprint _) ankle)
   let f:= masked (t').threshold ((localSection G d).footprint (0:Site Z)) (Push.Local.presented (localSection G d) 0 (t').threshold (Size.axis (Fa) i))
   have hu{q g}(T:Boutique X q g p m)(hU:(A.B.bake.make q).Selected):let U:=lark T.player i (okC b T hU hd) T.up; U.live.ingredient=Complex.reCLM ∘ f ∧ U.pale.ingredient=Complex.imCLM ∘ f:=by
      intro U; let P:= T.player; have hk:P.p=t':= (hU.represents _ _ _ T.hx).vac
      change Complex.reCLM ∘ masked P.p.threshold _ (Push.Local.presented (localSection G d) 0 P.p.threshold (Size.axis (Fa) i))=_ ∧ Complex.imCLM ∘ masked P.p.threshold _ (Push.Local.presented (localSection G d) 0 P.p.threshold (Size.axis (Fa) i))= _; rw [hk]; exact ⟨rfl,rfl⟩
   exact ⟨⟨fun i=>rfl,fun i=>rfl⟩, ⟨s,fun i=> le_rfl,fun i=> le_rfl⟩,fun i=>⟨(hu (U i) (hU i)).1.trans (hu (U 0) (hU 0)|>.1.symm),(hu (U i) (hU i)).2.trans (hu (U 0) (hU 0)|>.2.symm)⟩,fun i=>⟨(hu (U i) (hU i)).1.trans (hu (V i) (hV i)|>.1.symm),(hu (U i) (hU i)).2.trans (hu (V i) (hV i)|>.2.symm)⟩⟩
end main
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
