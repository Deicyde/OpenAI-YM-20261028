import YM.UVExtension.Cloud.Tail
import YM.UVExtension.Rafter.Stile
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
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
open UVExtension.Flake Dales Guild Lamppost Rafter Tabernacle Camp Oriel Oriel.Charted
include hm
local notation "Q"=> A.B.a.budget m
local notation "F0"=> A.B.a.clock.forcedAllowance m
open Bud Linden Copse Mallow Lotus Daisy Charity
open Pressure Pressure.Testing ConnectedActivityE6 Push.SectorMeasure
-- receipts passport ANY common root cloud + corresponding turns. true traveller.s.Ensure healthy supports MRT.
variable (K : ∀ b:Shade,duetB S N m n b hm)
local notation "c"=> A.B.a.S.side m n
local notation "q!"=> mount X N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
local notation "W"=> Cash.fragrances (((S.fits N n).charts m hm).atTopH)
local notation "k"=> (((S.fits N n).charts m hm).atTopH)
local notation "o"=> (0:Site c)
variable (Y:Blush.Cloud (mount X N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0))(M':∀ b:Shade,Blush.Cloud (cumulus S N m n b (m+1)))
    (ht:∀ i,(M' i).live.turn=Y.live.turn)(hY:Guarded X Y.live)(hf:∀ i,(M' i).live.ingredient=Y.live.ingredient)(hQ:∀ i,(M' i).pale.ingredient=Y.pale.ingredient)
    (hh:(0:Site (A.B.a.S.side (m+1) n))∈ Y.live.crest) (hp: Guild.PriceS X m)
local notation "t"=> fun b=> houseS (K b|>.body) beam0
local notation "pT"=> fun b=> Blush.scope (houseS (K b|>.body) beam0) (M' b) (0:Site c)
local notation "e0"=> Blush.enter (k)
local notation "X!"=> Blush.scope (k) Y o
local notation "y"=> locus Y.live k o
local notation "ℓ"=> fun b=> (H|>.align V (S.token N n) τ m m hm.le le_rfl hm K b beam0).furrow
include ht
set_option maxHeartbeats 750000 in
lemma decks (b:Shade): pT b= X! ∧ (∀ i, e0 i= Blush.enter (t b) (ℓ b i)) :=by
    have h(i): e0 i= Blush.enter (t b) (ℓ b i):= (Bud.slotsP ((S.fits N n).align V (S.token N n) τ m m hm.le le_rfl hm K b beam0) ⟨rfl,rfl,rfl,rfl,rfl⟩ rfl i).symm -- defeq
    refine ⟨funext fun i=> ?_, h⟩; change Blush.scope (t b) (M' b) _ i=Blush.scope k Y _ i; unfold Blush.scope
    by_cases hg:i∈Set.range (Blush.enter (k))
    · obtain ⟨i,rfl⟩:= hg; rw [(Blush.enter (k)).injective.extend_apply,h i, (Blush.enter (t b)).injective.extend_apply]; exact H|>.wallets V (S.token N n) τ _ _ _ le_rfl _ Y.live K _ ht beam0 b _ i -- inspect
    have hs:i ∉ Set.range (Blush.enter (t b)):=by rintro ⟨i,rfl⟩; obtain ⟨i,rfl⟩:=(ℓ b).surjective i; exact hg ⟨_,h _⟩
    rw [Function.extend_apply' _ _ _ hs,Function.extend_apply' _ _ _ hg]

local notation "S0"=> prices Y.live 0
local notation "k!"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "n!"=> A.B.a.clock.hatBeta (m+1)
local notation "Q0"=> budgetsP Y.live (X.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) 0
local notation "T!"=> fun b=> (K b).body
local notation "r!"=> (((P.L (A.B.a.clock.J (m+1))).val:ℂ)^d)
local notation "G'"=> Keeper.sufficient
local notation "H'"=> fun b=> Rainfall.sky ((K b).body) beam0 r! (M' b) F -- r!
local notation "N0"=> ((A.B.a.clock.hatBeta (m+1)) * S0)
local notation "𝔊"=> Ovens.Pipes.addr (folio G c) (Q)
variable (hT:∀ b:Shade, sparkT (K b|>.body) beam0 (M' b) d)
include hY hf hQ hh hT hp
set_option maxHeartbeats 750000 in
lemma slated :
   Rafter.Stalk (shop (G:=G) Q X!) spreadK (fun b i (u:Concert.Tap (A.B.a.budget m) G 0 (X! i))=> u.read ((H' b).bulk i)) (‖r!‖*(N0+N0+(N0+N0))) ∧ Rafter.Stalk (belaying (G:=G) Q (fun i=> (Ovens.Pipes.addr (folio G _) Q i).support)) spreadK (fun b i u=> (H' b).forced i u) (‖r!‖*(Q0+Q0+(Q0+Q0))) :=by
   have ha(p: Lotus.Leaf (q!))(h:p.turn=Y.live.turn) (hc:p.weight=Y.live.weight)(hv: ∀ b:Shade, Lotus.Leaf (cumulus S N m n b (m+1)))(hp':∀ b,(hv b).turn=p.turn)(hP:∀ b,(hv b).ingredient=p.ingredient) :
       let Fp b (i:W):= matin (hv b) (houseS (K b|>.body) beam0) (ℓ b i) Chi.canonical
       Nonempty (Atlas (cardsP (G:=G) Q o y ((Q).supportExponent+2)) spreadK (fun b i (u:Concert.Tap (A.B.a.budget m) G o (locus Y.live k o i))=> u.read (Fp b i)) (fun _=> N0+N0)) ∧ Nonempty (Atlas (mantleX A m n 0) spreadK (fun b i x=> Mallow.tonic (pupil (K b).body beam0 (hv b)) i x) (fun _=> Q0+Q0)):=by
       intro v; have hj: p.crest=Y.live.crest:=by unfold Leaf.crest; rw [h]
       have hg := support_zero (A.B.a.clock.op m n).ratio _ (hj.symm ▸ hh); have hs:Guarded X p:=⟨fun Qx h' hP=> by rw [h]; exact hY.lives Qx h' hP⟩
       obtain ⟨hM,_,he⟩:= Fitted.jollity S.grove.enabled (S.fits N n) (S.cart N n) (S.token N n) τ m m hm.le le_rfl hm p hs K hv hp' hP beam0 (0:Site (A.B.a.S.side m n)) hg hp 0
       have hr: locus p k o=y :=by funext v; unfold locus Charity.speaks; rw [h]
       simp_rw [budgetsP,Linden.prices,hc,hj] at he; constructor
       · change Nonempty (Atlas (cardsP (G:=G) Q o (locus p k o) _) spreadK (fun d j (u:Concert.Tap (A.B.a.budget m) G o ((locus p k o) j))=> u.read (v d j)) _ ) at hM -- underscore price. edit
         rw [hr,Linden.prices,hj,hc] at hM; exact hM
       exact he
   let v b (j:W):= matin (M' b).live (t b) (ℓ b j) Chi.canonical; let q b (j:W):= matin (M' b).pale (t b) (ℓ b j) Chi.canonical
   obtain ⟨hx,h1⟩:= ha Y.live rfl rfl (fun b=>(M' b).live) ht hf; obtain ⟨hm',h2⟩:= ha Y.pale Y.together.symm Y.rates.symm (fun b=>(M' b).pale) (fun b=> (M' b).together.symm.trans ((ht b).trans Y.together)) hQ
   have hL(b):= decks S N m n hm K Y M' ht b
   constructor
   · have hz: (r!)≠0:=pow_ne_zero d (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (P.L _).property))
     refine Rafter.mist (A.B.a.budget m) (y) X! r! v q (fun b=>(H' b).bulk) e0 ?_ ?_ hz ?_ ?_ hx hm'
     · intro b i; change Blush.fields (t b) (M' b) _ _=_; unfold Blush.fields; rw [(hL b).2 i, Progress.DirectedRecipe.stuffed]; rfl
     · exact fun i=> (Blush.enter (k)).injective.extend_apply ..
     · intro b j; rw [← (hL b).1]; exact (hT b).halo.regular j
     intro j hj b; apply Progress.DirectedRecipe.blank; rintro ⟨i,rfl⟩; obtain ⟨i,rfl⟩:= (ℓ b).surjective i; exact hj ⟨_,(hL b).2 _⟩
   obtain ⟨f⟩:=h1; obtain ⟨g⟩:=h2; have hb:= ((Stalk.ascend f).plus ((Stalk.ascend g).scales Complex.I)).scales r!; rw [Complex.norm_I,one_mul] at hb; obtain ⟨f,hf,hB,hbb⟩:= hb.rises
   refine ⟨f,hf,hB,fun z hz=>?_⟩ -- K stamps by definitional equality
   obtain ⟨g,hg,hV⟩:= (hbb z hz).afloat
   refine ⟨g,hg,fun i=>?_⟩; have ht:= hV i; simp_rw [mantleX,Copse.nose,Copse.portal,Copse.worth,Copse.one] at ht; exact ht
end YM.UVExtension.Cloud
