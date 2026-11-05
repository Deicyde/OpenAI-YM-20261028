import YM.UVExtension.Forest.Forte
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
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
local notation "K'"=> A.B.a.budget m
open Steady Planned.GuardedAtom Guard Roads.Unum Wet.MarketP
variable {ι:Type}{w:Filter ι} [w.NeBot][w.IsCountablyGenerated](t:ι→ ℕ)(ht:Tendsto t w atTop)
variable (hh: cashr (A:=A) w t m)(hq:cashr (A:=A) w t (m+1))
variable (hm:∀ i,m<t i)
local notation "x'"=> fun i=> v (t i) n
local notation "g'"=> fun i=> S.realBeat ((x' i).val) (t i) n
local notation "b"=> fun i=> S.realBeat ((x' i).val) (t i) n (m+1)
local notation "gL"=> fun i=> slots0 S (t i) m n (x' i) (hm i)
local notation "N₁"=> A.B.a.S.side (m+1) n
local notation "N₀"=> A.B.a.S.side m n
local notation "shearsD"=> fun i=> slots1 S (t i) m n (x' i) (hm i)
local notation "W'"=> fun i=> (ray S (t i) n m (x' i) (hm i)).body
local notation "gM"=> fun i=> Keeper.sufficient (gL i)
local notation "F"=> (frames G).level d
variable (Z:(i:ι)→Blush.Cloud (S.realBeat ((v (t i) n).val) (t i) n (m+1))) (hD:Wet.Constant (v:=w) (fun i=>(Z i).live))(hC:Wet.Constant (v:=w) (fun i=>(Z i).pale))
    (hd:d+3 ≤ A.B.a.clock.J m)
-- Gold reads.SAIL.DENSE extend using standard CLM.
local notation "L"=> fun i=> tide S R d (t i) m n (x' i)
local notation "V'"=> fun i=> readC S R d (t i) m n (x' i) hd
local notation "Q'"=> A.B.a.budget (m+1)
local notation "E1"=> Bucket (F) K' (hol G) N₀
local notation "η0"=> Doors.rate (P.L (A.B.a.clock.J (m+1)))
lemma dons i : Waged (W' i) beam0 (V' i) (shearsD i) (gM i) (L i):= follows (hd:=hd) _ _ _ _ _ _ _ (hm i) -- hd explicit order
variable (he:(1+2*(A.B.a.params m).columns)*Doors.rate (A.B.a.S.block m) ≤ Bid.barunit (A.B.a.S.block m))
include a hv ht hh hq hd hm
section primary
include he
lemma pivotW (i:Option (F).Index) :∃ X:E1, Tendsto (fun j:ι=> (L j).vane i) w (𝓝 X):=by
   rcases i with _|i; · refine ⟨0,tendsto_const_nhds.congr' (Eventually.of_forall fun i=>?_)⟩; exact (Waged.noneM (dons S v R d m n t hm hd i)).symm
   by_cases h:i=0
   · subst i; refine ⟨(((P.L (A.B.a.clock.J (m+1))).val:ℂ)^d • (F).e0,0),tendsto_const_nhds.congr' (Eventually.of_forall fun i=>?_)⟩; exact (Waged.unit (dons S v R d m n t hm hd i)).symm
   let Z j:= lark (b j) i (V' j) (shearsD j); have ht(j):=(ting S v R d (t j) m n (hm j) hd he).2.2 i h
   have hE(j):0∈(Z j).live.crest.image (A.B.a.clock.op m n).ratio.parent:=by  have hh:(Z j).live.crest=(localSection G d).footprint (0:Site N₁):= skin ..; exact Graces.support_zero _ _ (hh.symm ▸ ankle)
   obtain ⟨z,hZ⟩:=roues S v R d m n a x hv t ‹_› hh hq hm Z (eminence (R:=b) (fun j=>(Z j).live) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)) (eminence (R:=b) (fun j=>(Z j).pale) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)) hd ht hE
   exact ⟨z,hZ.congr' (Eventually.of_forall (fun j=> (Waged.pace (dons S v R d m n t hm hd j) i h).symm))⟩
end primary
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
section pre
variable (i:Eyelet.Slot (A.B.a.S.side (m+1) n))(U:Birth (hol G) i.1 (A.B.a.budget (m+1)) d)
local notation "T"=> (Q').supBounds 0 i.1.val U.val
local notation "K"=> tin d (hol G) i.1 Q'
lemma firstly : ∃ x:E1, Tendsto (fun j=>(L j).glass i ( (Eyelet.fee Q' i.1.val:ℂ) • twig K U)) w (𝓝 x):=by
    have hp:T ‖K U‖:= (pays d (hol G) i.1 Q' U).2 le_rfl; let Z j:= tonne (n:=n) (Q:=fun _=>b j) beam0 (shearsD j) i U _ hp -- Q binder implicit shape.N
    have hh(j):=Waged.sack (dons S v R d m n t hm hd j) i |>.spark U _ hp
    have hx(j) : (Z j).live.crest=i.1.val :=by change ((b j).activities.reg (Blush.found 0 i.1.val i.1.property)).support=i.1.val; rw [Blush.latch _ _ _ _ (shearsD j)]
    obtain ⟨z,hZ⟩:=roues S v R d m n a x hv t ht ‹_› hq hm Z (eminence (R:=b) (fun j=>(Z j).live) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)) (eminence (R:=b) (fun j=>(Z j).pale) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)) hd hh (fun j=> Graces.support_zero _ _ ((hx j).symm ▸ i.1.property))
    exact ⟨z,hZ.congr' (Eventually.of_forall (fun j=> Waged.sack (dons S v R d m n t hm hd j) i|>.linke U _ hp))⟩
end pre
section link
variable (i: StockTag (A.B.a.S.side (m+1) n))(U: Eyelet.Bolt (G:=G) (A.B.a.budget (m+1)) i)
local notation "K"=> sink (G:=G) Q' i
lemma nymph : ∃ x:E1, Tendsto (fun j=>(L j).wing i ( ((Eyelet.fee Q' i.val.1 / κ:ℝ):ℂ) • twig K U)) w (𝓝 x):=by
    by_cases h:0∈ i.val.1; swap
    · refine ⟨0,tendsto_const_nhds.congr' ?_⟩; filter_upwards with j; rw [Waged.blank (dons S v R d m n t hm hd j) i h]; rfl
    have hp: ∀ V,‖U.val V‖ ≤ ‖K U‖ := (debts _ _ _).2 le_rfl
    let Z j:= Graces.vaneT (n:=n) (Q:=fun _=>b j) beam0 (shearsD j) i U _ hp
    have hz(j):=Waged.limb (dons S v R d m n t hm hd j) i h|>.spark U _ hp
    have hx(j) : (Z j).live.crest=i.val.1:= congr_arg Prod.fst (cardK (Keeper.sufficient (shearsD j)) i)
    obtain ⟨z,hZ⟩:=roues S v R d m n a x hv t ht hh hq hm Z (eminence (R:=b) (fun j=>(Z j).live) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)) (eminence (R:=b) (fun j=>(Z j).pale) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)) hd hz (fun j=> Graces.support_zero _ _ ((hx j).symm ▸ h))
    exact ⟨z,hZ.congr' (Eventually.of_forall (fun j=> Waged.limb (dons S v R d m n t hm hd j) i h|>.linke U _ hp))⟩
end link
end YM.UVExtension.Mast
