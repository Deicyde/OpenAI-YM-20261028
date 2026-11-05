import YM.UVExtension.Mast.Grow
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
variable {L:∀ i:ℕ,ℕ → Lacing.Banner («H»:=A.B.a) ((frames G).level d) (p:=n) (A:=hol G) i} {r:ℕ}{u c w a:ℕ→ℝ}
variable (hp:d+3≤ A.B.a.clock.J r)(hx:∀ i:ℕ,r ≤ i→Ability S d n R i (L i) (u i) (c i) (w i) (a i) (a (i+1)) v)


-- Verses. All N. May require v in μΘ varying.N. Served Lens matches etc.
structure Pans (S:Uses Q hG)(v:Keys S)(d:ℕ) (n:ℕ) (r:ℕ) (W:Bid.Worth) (L:∀ i:ℕ,ℕ → Lacing.Banner («H»:=A.B.a) ((frames G).level d) (p:=n) (A:=hol G) i) where
   song N : Extra.Histories.Music ((frames G).level d) (Orchard.Path S v) N n
   lyr i (hi:r≤ i): Lyrics S v (W:=W) d i n r (fun m _=> L m i) (song i)

include hp hx
lemma banded : Nonempty (Pans S v d n r W L):=by
   have hM i: ∃ V: Music ((frames G).level d) (Orchard.Path S v) i n, r ≤ i→Lyrics S v (W:=W) d i n r (fun m _=> L m i) V:=by
      by_cases hi:r≤ i; · obtain ⟨V,hV⟩:= songs S v R d i n hp hx hi; exact ⟨V,fun _=>hV⟩
      exact ⟨⟨fun _=> ⟨fun _=>Extra.Histories.primary 0 0,fun _=>0,LinearEquiv.refl _ _⟩⟩,fun h=> False.elim (hi h)⟩
   choose f hf using hM; exact ⟨⟨f,hf⟩⟩

omit hp hx
namespace Pans
open Motion
variable (U:Pans S v d n r W L)
local notation "Y"=> U.song
set_option quotPrecheck false
def base (i:ℕ)(N:ℕ) : Card («H»:=A.B.a) F (p:=n) (A:=hol G) i:= if h:r ≤ N then (U.lyr N h).Vista i else 0
include hx -- no hp? eqst hx
lemma circ (he:∀ m:ℕ,r ≤ m → Course (L m)): Arcus («H»:=A.B.a) (p:=n) r (F) L (fun i N=> base S v d n U i N) u c w a:=by
   refine ⟨fun i hi=> (hx i hi).owns,fun i hi j=> (hx i hi).plays _,he,fun i hi j hj=>?_,fun i hi k hk=>?_⟩
   · unfold base; simp_rw [dif_pos (hi.trans hj)]; intro x; change ‖(U.lyr j (hi.trans hj)).Vista i x‖ ≤ _; rw [Lyrics.takes _ i hi hj]; exact ((U.lyr j (hi.trans hj)).climbs i hi hj x).trans (mul_le_mul_of_nonneg_right (hx i hi|>.size) (Work.G08.size_nonneg ..))
   dsimp only [Lacing.slip]
   unfold base; simp_rw [dif_pos (hi.trans hk.le)]; convert! (Lyrics.eqst R hx (U.lyr k (hi.trans hk.le)) i hi hk).2

local notation "Z!"=>base S v d n U
local notation "blink"=>UVExtension.Arrives
def stalls (i N:ℕ) := Lacing.steer (fun _:Motion=> L i N) (fun _:Motion=> base S v d n U (i+1) N) (glaring A.B.a i n)
lemma sym (i N:ℕ)(hi:r ≤ i) (hk:i<N) : (Y N|>.tone (i+1)).index.toLinearMap = (stalls S v d n U i N).symm.toLinearMap.comp (Y N|>.tone i|>.index.toLinearMap):=by
   have X:= U.lyr N (hi.trans hk.le); unfold stalls base; simp_rw [dif_pos (hi.trans hk.le)]; apply LinearMap.ext; intro x; have h:= (X.eqst R hx i hi hk).1 x; simp only [LinearEquiv.coe_toLinearMap,LinearMap.comp_apply]; rw [h,LinearEquiv.symm_apply_apply]
variable (he:∀ m:ℕ,r ≤ m → Course (L m))
include he
lemma wakes (i:ℕ)(hi:r ≤ i)(x:(F).Coeff): blink fun n'=> (Z! i n') x:= (circ S v R d n hx U he).cove i hi x
lemma plied (i:ℕ)(hi:r ≤ i)(x:(F).Coeff): blink fun n'=> (U.stalls S v d n i n').symm x:=by
   let f j:=fun _:Motion=> L i j; let ha:=hi.trans i.le_succ; let g j:=fun _:Motion=> base S v d n U (i+1) j
   refine Remnant.solved (f:=fun j=> major (f j) (g j) (glaring A.B.a i n)) (h:=?_) (2*w i*((F).extra+1:ℕ)) ?_ x -- or pilastered
   · exact fun x=> (wares («Y»:=g) (L:=f) _ (fun _=>he i hi) (fun _=> U.wakes S v R d n hx he _ ha) x).1
   filter_upwards [eventually_gt_atTop i] with j hj -- u mvar missing
   intro v'; obtain ⟨T,hT,hC⟩:= (hx i hi|>.plays j hj).efforts; have hp:= (Gate (hx i hi|>.owns) («Y»:=g j) (L:=f j) (fun _=> hT) hC (fun _=> (circ S v R d n hx U he).light _ ha j hj) (glaring A.B.a i n) v').1
   have hu:= Push.Local.size_le_norm F (major (f j) (g j) (glaring A.B.a i n) v'); have hx : 0≤2*w i:=mul_nonneg zero_le_two (zero_le_one.trans (hx i hi|>.owns.calm))
   exact (Push.Local.norm_le_size _ _).trans (hp.trans ((mul_le_mul_of_nonneg_left hu hx).trans_eq (mul_assoc ..).symm))
-- Index between r and every fixed level normalization. top bare complement later.
def feeds (i N:ℕ):= ((Y N).tone r).index.symm.trans ((Y N).tone i).index
lemma spikes (i:ℕ)(hi:r ≤ i)(x:(F).Coeff): blink fun N=> feeds S v d n U i N x:=by
    induction hi with
    | refl=> unfold feeds; simpa using! UVExtension.Arrives.steady x
    | step hi IH => rename_i i; apply (Lacing.Remnant.loops (f:=fun N=> (stalls S v d n U i N).symm.toLinearMap) (x:=fun N=> feeds S v d n U i N x) (h:=fun y=>plied S v R d n hx U he i hi y) (hp:=IH)).copy; filter_upwards [eventually_gt_atTop i] with N hN
                    let X:=(U.song N).tone r; let v':=X.index.symm x; exact Eq.symm (LinearMap.congr_fun (sym S v R d n hx U i N hi hN) v')
lemma pages (i:ℕ)(hi:r ≤ i)(x:(F).Coeff): blink (show ℕ → Bucket F (A.B.a.budget i) (hol G) (A.B.a.S.side i n) from fun (N:ℕ)=> by exact Lacing.Face H N n (A:=hol G) i ((U.song N).tone i) (((U.song N).tone r).index.symm x)) := by
    have hs:= spikes S v R d n hx U he i hi x
    apply (hs.pair (Remnant.loops (f:=fun j=> base S v d n U i j) (x:=fun j=>U.feeds S v d n i j x) (U.wakes S v R d n hx he i hi) hs)).copy
    filter_upwards [eventually_ge_atTop i] with N hN; let h:= U.lyr N (hi.trans hN); unfold base; rw [dif_pos (hi.trans hN), h.takes _ hi hN]
    let Z:=(U.song N).tone i; let y:= ((U.song N).tone r).index.symm x; change (Z.index y,Lacing.terrain H N n (hol G) i Z (Z.index y))=Lacing.Face H N n (hol G) i Z y; unfold Lacing.terrain; rw [Z.index.symm_apply_apply]; exact Prod.ext (((h.earned.earned i hi hN).currents y).symm.trans (sees ..).symm) rfl
end Pans
end YM.UVExtension.Mast
