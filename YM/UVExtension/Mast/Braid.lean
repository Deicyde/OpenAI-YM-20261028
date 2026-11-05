import YM.UVExtension.Mast.Leathers
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


-- deterministic lens story. corners origin matches future.Adjust unit.
namespace Pans
open Motion Relay Remnant
variable (U:Pans S v d n r W L)
local notation "Y"=> U.song
local notation "Fι"=> ((frames G).level d).Coeff
set_option quotPrecheck false
private def vision (M N:ℕ) (x:(F).Coeff): Bucket F (A.B.a.budget M) O! (A.B.a.S.side M n):=by exact Lacing.Face H N n (hol G) M ((Y N).tone M) x
variable {k:ℕ}(he:∀ m:ℕ,r ≤ m → Course (L m))(ht:r ≤ k) (x:((frames G).level d).Coeff)
variable (g:∀ N i:ℕ, Solo ((frames G).level d) (Orchard.Path S v) n i)
def glove (i N:ℕ): Bucket F (A.B.a.budget i) O! (A.B.a.S.side i n):= Lacing.photo H N n O! i (g N i)
local notation "gl" => glove S v d n g
variable (hg:∀ᶠ i:ℕ in atTop, (g i k)= Relay.pair (Orchard.Path S v) i n (U.song i) (Extra.Histories.primary 0 x) 0) (hp':∀ (i:ℕ)(hi:k < i), Quired (L:=fun m _=> L m i) (Orchard.Path S v) i n (hol G) (U.song i) r k (g i) (Nat.le_of_lt hi)) -- hm motive ∀, lambda needed
local notation "arrives"=>UVExtension.Arrives
include hx he
set_option synthInstance.maxHeartbeats 80000
lemma beats (i:ℕ)(h0:r ≤ i)(x':ℕ→ (F).Coeff)(hP:arrives x'): arrives (fun N=>vision S v d n U i N (((Y N).tone i).index.symm (x' N))):=by
   have hp := Remnant.loops (f:=fun j=> U.base S v d n i j) (x:=x') (U.wakes S v R d n hx he _ h0) hP
   apply (hP.pair hp).copy; filter_upwards [eventually_ge_atTop i] with N hN
   have hq:=U.lyr N (h0.trans hN); let Z:=(U.song N).tone i; let y:= Z.index.symm (x' N); unfold base; rw [dif_pos (h0.trans hN), Lyrics.takes hq i h0 hN]; exact Prod.ext (show x' N= (Eye _ _ _ _).1 from (((Z.index.apply_symm_apply _).symm.trans ((hq.earned.earned i h0 hN).currents y).symm).trans (sees (Z.plays y) O! ((H).rep N n i) (Real.sqrt (T'|>.clock.forcedAllowance i))|>.symm))) rfl

lemma pillars (i:ℕ)(hi:r ≤ i)(x:Fι): arrives fun k=> stalls S v d n U i k x:=by
    let t:=glaring A.B.a i n; let f j:= fun _:Motion=> L i j; let V j:=fun _:Motion=> U.base S v d n (i+1) j; have h0:=hi.trans i.le_succ
    apply (wares (L:=f) («Y»:=V) t (fun _=>he i hi) (fun _=> U.wakes S v R d n hx he _ h0) x).1.copy
    filter_upwards [eventually_gt_atTop i] with j hj
    have h:= hx i hi; obtain ⟨T,hT,hK⟩:=(h.plays j hj).efforts
    exact (focal h.owns (L:=f j) («Y»:=V j) (fun _=>hT) hK (fun _=> (U.circ S v R d n hx he).light _ h0 _ hj) t x).symm

include ht hp' hg
set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
lemma chord (j:ℕ)(h:r ≤ j)(hK:j ≤ k): arrives (gl j)∧ arrives (fun N=> ((Y N).tone j).index (g N j).a):=by
   induction hK using Nat.decreasingInduction with
   | self =>
      constructor; swap
      · apply (UVExtension.Arrives.steady x).copy; filter_upwards [hg] with i hi; rw [hi]; exact (((Y i).tone k).index.apply_symm_apply ..).symm
      let V j:= vision S v d n U k j (((Y j).tone k).index.symm (-x))
      have hv: arrives V := beats S v R d n hx U he k ht (fun _=>-x) (UVExtension.Arrives.steady _)
      let X:ℕ→ Bool→ Bucket F (A.B.a.budget k) O! (A.B.a.S.side k n):= fun j i=> rooms (A.B.a.S.side k n) F O! _ (aisleN (code Bool) i) (twain (x,0) (V j) i)
      have hM(i:Bool) : arrives (fun n=> X n i):=by cases i; exact hv.post (rooms (A.B.a.S.side k n) F O! _ (aisleN (code Bool) false)).continuous; exact UVExtension.Arrives.steady (X 0 true)
      apply (UVExtension.Arrives.sum (f:=X) Finset.univ (fun i _=>hM i)).copy
      filter_upwards [eventually_ge_atTop k,hg] with N hN hG'
      let g':=(Orchard.Path S v).rep N n k; let y:= Real.sqrt (T'|>.clock.forcedAllowance k); let Z:=(U.song N).tone k; let U':Coefficient F (A.B.a.S.side k n):=Extra.Histories.primary (0:Site (A.B.a.S.side k n)) x
      let v':= -Z.index.symm U'.x; have hz:v'=Z.index.symm (-x):= (map_neg ..).symm
      let hq:=U.lyr N (ht.trans hN)
      have hw : Nonempty (Planned.GuardedAtom.Guard.Keeper g'.p g'.activities):=⟨Planned.GuardedAtom.Guard.Keeper.sufficient (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed ..) N k n hN)⟩
      have ha:Eligible U' O! g' y:=⟨hw,primary_format _,_, primary_rem _ (Real.sqrt_pos.mpr (forcedPos A.B.a k))⟩
      have ht:= (hq.earned.earned k ht hN).earns v'
      unfold glove; rw [hG']; change _=tracks H N n k O! (beside U' (Z.plays v')); rw [stanzaP H N n O! k U' (Z.plays v') ha (show Eligible _ _ _ _ from ⟨hw,ht.1,_,ht.2⟩)]; refine Finset.sum_congr rfl fun i _=>?_ ; cases i; rw [hz]; rfl
      have he' : tracks H N n k O! U'=(x,0):= by change Eye U' O! g' y=_; rw [show Eye U' O! g' y=_ from ha.vistas, Eligible.blankC ha|>.1,Eligible.blankC ha|>.2]; rfl
      rw [he']; rfl
   | of_succ i hi IH =>
      let z N:=RoutesF.rain (L i N) (gl (i+1) N|>.2) none
      have hp : arrives z:=(he i h).useP _ _ ((IH (h.trans i.le_succ)).1.post continuous_snd)
      let l:= fun N=> vision S v d n U i N (((Y N).tone i).index.symm (-(z N).1)); have hh : arrives l:= beats S v R d n hx U he i h _ (hp.post (continuous_fst.neg))
      let xi N a:= rooms (A.B.a.S.side i n) F O! _ (aisleN (code Bool) a) (twain (z N) (l N) a); let b N:=(g N (i+1)).a; have hS: arrives fun j=> ((Y j).tone i).index (b j):=by
         apply (Remnant.loops (f:=fun j=> (stalls S v d n U i j).toLinearMap) (U.pillars S v R d n hx he _ h) ((IH (h.trans i.le_succ)).2)).copy; filter_upwards [eventually_gt_atTop i] with j hj
         have ht:= LinearMap.congr_fun (sym S v R d n hx U i j h hj) (b j); apply ((stalls S v d n U i j).symm.injective); exact ((stalls S v d n U i j).symm_apply_apply _).trans ht
      have hA : ∀ᶠ j in atTop, (gl i j= ∑ a:Bool,xi j a)∧ (Y j|>.tone i|>.index (g j i).a)= ((Y j).tone i).index (b j)+ (z j).1:=by
         filter_upwards [eventually_gt_atTop k] with j hJ
         let Pp:=(U.song j).tone i; let x:= (z j).1
         obtain ⟨hr,hq⟩:= (Quired.aim (hp' j hJ) i h hi).delta; refine ⟨hq.trans ?_,?_⟩
         · have hh : -(Pp.index.symm x)= Pp.index.symm (-x):= (map_neg ..).symm; refine Finset.sum_congr rfl fun k _=>?_; change rooms _ F O! _ _ (twain _ (tracks H j n i O! (Pp.plays (-(Pp.index.symm x)))) k)=_; rw [hh]; rfl
         rw [hr,map_add,LinearEquiv.apply_symm_apply]; rfl
      have hf(i:Bool) : arrives (fun N=> xi N i):=by cases i; exact hh.post (rooms _ F O! _ _).continuous; exact hp.post (rooms _ F O! _ _).continuous
      exact ⟨(UVExtension.Arrives.sum Finset.univ (fun i _=> hf i)).copy (hA.mono fun _ h=> h.1.symm), (hS.plus (hp.post continuous_fst)).copy (hA.mono fun _ h=> h.2.symm)⟩
end Pans
end YM.UVExtension.Mast
