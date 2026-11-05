import YM.FullVolume.Reel.Brew
/-! Retain complete actual calibrated columns. Odyssey equality with THAT Voice, Č columns and Koz echoes. Force and reads normalized through the frames, not zero-profile.
 -/
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Legato.Bandage.Boutique
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open YM.FullVolume Ray Paint Tower
variable {G:Gauge}{n N p m d:ℕ}{F:Labels.Frame G d} {H:History G}{Y:Hol G}{B:SectionData F} {L:Side}
variable {T₀:ℝ}
-- Solo charts.S factoring physical.A cost W(s) via pivot π at epoch-level.Color curvature per stamps.Weight.Q
namespace Stamp
variable (S:Tool F H N p m)(P:Voice F H p (m+1))
set_option quotPrecheck false
local notation "s₀"=> H.S.side m p
local notation "s₁"=> H.S.side (m+1) p
local notation "A_"=> (H.rep N p m)
local notation "R0"=> H.rep N p (m+1)
local notation "X"=> (H.levels.params (m+1)).columns
local notation "u'"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Q_"=> H.S.block m
local notation "u₀"=>((L.val:ℂ)^d)
variable (hP:Heard B H N p Y (m+1) P) (hY:H.Selected) (hm:m<N)(L:Side)
variable {T:Desk G (H.S.side (m+1) p)}(ht:Well (H.rep N p (m+1)) T (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
variable (Q:Gram F Y T ((H.levels.params (m+1)).columns))(hq:Q=Matric.measure hP S.up ht)
local notation "V_"=> pollen F Y T
local notation "Φ"=> H.levels.clock.op m p
variable (K:F.Index→ Essence G (H.S.side (m+1) p))(φ:F.Index→ Response G (H.S.side m p))(D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (V: Set Wing)(h:B.Sound Y)(he: SoundDoor (H.levels.clock.op m p) D) (hz:Chorus H N p (m+1) P)
variable (W:∀ i:Motion,Wing ≃ Wing)(hw:∀ z:Motion, ∃ Z: (H.rep N p (m+1)).activities.Moves z.1 ((H.levels.clock.op m p).ratio.embed 0), travelW z ((H.levels.clock.op m p).ratio.embed 0) Z= W z)
local notation "S'"=> ⋃ z:Motion,W z '' V
local notation "Vp"=> Q.scythe
local notation "Xs"=> H.rep N p (m+1)
local notation "p0"=> P.plays
local notation "n'"=> (0: Site s₀)
local notation "w_"=> fun i:Tally F=>S.portfolio Vp i
local notation "Zp"=> (0:Site s₁)
local notation "ζ"=> Size.axis F
-- qualification from outside.Do not cfg motif from S'.Cap.But actual Lambert stamps. Use Beam of all arms.P. Finite.A.
include hP ht hq hm h hY
lemma readyP (Q':F.Index)(hx:(V_ Q' (Vp Q')).Format 0 Y R0) :let z:=ζ Q';let u:=V_ Q' (Vp Q');let y:= p0 (P.index.symm z); u.x=y.x∧ u.exponentialEntry 0 B R0=y.exponentialEntry 0 B R0 ∧ profile (R0).activities u.forced=profile (R0).activities y.forced:=by
    intro z U A
    have hz: A.x=z:=(hP.currents _).trans (P.index.apply_symm_apply _); have hZ:=hP.earns (P.index.symm z); have hp : Coin.uses (Vp Q')=capture A S.up:=by rw [hq]; exact Matric.notations hP S.up ht z
    have ha : U=book A.x (capture A S.up):=by rw [hz,←hp]
    rw [ha]; exact ⟨rfl, Matric.expo A _ B hZ.1, Matric.profited A _⟩ -- ambiguity P support
structure Hinge (T:Desk G (H.S.side (m+1) p))(Q:Gram F Y T ((H.levels.params (m+1)).columns))(L:Side):Prop where
    holding (i:F.Index):let V₀:= Q.scythe i;let U₀:=pollen F Y T i V₀; ∃ v t,Fleet (H.rep N p (m+1)) (H.rep N p m) D V 0 0 ((L.val:ℂ)^d) (U₀.x 0) (U₀.exponentialEntry 0 B (H.rep N p (m+1))) (profile (H.rep N p (m+1)).activities U₀.forced) (profile (H.rep N p m).activities (S.shot i (Coin.uses V₀)).forced) v t (K i) (φ i)
    livelihood (i:Tally F):∃ v,(S.portfolio (fun i=>Q.scythe i) i).remBound 0 (H.rep N p m) (Real.sqrt (H.levels.clock.forcedAllowance m)) v
-- not based on physical degree? general L
variable (hQ:Hinge S K φ D V (B:=B) (Y:=Y) T Q L)
local notation "f_"=> fun i:Tally F=> P.index.symm (Motion.patch F i.1 (ζ i.2))
local notation "Lp"=> (u₀)
include hQ hw he hz
lemma spinsT (j:Tally F): let V':=f_ j; let i:=j.fst;
    let T:=(P.plays V'); ∃ a b,Fleet R0 A_ D S' 0 0 ((L.val:ℂ)^d) ((Motion.patch F i (Size.axis F j.2)) 0) (T.exponentialEntry 0 B R0) (profile (R0).activities T.forced) (profile (A_).activities (S.portfolio Q.scythe j).forced) a b (dials i 0 (W i) (K j.2)) (upwards i 0 (φ j.2)):=by
    intro V' i T'; obtain ⟨a,b,Hg⟩:= hQ.holding j.2
    have he':(Φ).ratio.embed 0=0:=Motion.embed_origin _
    obtain ⟨F0,hz'⟩:=hw i
    let R:= V_ j.2 (Vp j.2);let z:= ζ j.2; let v:= P.index.symm z;let s:= p0 v
    obtain ⟨hs,hf,hU⟩:= readyP S P hP hY hm ht Q hq h j.2 ((granted ht Y z (Vp j.2)).1) -- signature S parameters
    have hW: (W i : Equiv.Perm Wing)=travelW i ((Φ).ratio.embed 0) F0:=hz'.symm
    let V0: Set Wing:= W i '' V; have hX:(Wing.labelRoute F0) '' V= V0:=by unfold V0;rw [hW];rfl
    have hF:= (Hg.mobile i 0 he F0 (show Motion.scalar i ((L.val:ℂ)^d)= (L.val:ℂ)^d from by unfold Motion.scalar; split<;>simp)).loosen (Y:= S') (hX ▸ (subset_iUnion (fun i'=> (W i') '' V) i)) le_rfl le_rfl -- cast hX direction
    have hV : V'=Motion.patch F i v:= by apply P.index.injective; rw [← hP.moves]; change P.index (P.index.symm _)=Motion.patch F i (P.index (P.index.symm _));simp only [P.index.apply_symm_apply];rfl
    have hZs(u:Config G s₁):(Xs).eval u≠0:=(Tour.bright H hY N p (m+1) hm u).ne'
    have hP₁ : stepUp i (0:Site s₁) (R.exponentialEntry 0 B R0)= T'.exponentialEntry 0 B R0:=by rw [show R.exponentialEntry _ _ _ = _ from (show R.exponentialEntry 0 B R0=_ from hf)]; unfold T'; rw [hV]; exact chanting B H N p _ Y P h hP hz hY hm hZs v i
    have hP₂:floatUp i (0:Site s₁) (profile (Xs).activities R.forced)=profile (Xs).activities T'.forced:=by rw [show profile _ R.forced= _ from hU]; unfold T'; rw [hV]; exact hz.pages v i
    -- avoid moving equiv.P.redirect with hW orientation, keep on U family.
    rw [show travelW i ((Φ).ratio.embed 0) F0=W i from hz'] at hF; simp_rw [he',affine,Signed.act_zero,zero_add] at hF
    refine ⟨a,b,?_⟩; rw [← hP₁,← hP₂,show profile (A_).activities (S.portfolio Q.scythe j).forced= _ from (show profile (A_).activities (S.portfolio Q.scythe j).forced= floatUp i 0 (profile (A_).activities (S.shot j.2 (Coin.uses _)).forced) from foyer i 0 (S.whirl j.1) (S.shot j.2 (Coin.uses (Vp _)))),show Motion.patch F i z 0= scalar i (z 0) from ?_]; exact hF
    unfold Motion.patch scalar; split<;>simp only [Pi.star_apply,Push.Local.act_at_zero]<;> rfl
abbrev sprays (v:F.Coeff): Essence G (H.S.side (m+1) p):=fun j U=> ∑ i:Tally F,chips F v i * dials i.1 (0:Site (H.S.side (m+1) p)) (W i.1) (K i.2) j U
abbrev flutes (v:F.Coeff): Response G (H.S.side m p):=fun j U=> ∑ i:Tally F, chips F v i* upwards i.1 (0:Site (H.S.side m p)) (φ i.2) j U
lemma funeral (v:F.Coeff): let p':=P.plays v;let u:= p'.x;let i:= S.pages Q.scythe u
    ∃ a b,Fleet R0 A_ D S' 0 0 ((L.val:ℂ)^d) (u 0) (p'.exponentialEntry 0 B R0) (profile (R0).activities p'.forced) (profile (A_).activities i.forced) a b (sprays K W u) (flutes φ u):=by
    intro p' u i; choose a b hh using fun j=> spinsT S P hP hY hm L ht Q hq K φ D V h he hz W hw hQ j
    let α(z:Tally F):= Motion.patch F z.1 (ζ z.2); let f j:=p0 (P.index.symm (α j)); let U:= P.index v; let y:= chips F u; let V':= K
    let k0(j:Tally F):= S.portfolio (Vp) j
    let A j:= (y j) • dials (j.1) (0:Site s₁) (W j.1) (K j.2); let B' j:= y j • upwards j.1 (0:Site s₀) (φ j.2)
    have hX(j):= (hh j).dice (y j); have hx : u=U:= hP.currents v
    have h₁: (fun i' b=>∑' j:Tally F,A j i' b)=sprays K W u:=by funext i b; rw [tsum_fintype]; rfl
    have h₂:MergeProof.band B'= flutes φ u:=by funext i b; unfold MergeProof.band; rw [tsum_fintype]; rfl
    have hz(i:Tally F): profile (A_).activities (Extra.Histories.stretch (y i) (k0 i)).forced=y i • profile (A_).activities (k0 i).forced:= profile_scale ..
    choose b hxk using fun i:Tally F=> hQ.livelihood i
    rw [← h₁,← h₂]; refine ⟨_,_,Fleet.amassed he hX ?_ ?_ (fun i U=>?_) ?_ Summable.of_finite Summable.of_finite⟩ -- sigma ι indexed macro
    · let g':= (IsLinearMap.mk' _ (expoLinear (T:=B) _ _ hP.book (fun i=> (hP.earns i).2))).comp P.index.symm.toLinearMap;intro W
      rw [show p'.exponentialEntry 0 B (R0) W=(g' u) W from ?_, ← fixing F g' u, Finset.sum_apply]; exact hasSum_fintype _
      rw [hx]; change _=(p0 (P.index.symm (P.index v))).exponentialEntry _ _ _ _;rw [LinearEquiv.symm_apply_apply]
    · let g':=(IsLinearMap.mk' _ (inkL P.plays P.charge hP.book (fun i=>(hP.earns i).2))).comp P.index.symm.toLinearMap; intro p W
      rw [show profile (R0).activities p'.forced p W=(g' u) p W from ?_,← fixing F g' u]; simp_rw [Finset.sum_apply]; exact hasSum_fintype _
      rw [hx]; change _=profile (R0).activities (p0 (P.index.symm (P.index v))).forced _ W;rw [LinearEquiv.symm_apply_apply]
    · let k(i):= profile (A_).activities (Extra.Histories.stretch (y i) (k0 i)).forced; have hm:= profile_merge (code _) (fun j:Tally F=> (Extra.Histories.stretch (y j) (k0 j))) (Real.sqrt_pos.mpr (forcedPos ..)) (fun j=> stretch_rem _ (hxk j)) Summable.of_finite i U
      exact hm.congr_fun (fun v=> (congr_fun (congr_fun (hz v) i) U).symm)
    have hp:u 0=∑ z:Tally F,y z*α z 0:=by
       rw [show (∑ z:Tally F,y z*α z 0)= (∑ z:Tally F,y z • α z) 0 from (by rw [Finset.sum_apply];rfl)]; exact congr_fun (fixing F LinearMap.id u|>.symm) 0
    rw [hp]; exact hasSum_fintype _
end Stamp
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.Stamp.funeral
