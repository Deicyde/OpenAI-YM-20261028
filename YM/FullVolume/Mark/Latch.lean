import YM.FullVolume.Mark.Carts
import YM.MergeProof.Renaissance
/-!
# Strengthened one-source coupons. Stamp before the inverse and orbit:
keep S.C. actual cables and ink, seats for the contact books with all supports.
Unused F presentations not supplied with new motions or selections. Root10
entropy is in the usual Canonical coordinates. Need quantitative analytic &
rep continuity of these specific receipts to propagate graphs; not postulates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H:History G) (N p m:ℕ)(Y:Hol G)
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "R"=> H.rep N p m
local notation "E"=> H.rep N p (m+1)
local notation "c"=> H.S.side m p
local notation "f"=> H.S.side (m+1) p
local notation "L"=> H.S.block m
set_option quotPrecheck false
abbrev Pin (F:Labels.Frame G d) (n:Side):= F.Coeff× File G n
def tell {n:Side} (a:Pin F n):= book a.1 a.2
def closeK {n:Side}{R0:Rep G n}(K : Keeper R0.p R0.activities)(P:Coefficient F n): Pin F n :=(P.x,capture P K)
structure Span (P:Coefficient F (H.S.side m p))(α : Config G (H.S.side (m+1) p)→ℂ)(ρ:Res G (H.S.side (m+1) p)) (δ:ℂ) (Q:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(A:Wing→Prop)(U:Config G (H.S.side (m+1) p)→ℂ)(lead:F.Coeff)(b v y:ℝ): Prop where -- binder
  earns: Gig B H N p m Y U P lead b v
  songs: Tale A 0 0 (((H.S.block m).val:ℂ)^d) α ρ (profile (H.rep N p m).activities P.forced) δ y v Q
section span
variable {B H N p m Y}{X:Wing→Prop}{Z:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
lemma Span.weaken {g Q U α χ u a b v a' b' v'}(h:Span B H N p m Y Q g U α Z X χ u a b v)(h₁:a ≤ a')(h₂:b≤b')(hq:v≤v'):Span B H N p m Y Q g U α Z X χ u a' b' v':= ⟨h.earns.weaken h₁ h₂, h.songs.climb le_rfl hq h₂⟩
lemma Span.close {g Q U α χ u a b v}(K:Keeper (H.rep N p m).p (H.rep N p m).activities)(h:Span B H N p m Y Q g U α Z X χ u a b v) (hp:H.Selected)(hm:m≤N):Span B H N p m Y (tell (closeK K Q)) g U α Z X χ u a b v:=by
   let P:=book Q.x (capture Q K); have he:= h.earns.format
   refine ⟨⟨invest Q K he,(Matric.pays Q K B he h.earns.bound (hp.represents N p m hm).good).trans h.earns.agrees,h.earns.leadP,?_⟩,?_⟩ -- rw
   · obtain ⟨a,b,hv,hx⟩:= h.earns.future; exact ⟨a,b,wages Q K he hv,hx⟩
   rw [show profile (H.rep N p m).activities (tell (closeK K Q)).forced=_ from profited Q K]; exact h.songs
end span
open Extra.Histories.InputColumn
structure Plate (F:Labels.Frame G d)(n n':Side) where
  main : F.Index → Pin F n'
  tint : ℕ→ (Config G n→ℂ)→ Pin F n'
  ink : ℕ→ (Config G n→ℂ)→ Pin F n'
namespace Plate
-- apply regular tint by INDEX (although eventual actual formula need not distinguish indices within a support)
variable (P:Plate F (H.S.side (m+1) p) (H.S.side m p))
structure Prints (T:Heading F)(u ζ v:ℝ)(S:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(X:Wing→Prop):Prop where
  heading z: F.coeffSize (T.map z) ≤ u * F.coeffSize z ∧ F.coeffSize (T.map.symm z) ≤ u*F.coeffSize z
  main i:let x:= Size.axis F i; let Q:= Extra.Histories.primary (0:Site f) x
    Span B H N p m Y (tell (P.main i)) (Q.exponentialEntry 0 B E) 0 (x 0) S X (Q.density 0 B E) (T.leads L x) (ζ*F.coeffSize (F.core x)) (u*F.coeffSize (vowel F L (F.core x))) v
  regular i U t: let b:= mapSeat (n:=f) i; let x:=(E).p.mass b t -- f unknown in mapSeat
    RegFit E 0 d Y b U→ (E).p.supBounds 0 b U t→ Span B H N p m Y (tell (P.tint i U)) (masked (E).p.threshold b U) 0 0 S X (Extra.Histories.salary (E) b U) 0 (ζ*x) (ζ*x) (2*x)
  forced i U t: let a:=(E).p.mass ((E).activities.forced i).support t
    U≠0→ X (.gasKey i)→ SlotFit E 0 i U→ 0 ≤ t → (∀ V, ‖U V‖ ≤ t) → Span B H N p m Y (tell (P.ink i U)) 0 (exactGas (E).activities i U) 0 S X (Extra.Histories.fare E i U) 0 (ζ*(a/κ)) (ζ*(a/κ)) (2*a)
  blank i: P.ink i 0=0
end Plate
section stack
variable {ι:Type}[Nonempty ι][Countable ι]
  {g: ι→ Config G (H.S.side (m+1) p)→ℂ}{Q:ι→ Coefficient F (H.S.side m p)}{v:ι→ F.Coeff} {a b w:ι→ℝ}
lemma wind {X:Wing→Prop} (q:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(hq: SoundDoor (H.levels.clock.op m p) q)
    (h:H.Selected)(hm:m≤N){f':ι→ Config G (H.S.side (m+1) p)→ℂ}{w':ι→ Res G (H.S.side (m+1) p)}{t:ι→ℂ}{φ:Config G (H.S.side (m+1) p)→ℂ}{ψ:Res G (H.S.side (m+1) p)}{σ:ℂ}(hp:∀ j,Span B H N p m Y (Q j) (f' j) (w' j) (t j) q X (g j) (v j) (a j) (b j) (w j))(hg:∀ U,HasSum (fun i=>f' i U) (φ U))(hx:∀ i U,HasSum (fun j=> w' j i U) (ψ i U))(ht:HasSum t σ)
    (hf:Dominated g)(hk:∀i,Measurable (g i)) (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable a)(ha:Summable b)(hζ:Summable w): Span B H N p m Y (Extra.Histories.merge (code ι) Q) φ ψ σ q X (fun V=> ∑' i,g i V) (∑' i,v i) (∑' i,a i) (∑' i,b i) (∑' i,w i):=by
   have hκ: 0< (kappa H m):= Real.sqrt_pos.2 (forcedPos ..)
   exact ⟨Gig.all_in B H N p m Y h hm (fun j=>(hp j).earns) hf hk hv hu ha, Tale.upon hq (fun j=>(hp j).songs) hg hx (fun i U=> profile_merge (code _) Q hκ (fun i=>(hp i).earns.bound) ha i U) ht ⟨fun i=>by
      obtain ⟨ι,p,h,z,ψ,H⟩:= (hp i).songs; exact sumBudget_credit H.purchase,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg (hp i).earns.bound,ha,le_rfl⟩⟩
end stack
lemma spanNone (X:Wing→Prop)(q:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)) {t u:ℝ}(ht:0≤t)(hu:0≤u) : Span B H N p m Y (book 0 0) 0 0 0 q X 0 0 t t u :=by
    let P:Coefficient F c:= book 0 0
    let S:= R
    have he: P.density 0 B S=0:=by
       funext V; have hf i:P.maskedTerm S i V=0:= congr_fun (map_zero (maskLinear ..)) _
       have hj i:P.marked S i V=0:=by simp [P,Coefficient.marked];
       have hx:P.exponentialEntry 0 B S V=0:=by
           change part B 0 S V 0 + ∑' i,P.maskedTerm S i V=0; simp only [map_zero,hf,tsum_zero,add_zero]
       change _ = (0:ℂ); unfold Coefficient.density; simp [hx,hj]
    have htP : profile S.activities P.forced=0:=by funext i j; simp [profile,cram,P]
    have hk :=Real.sqrt_pos.mpr (forcedPos H.levels m)
    refine ⟨⟨?_,?_ ,by simpa [P,Frame.coeffSize] using ht,0,0,?_ ,by simpa using ht⟩,?_⟩
    · exact ⟨fun i=>(regular0 S.p _ 0).1,fun i=>spot _ i,fun i=>rfl,fun _ _=> vanishing0 _ _ Y,fun i U h=> (h rfl).elim, fun i h=> (h rfl).elim,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
    · change P.density 0 B S = Extra.Histories.blast H N p m d 0; rw [he]; unfold Extra.Histories.blast; funext x; simp [StepData.push]
    · refine ⟨hk,le_rfl,le_rfl,⟨0,budget0 ..,fun i=>(regular0 ..).2⟩, fun i=>0,by rw [mul_zero]; exact budget0 ..,fun i=> ⟨le_rfl,fun U=> (norm_zero («E»:=ℂ)).le⟩⟩
    rw [show profile (H.rep N p m).activities (book (0:F.Coeff) 0).forced= _ from htP]; exact taped hu ht
end YM.MergeProof.Matric
