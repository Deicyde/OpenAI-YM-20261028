import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tensors
import YM.MergeProof.Badlands
import YM.MergeProof.North.Focal
import YM.MergeProof.South.Rapt


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories  Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge} {n:Side} (C:Family G) (J j m p k N d:ℕ) {r:ℕ→ℕ}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "V'"=> Site (C.side J p)
local notation "Q"=> (hands C p J)
local notation "ξ"=> Mix.camp C p J
variable (a:Site (C.side j p))
-- path of offset marker T
-- uniqueness of parent at j=j matches embed.
def loops (i:ℕ) : Site (C.side i p):= if h:j ≤ i then (C.S.toDepth h p).embed a else (C.S.toDepth (by omega : i≤j) p).parent a
def bites (i:ℕ)(x:Name (Site (C.side J p))): Site (C.side i p):= affine ((Q x.1).1) (Mix.camp C p J i x.1) (if x.2 then loops C j p a i else 0)
local notation "o"=> bites C J j p a
local notation "v"=> loops C j p a
lemma vect (he:j ≤ k): v k=(C.S.toDepth he p).embed a:= dif_pos he
lemma same : v j=a:=by rw [vect C _ _ _ _ le_rfl]; change (C.S.toDepth (le_refl j) p).embed a = _; unfold Ratio.embed Schedule.toDepth; simp only [tsub_self,Schedule.steps]; rw [show ((1:Side).val :ℕ)=1 from rfl,one_smul,wrap_lift]
lemma vote (he:k ≤ j): v k=(C.S.toDepth he p).parent a:=by
    rcases he.lt_or_eq with h|rfl
    · rw [loops,dif_neg (by omega)]
    have ht:=same C _ p a; rw [vect C _ _ _ _ le_rfl] at ht; rw [same]; exact (by nth_rw 2 [← ht]; rw [Ratio.embed_parent])
lemma zeroMama (he:J ≤ k): (ξ k 0)=0:=by rw [Mix.camp,dif_pos he];exact (C.S.toDepth he p).root.map_zero
lemma P_on : Q 0=(1,false):= by let T:= Cells.center C.S p (le_refl J) 0; have h:T.omega 0=1:= T.omega_zero; have hh:¬ T.hand 0:= T.hand_zero; change dye (T.omega 0) (T.hand 0)=_; simp [h,hh,dye]
lemma biteF (i:V'): o k (i,false)=ξ k i:=by simp [bites,affine]
lemma biteT (he:J≤k): o k (0,true)=(v k):=by unfold bites; rw [show Q _= _ from P_on ..,zeroMama C J p k he]; simp [affine]
lemma bit (he:J ≤ k)(i:V')(b:Bool): o k (i,b)= affine (Q i).1 (ξ k i) (o k (0,b)):=by cases b; simp only [biteF,zeroMama C J p k he];simp [affine]; rw [biteT C J j p k a he]; unfold bites; simp
lemma elev (he:J ≤ k)(b:V'): ξ k b=(C.S.toDepth he p).embed b:=dif_pos he
lemma uphill (hk:J ≤ m): Migrating H m p N ξ:=⟨fun i hj _=>funext fun a=> Work.I03.camp_step C p (hk.trans hj) a⟩

lemma retina (hk:J≤j): Migrating H j p N o:=by
    refine ⟨fun i hj hn=> funext fun ⟨x,b⟩=>?_⟩; let T:=C.path.levels.clock.op i p; have hp: j ≤ i+1:= hj.trans i.le_succ
    have he:T.ratio.embed (ξ i x)=ξ (i+1) x:= Work.I03.camp_step C p (hk.trans hj) x
    cases b; exact (by dsimp only [Function.comp_apply];rw [biteF,biteF,← he])
    unfold Function.comp bites; simp only [ite_true]; rw [← he]; change T.ratio.root _ = _; unfold affine; rw [map_add, Ratio.root_embed,Ratio.root_embed,T.ratio.signed,vect C j p i a hj,vect C j p (i+1) a hp,embed_comp (C.S.toDepth hj p) T.ratio _]
lemma bitesParent {μ:ℕ}(hk:J ≤ k)(hm:k≤μ)(hi:μ≤j): (C.S.toDepth hm p).parent ∘ o μ=o k:=by
    funext x; rcases x with ⟨x,b⟩; let T:= C.S.toDepth hm p; have he:T.embed (ξ k x)=ξ μ x:=by rw [elev C J p k hk,elev C J p μ (hk.trans hm)]; exact (embed_comp (C.S.toDepth hk p) T (C.S.toDepth (hk.trans hm) p) x).symm
    cases b; dsimp only [Function.comp_apply]; rw [biteF,biteF,← he]; exact T.embed_parent _
    unfold Function.comp bites; simp only [ite_true]; rw [← he,Push.Local.parent_affine _ (C.S.toDepth_odd hm p),vote C j p μ a hi,vote C j p k a (hm.trans hi)]
    exact congr_arg (affine (Q x).1 (ξ k x)) (parent_nested T (C.S.toDepth hi p) _ (C.S.toDepth_odd hm p) (C.S.toDepth_odd hi p) _ |>.symm)
end
end YM.MergeProof.Ribbons
