import YM.FullVolume.Shroud.Shift
/-! pad all moving histories by changing ONLY unused level 0. Never ask it for marked transmission (or for Meaning of Calibration). All θ and field normalization use actual R'.record at higher levels. Startup at N=0 kept. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K'"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
def outing (p:ℕ):= (supply T p).choose
@[simp] lemma allowed (p:ℕ):0< outing T p:=(supply T p).choose_spec.1
-- gather choices for each p.N. used for request φ h, no paths.Prom.Adj.W for unused levels.Unknown center. Maybe require ghost unchanged when β=bar for stronger.
variable (F:∀ p N, Contest N p T.L)(hp:∀ p N, |(F p N).bonusB - R.alloy.B.a.clock.bar| ≤ outing T p)
def spirit (N p:ℕ): Trail L! p := if N=0 then R.T.history N p else update (F p N|>.trail) 0 (Muslin.adorn ((F p N).trail 0) ((F p N).bonusB-o))
namespace Spirit
local notation "s"=> spirit T F
local notation "A"=> (R.alloy.B.bake.make s)
lemma fades : spirit T F 0=R.T.history 0:=by funext p; unfold spirit; split; rfl; contradiction
variable {N m p:ℕ}
local notation "V'"=> (F p N)
local notation "P'"=> (F p N|>.trail)
lemma at_height (h:1 ≤ N)(i:ℕ)(he:1 ≤ i):(A).rep N p i=(F p N).trail i:=by change s N p i=_; unfold spirit; rw [if_neg (by omega)]; exact Function.update_of_ne (by omega : i≠0) _ _
private lemma fixzero (h:1 ≤ N): (A).rep N p 0= Muslin.adorn (P' 0) ((V').bonusB - o):=by change s N p 0=_; unfold spirit; rw [if_neg (by omega),update_self]
include hp
lemma old_stamp (h:m<N): (R.alloy.B.bake.make (spirit T F)).Transfer N p m:=by
   let P:=F p N; let H:= (supply T p).choose_spec; have he:= hp p N; have hU:=P.rises.persists m (Nat.zero_le _) h; have hi: 1 ≤ N:= Nat.lt_of_le_of_lt (Nat.zero_le m) h; let Y:= R.alloy.B.bake.make (spirit T F)
   change Y.Transfer N p m
   cases m with
   | zero =>
       have hh:=H.2.2 N hi P he
       change ((A).rep N p 0).eval = _ ∧ |((A).rep N p 1).beta-((A).rep N p 0).beta - _| ≤ _
       rw [fixzero T F hi, at_height T F hi 1 le_rfl,show Y.β N p (0+1) = _ from congr_arg Rep.beta (at_height T F hi 1 le_rfl)]
       refine ⟨hh.2.trans hU.link,?_⟩
       let l:= G.slopeConstant *Real.log ((A).S.block 0).val; let x:= P.trail 0; let d:= P.bonusB-o
       change |(P.trail 1).beta-(x.beta-d)-l|≤ _; rw [show _- (x.beta-d)-l= (P.trail 1).beta - x.beta-l+d from by ring]; apply (abs_add_le ..).trans
       have hy:= headroom T P (m:=0) hi; change |(P.trail 1).beta-x.beta-l| ≤ _ at hy; have hf:|d|≤1/2:=he.trans H.2.1; exact (add_le_add hy hf).trans_eq (by rw [sub_add_cancel]; rfl)
   | succ m=>
       change ((A).rep N p (m+1)).eval=_ ∧ |((A).rep N p (m+1+1)).beta- ((A).rep N p (m+1)).beta-_|≤_
       rw [at_height T F hi (m+1) (by omega),at_height T F hi (m+1+1) (by omega),show Y.β N p (m+1+1)=_ from congr_arg Rep.beta (at_height T F hi (m+1+1) (by omega))];
       exact ⟨hU.link,hU.drift⟩
lemma bornMeet : (R.alloy.B.bake.make (spirit T F)).Selected:=by
   let Y:=R.alloy.B.bake.make (spirit T F);have hF N m p (h : m≤N): Lives (T.L.tunes) N m p ((F p N).trail m)∧ ((F p N).trail m).beta∈ band L! m:= (F p N).rises.prices _ (Nat.zero_le _) h
   have he p (i:ℕ): (A).rep 0 p i= (Issue.trail R.T).rep 0 p i:= congr_fun (congr_fun (fades T F) p) i
   have hZ i j:Y.β i j 0=o:=by
      change ((A).rep i j 0).beta = o; cases i with
      | zero=> rw [he]; exact R.T.choice.reaches ..
      | succ i=> rw [fixzero T F (by omega)]; unfold Muslin.adorn bonusB; dsimp only; ring
   have hy p N m(h : m≤ N): ((A).rep N p m).path= R.alloy.B.bake.path N m:=by
      rcases N with _|N
      · obtain rfl:m=0:=by omega
        rw [he]; exact ((R.T.sticks 0 p).prices 0 (Nat.zero_le 0) le_rfl).1.path
      cases m with
      | zero=> rw [fixzero T F (by omega)]; exact (hF _ _ _ h).1.path
      | succ m=> rw [at_height T F (by omega) (m+1) (by omega)]; exact (hF _ _ _ h).1.path
   refine ⟨fun N p q m h=> (hy p N m h).trans (hy q N m h).symm,fun N p m h=>?_,fun N p=>?_,fun i j k hk=> old_stamp T F hp hk,hZ, trajectory Y hZ (fun i j k hk=>old_stamp T F hp hk)⟩
   · have ht:= hF N m p h; rcases N with _|N
     · have hp:= R.T.choice.represents 0 p m h
       let T' := R.T.history 0 p m; refine ⟨?_,?_ ,?_,?_⟩
       · rw [he]; exact hp.vac
       · rw [he]; exact hp.clip
       · rw [he]; exact hp.good
       change ((A).rep 0 p m).beta ∈ _; rw [he]; exact hp.band
     cases m with
     | zero=>
        have hM:= fixzero T F (N:=N+1) (by omega) (p:=p)
        have hb: Y.β (N+1) p 0∈ band L! 0:=by rw [hZ]; unfold Shoot.band Calendar.hatBeta; rw [Schedule.scale_zero,mul_zero,add_zero]; have he:0<o := L!|>.clock.bar_pos; constructor<;>linarith
        refine ⟨by rw [hM]; exact ht.1.point,by rw [hM]; exact ht.1.clip,?_,hb⟩ -- hp path doesn't prove new R'.p.M ext tactic
        rw [hM]; exact (T.supply p|>.choose_spec|>.2.2 _ (by omega) (F p (N+1)) (hp ..)).1
     | succ m=>
        have H:=at_height T F (N:=N+1) (p:=p) (by omega) (m+1) (by omega); refine ⟨?_,?_,?_,?_⟩
        · rw [H]; exact ht.1.point
        · rw [H]; exact ht.1.clip
        · rw [H];exact ht.1.valid
        change ((A).rep _ _ (m+1)).beta∈ _; rw [H];exact ht.2
   cases N with
   | zero=> change ((A).rep 0 p 0).v=_∧ ((A).rep 0 p 0).eval= Wilson.bare ((A).rep 0 p 0).beta; rw [he];exact R.T.choice.starts ..
   | succ n=> change ((A).rep (n+1) p _).v=_∧((A).rep (n+1) p (n+1)).eval=Wilson.bare ((A).rep (n+1) p (n+1)).beta; rw [at_height T F (by omega) (n+1) (by omega)]; exact ⟨(F p (n+1)).rises.fromTop.scalars,(F p (n+1)).rises.fromTop.raw⟩
end Spirit
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Spirit.bornMeet
