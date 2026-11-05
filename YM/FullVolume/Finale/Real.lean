import YM.FullVolume.Tess.End
/-
 Crucial: the auxiliary real extension used to enroll an orbit of origins was not a calibrated history below them. Here transfer the (same literal) charts to the TRUE recursion. Do not change the Kin or support calendars.H. Recipe deterministic for trials.
 -/
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
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
variable (Z:Face T W)
/-- Actual reps. Includes reference stage0; no Berry padding except beyond cutoff. -/
private def arcR:= R.alloy.B.bake.make (fun N p=> (Z.F p N).trail)
private def arcD (d N p :ℕ): TransferData ((Labels.frames G).level d) (arcR Z) N p:= by let V:= Z.owns.record d N p; exact ⟨V.entries,V.terminal⟩
def novel (Z:Face T W):Family G:= ⟨arcR Z, Next.Foundations.hol G, Labels.frames G, Next.Foundations.localSection G,R.t,arcD Z⟩
local notation "X"=> Z.novel
local notation "S!"=> R.family.S
lemma motionR (N p:ℕ) : (novel Z).path.rep N p=(Z.F p N).trail:=rfl
lemma pricedR {N:ℕ} : Competes T.L.tunes p N 0 (Z.novel.path.rep N p):= (Z.F p N).rises -- N variable
local notation "C"=> Z.V T W
lemma movedR (N p m:ℕ)(hm:m<N): R.alloy.B.Move N m p ((novel Z).path.rep N p m) ((novel Z).path.rep N p (m+1)):= ((T.L.disappears (pricedR Z)).persists m (Nat.zero_le m) hm).continues.1
lemma meshSound d: ((Z.novel).localSection d).Sound (Z.novel).params:= R.makes.sections _
lemma stencil d N p (hv:R.family.ref d ≤ N) : ∀ x∈(Z.novel.localSection d).stencil, ∀ i:Axis,20*((x i).natAbs+1) ≤ (Z.novel.side N p).val:= R.makes.places _ _ _ hv
lemma reachesP (d:ℕ) : d+3 ≤ (novel Z).path.levels.clock.J ((novel Z).ref d) ∧ ∀ m ≥ R.family.ref d, d+1 ≤ ((P!).params m).order∧ d≤ ((P!).params m).power:= R.makes.stages _
lemma liftoff (d N p :ℕ)(hp:R.family.ref d ≤ N): let V:=(Z.novel).factory d N p; V.Based R.family.params (R.family.localSection d) (R.family.ref d):=by
     have hh(m)(hx:R.family.ref d ≤ m)(h:m ≤ N): (Z.novel).path.rep N p m=(Z.V T W).path.rep N p m:= (Z.score.palm N p (show 1 ≤ N from (W.late d).trans hp) _ (show 1 ≤ m from (W.late d).trans hx) h).symm
     intro V; let U:=(C).factory d N p; let H:=(C).path; have h : U.Based (C|>.params) ((C).localSection d) (R.family.ref d):= Z.owns.priced d N p hp
     let Y:= (X|>.path)
     have hN:Y.rep N p N=H.rep N p N:= hh N hp le_rfl
     refine ⟨hp,fun m he hv v=> ?_,fun m he hv v=> ?_, h.back,h.front,h.linear,h.bare_coord,h.bare_germ, fun v u=> ?_,?_,h.reads,h.unit_coord,h.realForm,h.orients⟩
     · exact (show Y.rep N p m= _ from hh m he hv).symm ▸ (show (V.entries m v).Format 0 (R.family.params) (H.rep N p m) from h.format m he hv v)
     · change _; -- rw may transport requires H↑ Y.path.Level true. explicit
       exact (show Y.rep N p m= _ from hh m he hv).symm ▸ (show (V.entries m v).remBound 0 (H.rep N p m) _ _ from h.cap m he hv v)
     · -- `initial` doesn't use rep. freeze
       have hz:(H.S.a N:ℂ)^d *↑((H.rep N p N).eval u)* (initial ((C).localSection d) H N p v 0 u)=(Y.S.a N:ℂ)^d * ↑((Y.rep N p N).eval u)* (initial (R.family.localSection d) Y N p v 0 u):= by rw [hN]; rfl
       -- orientation issue rew
       exact (show (V.entries N v).density 0 (R.family.localSection d) (Y.rep N p N) u= _ from congr_arg (fun x=> (V.entries N v).density 0 (R.family.localSection d) x u) hN).trans ((h.encode v u).trans hz)
     intro m he hv v
     have hp:= hh m he hv.le; have hP:=hh (m+1) (he.trans m.le_succ) hv
     change (V.entries m v).density 0 _ ((X).path.rep N p m) = _
     rw [hp]; change _ = (((S!).block m).val:ℂ)^d • (Y.levels.clock.op m p).push ((novel Z|>.path).rep N p (m+1)|>.beta) ((V.entries (m+1) v).density 0 _ ((Z.novel).path.rep N p (m+1))) -- S!.block syntax
     rw [hP]; exact h.unnormalized m he hv v
lemma sections (d:ℕ): Z.novel.localSection d= R.family.localSection d:=rfl
lemma lengthA: (Z.novel).path.levels= R.family.path.levels:=rfl
-- Explicit orbit equating physical correlations including derivatives.W.Seam.
lemma novelO (N p d) (v:R.family.label d)(o:Site (R.family.side N p)): (Z.novel).O N p v o=(C).O N p v o:=rfl
lemma novelG (N p :ℕ)(hv:1 ≤ N){n:ℕ}(v:Fin n→ R.family.book.Token)(o:Fin n→Site (R.family.side N p)): Z.novel.numeric N p v o=(C).numeric N p v o:=by
    have hz: Z.novel.beta N p=(C).beta N p:=congr_arg Rep.beta (Z.score.palm N p hv N hv le_rfl).symm
    rw [Family.num,Family.num,hz]; rfl
-- center exact
lemma centralR : (centerF T W|>.novel)=R.family:=rfl
-- Eval physical account
abbrev parameter (F: Fan T W p) (w:sun)(v:sun):ℝ:= ((F.film (scaleSun w v)).F p 0).bonusB
lemma price_arc (F:Fan T W p)(w:sun)(N:ℕ)(v:sun): let Z:= F.film (scaleSun w v); (Z.novel.path.rep N p 0).beta= R.family.path.levels.clock.bar+(F.spin.val*w.val* Contest.beamWidth R.alloy.B.a)*v.val:=by
     intro Z; rw [show (Z.novel.path.rep N p 0).beta=_ from F.presents N _]; unfold Contest.ask; change R.alloy.B.a.clock.bar+(v.val*w.val*F.spin.val)*Contest.beamWidth R.alloy.B.a=R.alloy.B.a.clock.bar+_; ring
abbrev physF (F:Fan T W p){n:ℕ}(v:Fin n→R.family.book.Token)(l:List (Reach n))(w:sun)(N:ℕ)(s:sun) := squall (R.family.S.a N) l (Extraction.lifted (F.film (scaleSun w s)|>.novel) N p v)
lemma onReal (F:Fan T W p){n:ℕ} (v:Fin n→R.family.book.Token) (l:List (Reach n))(w:sun)(N:ℕ)(hn:1≤N) (s:sun): physF F v l w N s= Fan.shiftH F v l w N s:= congr_arg (squall _ _) (funext fun x=> (F.film (scaleSun w s)).novelG N p hn v (wrap _ ∘ x))
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.liftoff
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.price_arc
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.onReal
