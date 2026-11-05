import YM.FullVolume.Gain.Motion
/-!
# Lyrics full records for **all** Competes V.t.Trail, common charts. Articulus. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {g:G.Simple}{v q d t t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable (Φ : Plato L q v d t') (O:Ops L N n) (p p':Contest N n L)
include Φ O p
namespace Contest
local notation "T"=> Fin (N+1)
local notation "ℒ"=> Fin.last N
local notation "Ω"=>A.B.a
omit Φ O p
abbrev headB (i:T):i.val≤N:=Nat.le_of_lt_succ i.isLt
abbrev lobby (O:Ops L N n) (i:Fin (N+1)) := Home (O.plan i.val (Nat.le_of_lt_succ i.isLt))
abbrev rom (O:Ops L N n)(i:Fin (N+1)) := World (O.plan i.val (Nat.le_of_lt_succ i.isLt))
def pitch (i:Fin (N+1)):= toLambda (A.B.a.clock.hatBeta i) (p.trail i).beta
abbrev chair (i:T): lobby O i:= homeP Φ O p i (headB i)
def pose (i:Fin (N+1)): ℝ × lobby O i:= (pitch p i,chair Φ O p i)
include Φ O p
lemma nestTop : World.ready (Yawn O.receives (p.pitch ℒ))=World.ready ((↑(p.chair Φ O ℒ)):Completion (lobby O ℒ)) := by
   let a:= A.B.a.clock.hatBeta N; let x:=p.pitch ℒ; have ht:fromLambda a x=(p.trail N).beta:= p.spoken Φ N le_rfl; have he:fromLambda a x ∈ band A.B.a N:=ht.symm ▸ p.contour N le_rfl; rw [Pass.readingOn O.receives he]
   have hp:=p.startStory Φ; apply congr_arg (fun x:lobby O ℒ=> World.ready ((x:Completion (lobby O ℒ)))); apply umpire (A:=A) (he:=_) (h:=p.home_observe Φ O N le_rfl)
   let z:=lips O.receives (⟨fromLambda a x,he⟩:band A.B.a N); exact z.property.trans (congr_arg Rep.activities ((congr_arg (Tent.launch (A:=A) N n) ht).trans hp.symm))
def owed (p:Contest N n L)(i:Fin N):ℝ:= (p.trail i).beta - (p.trail (i+1:ℕ)).beta-A.B.kin.alpha N i
lemma forthB (i:Fin N): World.ready (Pass.reading (L.prim N i.val n i.isLt) (O.walks i i.isLt) (p.pose Φ O i.succ))=World.ready ((↑(p.chair Φ O i.castSucc)):Completion (lobby O i.castSucc)) ∧ drum (L.prim N i.val n i.isLt) (p.pose Φ O i.succ)=p.owed i:=by
   obtain ⟨x,h,hp⟩:= p.twines i i.isLt; let C: Director (A:=A) N i n (O.plan (i+1) i.isLt):= ⟨x,h ▸ ⟨⟨p.homeP Φ O _ i.isLt,p.home_observe Φ O _ i.isLt⟩⟩⟩
   let f:=p.pitch i.succ; let H:=L.prim N i n i.isLt
   have hy:= Φ.largeG.scale (i.val+1)
   have hw: (C.val.val).activities=(p.trail i.succ).activities:= congr_arg Rep.activities h
   obtain ⟨hq,hZ⟩:= Pass.espy Φ.SimpleR H Φ.Shears Φ.Saved (O.walks i i.isLt) hy C (y:=f) (Eq.trans (p.spoken Φ _ i.isLt) ((congr_arg Rep.beta h).symm)) (Pass.samples hy (p.mildS Φ _ i.isLt) (show |f-f|≤ 2 from (by norm_num))) ((p.home_observe Φ O _ i.isLt).trans hw.symm) (p.homeN Φ O _ i.isLt) Φ.voices.1
   refine ⟨?_,?_⟩
   · let P:= chooseR H (O.walks i i.isLt) C; exact congr_arg World.ready (hq.symm.trans (congr_arg (fun x:lobby O (Fin.castSucc i)=> (x:Completion (lobby O i.castSucc))) (umpire (A:=A) _ (chair Φ O p i.castSucc) (P.property.trans (congr_arg Rep.activities hp.symm)) (p.home_observe Φ O _ i.isLt.le))))
   exact hZ.symm.trans (by unfold Delta; change (H.moment x).beta-x.val.beta-A.B.kin.alpha _ _=_; rw [← hp,h]; rfl)
lemma sparkCost (i: Fin (N+1)): ‖p.chair Φ O i‖ ≤ FullVolume.Amp.glint:=by
   induction i using Fin.lastCases with
   | last=>
     have hb:= bootN R O.receives Φ.Lead Φ.Clever Φ.voices (Φ.largeG.scale N) (Φ.largeG.radiusY N) (x:= p.pitch ℒ) (p.mildS Φ N le_rfl)
     rw [p.nestTop Φ O] at hb; have hf:‖p.chair Φ O ℒ‖≤4*t':=(Completion.norm_coe (p.chair Φ O ℒ)).symm.trans_le hb; linarith [FullVolume.Amp.tintP.1, Φ.gate]
   | cast i=>
     have hv:= termsN Φ.SimpleR (L.prim N i n i.isLt) Φ.Shears Φ.Saved (O.walks i i.isLt) (Φ.largeG.scale _) Φ.voices (x:=p.pose Φ O i.succ) (m:=i.val) (p.mildS Φ _ i.isLt) (p.homeN Φ O _ i.isLt)
     have he:=p.forthB Φ O i; have hx:‖p.chair Φ O i.castSucc‖ ≤ d:=calc
       _= ‖World.ready ((↑(p.chair Φ O i.castSucc)):Completion (lobby O i.castSucc))‖:= (Completion.norm_coe _).symm
       _ ≤ _:= congr_arg (fun x:World (O.plan i.val i.isLt.le)=> ‖x‖) he.1.symm |>.trans_le hv.1
     linarith [FullVolume.Amp.tintP.1, Φ.earn]
lemma sparkN (i: Fin (N+1)): ‖p.chair Φ O i‖ ≤ 1/8:= (p.sparkCost Φ O _).trans (by norm_num [FullVolume.Amp.glint])
omit Φ O in
lemma priorB (i:Fin (N+1)) : (p.trail i).beta=(p.trail 0).beta-∑ k∈prior N i,(p.owed k+A.B.kin.alpha N k):=by
   have hz (j:ℕ)(h:j≤N) : (p.trail j).beta=(p.trail 0).beta-∑ k∈prior N ⟨j,by omega⟩,(p.owed k+A.B.kin.alpha N k):=by
     induction j with
     | zero=>simp [FullVolume.Amp.prior]
     | succ j ih=>
       let k:Fin N:=⟨j,by omega⟩; let S:= FullVolume.Amp.prior N k.castSucc; have h':k∉S:=by simp [S,FullVolume.Amp.prior]
       have hp: FullVolume.Amp.prior N k.succ= insert k S:=by
         ext i; simp only [FullVolume.Amp.prior,mem_filter,Finset.mem_univ,true_and,S,Finset.mem_insert,Fin.val_castSucc,Fin.val_succ]; rw [Fin.ext_iff]; omega
       change _=_-∑ i∈FullVolume.Amp.prior N k.succ, _; rw [hp,sum_insert h']
       have he:p.owed k=(p.trail (j)).beta-(p.trail (j+1)).beta-A.B.kin.alpha N j:=rfl
       rw [he]; have hh:(p.trail j).beta=(p.trail 0).beta-∑ i∈ S,(p.owed i+A.B.kin.alpha N i):= ih (by omega); change _=_; rw [hh]; unfold k; dsimp only; ring
   exact hz i (headB i)
end Contest
end YM.PhysicalNext.Repeat.Muse
