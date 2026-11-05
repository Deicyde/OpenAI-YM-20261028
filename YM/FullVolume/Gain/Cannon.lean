import YM.FullVolume.Gain.Dance
/-!
# Solve equations in Rally centered with real scalar intrinsic.Lip full.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Contest
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
local notation "T"=> Fin (N+1)
local notation "ℒ"=> Fin.last N
local notation "Ω"=> A.B.a.clock.hatBeta
include Φ O p
lemma shineTop : ∃ P:FullVolume.Amp.Pulse ℝ (World (O.plan N le_rfl)) glint, Hits (f:=fun y=>World.ready (Yawn O.receives y)) (ContinuousLinearMap.id ℝ ℝ) (p.pitch (Fin.last N)) P:=bootP R O.receives Φ.Lead Φ.Clever Φ.voices (Φ.largeG.scale N) (Φ.largeG.radiusY N) Φ.gate (p.mildS Φ _ le_rfl)
lemma shinePoint (i:Fin N): (∃ P:FullVolume.Amp.Pulse (ℝ × World (O.plan (i.val+1) i.isLt)) (World (O.plan i.val i.isLt.le)) glint, Hits (f:=fun y=>World.ready (Pass.reading (L.prim N i n i.isLt) (O.walks i i.isLt) y)) (zipB (O.plan (i.val+1) i.isLt)) (p.pose Φ O i.succ) P)∧∃ P:FullVolume.Amp.Pulse (ℝ × World (O.plan (i.val+1) i.isLt)) ℝ (stow A.B.a v i), Hits (f:=drum (L.prim N i n i.isLt)) (zipB (O.plan (i.val+1) i.isLt)) (p.pose Φ O i.succ) P:= incomeP Φ.SimpleR (L.prim N i n i.isLt) Φ.Shears Φ.Saved (O.walks i i.isLt) (Φ.largeG.scale _) Φ.voices Φ.earn (x:=p.pose Φ O i.succ) (p.mildS Φ _ i.isLt) (p.sparkN Φ O i.succ)
-- coerce wages
def widthB (a:Levels G)(m:ℕ):= normedWidth (a.clock.hatBeta m)
abbrev due (p:Contest N n L)(k:T): ℝ:=widthB A.B.a k*p.pitch k
omit O p
lemma spare (k:T)(_h:Nonempty (Contest N n L)): (0 < widthB A.B.a k ∧ widthB A.B.a k ≤ 1/128):=by
  let x:= Ω k; have hp:=Φ.largeG.scale k
  have hh:=widthP hp.floor; have he:= hp.grade; have hv:= hp.steps; have hZ:=hp.dust
  exact ⟨hh,show normedWidth x ≤_ from by unfold x; nlinarith⟩
lemma braceP (m:ℕ): 0<brace A.B.a m:= mul_pos (widthP (Φ.largeG.scale m|>.floor)) (Φ.largeG.scale m|>.floor)
include p
lemma dueP (i:T) : 17/20 ≤ p.due i ∧ p.due i ≤ 23/20:= p.mildS Φ _ (headB i)
include O
def vault : Rally N (rom O) where
   initB := (shineTop Φ O p).choose
   beams i:= (shinePoint Φ O p i).1.choose
   w i:=brace A.B.a i
   feeB i:=2*p.due i
   wt i:=widthB A.B.a i
   span i:=stow A.B.a v i
   lum i:= (shinePoint Φ O p i).2.choose
   wPos i:= braceP Φ i
   fee₁ i:=by linarith [(dueP Φ p i).1]
   wtP i:=by rw [Real.norm_of_nonneg (le_of_lt (spare Φ i ⟨p⟩).1)]; exact (spare Φ i ⟨p⟩).2.trans (by norm_num)
   accounts i:=by
      rw [show ∑ k∈ FullVolume.Amp.prior N i, stow A.B.a v k=∑ k∈Finset.range i,stow A.B.a v k from ?_]; exact Φ.largeG.radiusB i
      apply Finset.sum_bij (fun k _=>k.val)
      · simpa [FullVolume.Amp.prior] -- duplicate
      · exact fun _ _ _ _=> Fin.ext
      · intro k hk; have hp:= Finset.mem_range.mp hk; have hz:k<N:=lt_of_lt_of_le hp (headB i); exact ⟨⟨k,hz⟩,by simp [FullVolume.Amp.prior,hp],rfl⟩
      exact fun _ _=>rfl
-- Global comparison any competitor.
def ran (p p':Contest N n L) (i:T):= p'.pitch i-p.pitch i
def realm (p:Contest N n L)(i:T): rom O i:= World.ready ((p.chair Φ O i):Completion (lobby O i))
def jar (p p':Contest N n L)(i:T):= realm Φ O p' i-realm Φ O p i
abbrev beta (p:Contest N n L)(i:T):= (p.trail i).beta
def weightA:= ‖(ran p p',jar Φ O p p')‖
include p'
lemma hope (i:T): ‖p'.pose Φ O i-p.pose Φ O i‖= max ‖ran p p' i‖ ‖jar Φ O p p' i‖:= by
    let e:=zipped (O.plan i (headB i))
    let x:=p.pose Φ O i; let y:=p'.pose Φ O i
    let f:=zipB (O.plan i (headB i)); suffices hv: ‖y-x‖=‖f y-f x‖ from hv -- defeq
    exact (dist_eq_norm ..).symm.trans ((e.1.dist_eq y x).symm.trans (dist_eq_norm ..))
lemma highA (i:T):‖p'.pose Φ O i-p.pose Φ O i‖≤weightA Φ O p p':=by rw [hope]; exact max_le ((norm_le_pi_norm (ran p p') i).trans (le_max_left ..)) ((norm_le_pi_norm (jar Φ O p p') i).trans (le_max_right ..))
lemma beauty (i:Fin N): ‖jar Φ O p p' i.castSucc‖≤8*glint*weightA Φ O p p' ∧ ‖p'.owed i-p.owed i‖≤4*stow A.B.a v i*weightA Φ O p p':=by
    let H:=L.prim N i n i.isLt; let j:=i.succ
    have hx:=(vault Φ O p).lum i|>.cost; change 0≤2*fn A.B.a i v at hx; have hu:=p'.pose Φ O i.succ
    obtain ⟨ha,hV⟩:= ticket Φ.SimpleR H Φ.Shears Φ.Saved (O.walks i i.isLt) (Φ.largeG.scale _) Φ.voices Φ.earn (x:=p.pose Φ O i.succ) (p.mildS Φ _ i.isLt) (p.sparkN Φ O i.succ) (p'.pose Φ O i.succ) (p'.mildS Φ _ i.isLt) (p'.sparkN Φ O i.succ)
    have he := highA Φ O p p' j
    have h:= p.forthB Φ O i; have hh:= p'.forthB Φ O i; refine ⟨?_,?_⟩; · unfold jar realm; rw [←hh.1, ← h.1]; exact ha.trans (mul_le_mul_of_nonneg_left he (by norm_num [glint]))
    rw [←hh.2,←h.2,stow]; exact hV.trans ((mul_le_mul_of_nonneg_left he (show 0≤8*fn A.B.a i v from (by linarith))).trans_eq (by ring))
lemma beauty_last: ‖jar Φ O p p' ℒ‖ ≤8*glint*weightA Φ O p p':=by
   unfold jar realm; rw [←p'.nestTop Φ O,←p.nestTop Φ O]; apply le_trans (bootD R O.receives Φ.Lead Φ.Clever Φ.voices (Φ.largeG.scale _) (Φ.largeG.radiusY _) Φ.gate (p.mildS Φ _ le_rfl) (p'.mildS Φ _ le_rfl)); exact mul_le_mul_of_nonneg_left ((le_max_left ‖ran p p' ℒ‖ _).trans (by rw [← hope Φ O p p' ℒ]; exact highA ..)) (by norm_num [glint])
omit O
lemma riseB (i:T): p'.beta i-p.beta i= brace A.B.a i*ran p p' i*(due p' i+ due p i) := by
    let x:= Ω i; rw [beta,beta,←p'.spoken Φ i (headB i),←p.spoken Φ i (headB i)]; unfold ran pitch brace fromLambda due widthB Pass.salary pitch; ring
omit Φ in
lemma strideB (i:T): p'.beta i-p.beta i=(p'.trail 0).beta-(p.trail 0).beta-∑ k∈FullVolume.Amp.prior N i,(p'.owed k-p.owed k):=by
   unfold beta; rw [p'.priorB,p.priorB,sum_add_distrib,sum_add_distrib,sum_sub_distrib]; ring
include O
set_option quotPrecheck false
local notation "δ"=> (p'.trail 0).beta-(p.trail 0).beta
lemma scaleV (i:T): ‖ran p p' i‖ ≤ ‖δ‖/ (brace A.B.a i) +4*glint*weightA Φ O p p':=by
  let z:=p'.beta i-p.beta i; let r:=brace A.B.a i; let u:= weightA Φ O p p'; have hp:0<r:= braceP Φ i
  have hv: r*‖ran p p' i‖ ≤ ‖z‖:=by
    unfold z; rw [riseB Φ p p',norm_mul,norm_mul,Real.norm_of_nonneg hp.le]; apply le_mul_of_one_le_right (by positivity); apply le_trans _ (le_abs_self (due p' i+due p i)); linarith [(p.dueP Φ i).1,(p'.dueP Φ i).1]
  have hu : ‖z‖≤ ‖δ‖ + 4*glint*r*u:=by
    unfold z; rw [strideB p p']; apply (norm_sub_le ..).trans; apply add_le_add_right; apply (norm_sum_le ..).trans; calc
        _ ≤ ∑ k∈ FullVolume.Amp.prior N i, stow A.B.a v k * (4*u) := Finset.sum_le_sum fun k _=> (beauty Φ O p p' k|>.2).trans_eq (by unfold u; ring)
        _ ≤ _:=by rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (show ∑ k ∈ FullVolume.Amp.prior N i, stow A.B.a v k ≤ glint*r from (vault Φ O p|>.accounts i)) (by unfold u weightA; positivity)).trans_eq (by ring)
  rw [show ‖δ‖/brace A.B.a i+4*glint*(weightA Φ O p p')= (‖δ‖+ 4*glint*r*u)/r from ?_, le_div_iff₀ hp,mul_comm]; exact hv.trans hu
  change ‖δ‖/r+ 4*glint*u=(‖δ‖+4*glint*r*u)/_; field_simp
end YM.PhysicalNext.Repeat.Muse.Contest
