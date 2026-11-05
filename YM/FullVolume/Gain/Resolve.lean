import YM.FullVolume.Gain.Cannon
/-!
# Unique solution, Beam lift assigned to actual fiber. Scalars. Will transport to ambient across N separately. -/
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
local notation "T"=> Fin (N+1)
local notation "ℒ"=> Fin.last N
local notation "Ω"=> A.B.a.clock.hatBeta
namespace Contest
include Φ O p p'
local notation "u"=> weightA Φ O p p'
set_option quotPrecheck false
def bonusB (p:Contest N n L):ℝ:= (p.trail 0).beta
local notation "δ" => bonusB p'-bonusB p
lemma track : u ≤ 2*‖δ‖/brace A.B.a 0:=by
  let r:=‖δ‖/(brace A.B.a 0); let v:= weightA Φ O p p'; have h:0≤ v:=norm_nonneg _; have hr:=braceP Φ 0; have hR:0≤r:=div_nonneg (norm_nonneg _) hr.le
  suffices hv:u ≤ r+8*glint*v by rw [mul_div_assoc]; change v≤2*r; change v≤_ at hv; rw [show glint=(1/128:ℝ) from rfl] at hv; linarith
  have hv:0≤r+8*glint*v:= add_nonneg hR (mul_nonneg (by norm_num [glint]) h)
  change v ≤ r+_
  refine max_le ((pi_norm_le_iff_of_nonneg hv).mpr (fun i=>?_)) ((pi_norm_le_iff_of_nonneg hv).mpr (Fin.lastCases (motive:=fun i=>‖jar Φ O p p' i‖≤_) ?_ ?_))
  · apply (scaleV Φ O p p' i).trans; exact add_le_add (div_le_div_of_nonneg_left (norm_nonneg _) hr (Φ.largeG.pride (i.val))) (mul_le_mul_of_nonneg_right (by norm_num [glint]) h)
  · exact (beauty_last Φ O p p').trans (le_add_of_nonneg_left hR)
  exact fun i=> (beauty Φ O p p' i|>.1).trans (le_add_of_nonneg_left hR)
lemma one (h:bonusB p'=bonusB p)(m:ℕ)(hm:m≤N): p'.trail m=p.trail m:=by
   have ha:=track Φ O p p'; rw [h,sub_self,norm_zero,mul_zero,zero_div] at ha; have hk := norm_le_zero_iff.mp ha; change (ran p p',jar Φ O p p')=0 at hk; have hV: ran p p'=0:= congr_arg Prod.fst hk; apply L.deterministic p'.rises p.rises _ hm
   rw [← p'.spoken Φ N le_rfl, ← p.spoken Φ N le_rfl]; exact congr_arg _ (show p'.pitch ℒ=p.pitch ℒ from sub_eq_zero.mp (congr_fun hV ℒ))
lemma sense (hp:u ≤ lux): Rally.Facing (vault Φ O p) (ran p p') (jar Φ O p p') (bonusB p'-bonusB p):=by
   let r:=u; have hr(i:T):‖p'.pose Φ O i-p.pose Φ O i‖≤r:= highA ..
   have hf i: max ‖ran p p' i‖ ‖jar Φ O p p' i‖ ≤r:= hope Φ O p p' i ▸ hr i
   have hu : r ≤ 1/4:=hp.trans (by norm_num [lux])
   let V:=vault Φ O p
   have he(i:Fin N): sees (V.beams i) (ran p p' i.succ,jar Φ O p p' i.succ)=jar Φ O p p' i.castSucc∧ sees (V.lum i) (ran p p' i.succ,jar Φ O p p' i.succ)= p'.owed i-p.owed i:=by
     have h':= p.forthB Φ O i; have hh:= p'.forthB Φ O i; let e:=zipB (O.plan (i.val+1) i.isLt); let w:=p.pose Φ O i.succ; let x:=p'.pose Φ O i.succ
     have ha :‖x-w‖≤1/4:= (hr _).trans hu
     have hv:= (p.shinePoint Φ O i).1.choose_spec.jingle (y:=x) ha
     refine ⟨hv.trans (congr_arg₂ (fun a b:rom O i.castSucc => a-b) hh.1 h'.1), ((p.shinePoint Φ O i).2.choose_spec.jingle (y:=x) ha).trans (congr_arg₂ (·-·) hh.2 h'.2)⟩
   refine ⟨fun i=>((le_max_left ..).trans (hf i)).trans hp,fun i=>((le_max_right ..).trans (hf i)).trans hp,?_ ,fun i=>(he i).1.symm,fun i=>?_⟩
   · let x:=p'.pitch ℒ; have ht:‖x-p.pitch ℒ‖≤1/4:= ((le_max_left ..).trans (hf ℒ)).trans hu
     have hh:= (p.shineTop Φ O).choose_spec.jingle (y:=x) ht; exact (hh.trans (congr_arg₂ (fun a b:World (O.plan N le_rfl)=> a-b) (p'.nestTop Φ O) (p.nestTop Φ O))).symm
   change _=(V.feeB i)⁻¹*((V.w i)⁻¹*( _-∑ k∈ FullVolume.Amp.prior N i, sees (V.lum k) _) - V.wt i*_)
   simp_rw [fun i=>(he i).2]; rw [← show _= bonusB p'-bonusB p-∑ k∈FullVolume.Amp.prior N i,(p'.owed k-p.owed k) from p.strideB p' i, riseB Φ p p']; let w:=widthB A.B.a i
   have hx: p'.due i= w*ran p p' i+ p.due i:= by unfold w ran due; ring
   rw [hx]; have hb:= braceP Φ (i.val)
   have hk:1≤2*p.due i:=V.fee₁ i; have ha:2*p.due i ≠ 0:=by linarith
   change _=(2*p.due i)⁻¹*((brace A.B.a i)⁻¹*(brace A.B.a i*_ * _) - w*_); rw [eq_comm, inv_mul_eq_iff_eq_mul₀ ha]; rw [←mul_assoc, ← mul_assoc, inv_mul_cancel₀ hb.ne',one_mul]; ring
omit p p'
open FullVolume
variable {b:ℝ}
omit O
lemma born (hb:b∈ nearby A.B.a):∃ p:Contest N n L, bonusB p=b:=by
  obtain ⟨C⟩:= Arc.bought n N (L.supplier Φ.SimpleR) Φ.SimpleR Φ.firm 0 (Nat.zero_le _)
  obtain ⟨x,hx,h⟩:= C.covers hb
  exact ⟨⟨C.replay x,C.trials x hx,(show (C.replay x 0).beta=b from h).symm ▸ hb⟩,h⟩
-- nearby disk width unit stable relative brace
abbrev beamWidth (a:Levels G):= lux/4* brace a 0
def ask (a:Levels G)(w:ℝ):= a.clock.bar+w*beamWidth a
lemma raise : 0<beamWidth A.B.a:=mul_pos (div_pos (FullVolume.Amp.tintP.2) (by norm_num)) (braceP Φ 0)
lemma onLine (s:sun): ask A.B.a s∈ nearby A.B.a:=by
   let v:=beamWidth A.B.a; have ht:0<v:=raise Φ
   obtain ⟨k,hk⟩:=born (N:=0) (n:=0) Φ (interior_subset (centers A.B.a))
   have hh:= spare Φ (Fin.last 0) ⟨k⟩; have hp:widthB A.B.a 0 ≤1/128:= hh.2; have hx:=A.B.a.clock.bar_pos
   have he : v ≤ A.B.a.clock.bar/4:= by
      have hq : brace A.B.a 0 ≤ (1/128:ℝ)*A.B.a.clock.bar:=by
        have hv: Ω 0=A.B.a.clock.bar:=by simp [RG.Calendar.hatBeta]
        show _* _≤ _; rw [hv]; exact mul_le_mul_of_nonneg_right (hv ▸ hp) hx.le
      exact (mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤lux/4 by norm_num [lux])).trans (by unfold lux; linarith)
   change ask _ _ ∈ _; unfold ask FullVolume.nearby FullVolume.low FullVolume.high
   change _ ≤ _ ∧ _
   rw [Schedule.scale_zero]; unfold v at ht he; constructor <;> nlinarith [s.property.1,s.property.2] -- unfold v
set_option quotPrecheck false
include p O
lemma score (hb:bonusB p=A.B.a.clock.bar):∃ U:Box N (rom O), ‖U‖ ≤ lux ∧ ∀ s:sun,∀ p':Contest N n L, bonusB p'=ask A.B.a s →∀ i, p'.pitch i= p.pitch i+Beam.read _ s (U.1 i) ∧ realm Φ O p' i= realm Φ O p i+Beam.read _ s (U.2 i):=by
  let K:= vault Φ O p; let v:=beamWidth A.B.a; let b:=FullVolume.Amp.Beam.spark v
  have hp:= show 0<v from raise Φ
  have hh(i): ‖b‖≤ lux/4*K.w i:=by unfold b; rw [Beam.sparkN,Real.norm_of_nonneg hp.le]; apply mul_le_mul_of_nonneg_left (Φ.largeG.pride _) (by norm_num [lux])
  obtain ⟨U,⟨hr,hU⟩,-⟩:=K.payable hh
  refine ⟨U,hr,fun s p' hb' i=>?_⟩
  let y:=bonusB p'-bonusB p; have hs:y= FullVolume.Amp.Beam.read _ s b:=by unfold b y; rw [Beam.sparkL,smul_eq_mul,hb',hb,ask]; unfold v; ring
  have hh': weightA Φ O p p' ≤ lux:= by
      have hh':‖y‖≤ v:=by rw [hs]; exact (FullVolume.Amp.Beam.price ..).trans ((hh 0).trans_eq rfl) -- use .sparkN
      apply (track Φ O p p').trans; rw [div_le_iff₀ (braceP Φ 0)]; change 2*‖y‖ ≤ _; unfold v beamWidth at hh'; nlinarith [braceP Φ 0, FullVolume.Amp.tintP.2]
  obtain ⟨h,hv⟩:=K.south hh hr (ran p p') (jar Φ O p p') s hs (sense Φ O p p' hh') hU i
  exact ⟨h ▸ (by unfold ran; ring),hv ▸ (by unfold jar; abel)⟩
end Contest
end YM.PhysicalNext.Repeat.Muse
