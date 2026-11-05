import YM.FullVolume.Spiral.Nilot
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
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
set_option maxHeartbeats 480000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "p_"=> Home T
abbrev Ticket (A:Alloy X D)(N m n:ℕ):= {x : Flight A N m n // HasSlots x.val.p x.val.activities}
local notation "xA"=> Nilot T
local notation "C_"=> Ticket A N m n
def glades (x:ℝ × Nilot T): Ticket A N m n:= if h:fromLambda Ω x.1 ∈ band A.B.a (m+1) ∧ ‖x.2‖≤1 then ⟨(teacher (x.2.val) h.2 H.paid ⟨_,h.1⟩ 0|>.val),x.2.property⟩ else ⟨(teacher (T:=T) 0 (le_trans (b:=(0:ℝ)) (norm_zero).le zero_le_one) H.paid ⟨A.B.a.clock.hatBeta (m+1), by have := A.B.a.fits.delayed (m+1); constructor <;> linarith⟩ 0|>.val),(Nilot T).zero_mem⟩
structure ReadsF (C:Ticket A N m n)(x:ℝ × Nilot T):Prop where
    norm : ‖x.2‖≤1
    takes : C.val.val.beta=fromLambda Ω x.1
    bills : C.val.val.activities= observe T x.2.val
include H
lemma gleans (x:ℝ × Nilot T) (ht: fromLambda Ω x.1 ∈ band A.B.a (m+1))(hv:‖x.2‖≤1): ReadsF (glades H x) x:=by unfold glades; rw [dif_pos ⟨ht,hv⟩]; exact ⟨hv,rfl,rfl⟩
omit H
variable (V:Climate (A.B.a.clock.hatBeta (m+1)))
include V
lemma trailP (F:sun→ Ticket A N m n)(x y:ℝ× Nilot T)(ht:emcee Ω x.1)(hw:‖y.1‖≤1)(hg:∀ i:sun,ReadsF (F i) (x+i.val • y)):∃ Y,SectorOn (A:=A) (fun i=> (F i).val) Y:=by
    obtain ⟨U,hU⟩:= Pass.priced _ V ht hw
    have hL:= beta_eq A.B.valid m
    have ha: ∃ M:Mist A.B.a m (grand Ω) (joy Ω),∀ i:sun,(F i).val.val.beta=(M.peak i).val:= ⟨⟨U.knot,U.flow,U.poses,U.move⟩,fun i=> (hg i).takes.trans (hU i (Pass.s1 i _ V.grade)).symm⟩
    rw [show grand Ω=fire G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) from congr_arg grand hL, show joy Ω=thaw G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) from congr_arg joy hL] at ha; obtain ⟨M,hM⟩:=ha
    let X:Home T:= x.2.val; let Z:Home T:=y.2.val
    let f i:=(F i).val
    have hp0 i: (f i|>.val.p)=Q:= (f i).property.1.point
    have hA(i:sun): (f i).val.activities=observe T (X+i.val • Z):= (hg i).bills
    have he(i):Rain.listIn (f i).val= layout G (S) Q:=by unfold Rain.listIn; rw [hA]; rfl
    refine ⟨M,?_⟩; change SectorOn f M; constructor
    · exact hM
    · exact fun i j=> (he i).trans (he j).symm
    · intro A' j; simp_rw [hp0,hA]; let u x:= (observe T x).regularOccurrence Q j A'; let a:=u X; let b:=u Z
      refine ⟨fun i=>a+b*i,(FullVolume.Ray.ink.straight ..).rise (by norm_num),fun i=>?_⟩
      unfold a b u Activities.regularOccurrence; dsimp only; let V:=layout G (S) Q; have hp (x:Home T): (observe T x|>.reg)=V.reg:= rfl
      simp_rw [hp]; by_cases hz: Healthy (Q).threshold (V.reg j|>.support) A'
      · rw [masked_eq _ _ _ _ hz,masked_eq _ _ _ _ hz,masked_eq _ _ _ _ hz]; rw [mul_comm _ i.val]; rfl
      rw [masked_ne _ _ _ _ hz,masked_ne _ _ _ _ hz, masked_ne _ _ _ _ hz,zero_mul,zero_add]
    intro V j; simp_rw [hA]; let x:=(observe T X).K j V; let z:=(observe T Z).K j V
    exact ⟨_,(FullVolume.Ray.ink.straight x z).rise (by norm_num),fun i=>by rw [mul_comm z i.val]; rfl⟩
section often
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
-- bypass choice v by jumps. No Need Price against one Version.Body.Proofs.
variable (hp:choir q) {x:ℝ × Nilot T}{c:ℝ} (E: Ticket A N m n →Y) (h : ∀ F:sun→Ticket A N m n, (∃ Y', SectorOn (A:=A) (fun i=> (F i).val) Y') → Rebar (q/2) (phraseS (E∘ F)) c)
include H V h hp
lemma sprung (X:Ticket A N m n)(he : ReadsF X x)(hu:emcee Ω x.1): E X= E (glades H x):=by
    have hv := gleans H x (he.takes ▸ X.val.property.2) he.norm
    let Y:= glades H x; let f(s:sun):= if s.val=0 then X else Y
    have h':= h f (trailP V f x 0 hu (by change ‖(0:ℝ)‖ ≤ _; simp) (fun i=>by rw [smul_zero,add_zero]; unfold f; split_ifs;exact he;exact hv))
    have h : 4≤q:=hp.1
    have he:= Pass.unison h' (by linarith only [h]) (b:=E Y) (fun i hi=> congr_arg E (show f i= Y from if_neg hi)); change E (f tip)=_ at he; rw [show f tip=X from if_pos rfl] at he; exact he
def Weft (T:Team (stageP A.B.a (m+1) n)): Type:= ℝ × Nilot T
private abbrev unwrap (x:Weft T): ℝ × Nilot T:= x
private abbrev tie (x:ℝ × Nilot T):Weft T:=x
instance: SeminormedAddCommGroup (Weft T):=inferInstanceAs (SeminormedAddCommGroup (ℝ × Nilot T))
instance: NormedSpace ℝ (Weft T):=by exact (show NormedSpace ℝ (ℝ × Nilot T) from Prod.normedSpace)
def eT (T:Team (stageP A.B.a (m+1) n)):Weft T→L[ℝ] ℝ × Guild T:=Guild.groupB T
omit H V h hp in
private lemma hT : Isometry (eT T) ∧ DenseRange (eT T):= by exact (Guild.grouped T)
omit H V h hp in
private lemma proot (x:ℝ × Nilot T){y: ℝ × Nilot T}{w:sun}(B:Beam (ℝ × Guild T))(hp: (Guild.groupB T) y=Guild.groupB T x+ Beam.read _ w B): ‖tie y-tie x‖ ≤ ‖B‖:=by
   rw [←dist_eq_norm,← (hT (T:=T)|>.1).dist_eq,dist_eq_norm]; change ‖Guild.groupB T y-Guild.groupB T x‖ ≤ _
   rw [hp,add_sub_cancel_left]; exact Beam.price B w
omit H V hp h in
private lemma norms_2 {T:Team (stageP A.B.a (m+1) n)} (x y: ℝ × Nilot T):‖tie x- tie y‖= max ‖x.1-y.1‖ ‖x.2-y.2‖:=by rfl
omit H V h hp in
private lemma Ba {hx wx:Nilot T}{u:sun}(hv:‖hx‖ ≤ 1/4)(ht: ‖wx‖≤1/4): ‖hx+u.val • wx‖≤1:= calc
   _ ≤ ‖hx‖+ ‖u.val • wx‖:= norm_add_le ..
   _ ≤ _:=by rw [show ‖u.val •wx‖= ‖u.val‖*‖wx‖ from norm_smul u.val (wx.val.val: Show (stageP A.B.a (m+1) n))]; exact (add_le_add hv ((mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr u.2)).trans ht)).trans (by norm_num)
private lemma theme (hx:mild Ω x.1)(hv:‖x.2‖≤1/8):∃ P':FullVolume.Amp.Pulse (ℝ × Guild T) Y (2*c),Hits (f:=fun y:Weft T=> E (glades H (unwrap y))) (eT T) (tie x) P':=by
    apply exitP (eT T) (tie x) hp hT.1 hT.2 le_rfl; refine ⟨by norm_num,?_⟩
    filter_upwards [Metric.closedBall_mem_nhds (tie x) (show (0:ℝ)<1/8 by norm_num)] with z hy; intro v hw; rw [Metric.mem_closedBall, dist_eq_norm] at hy; let y:=unwrap z; let w:=unwrap v
    have hh : max |y.1-x.1| ‖y.2-x.2‖ ≤ 1/8:= (norms_2 y x).symm.trans_le hy
    have he : max |w.1| ‖w.2‖≤1/4:=hw
    have Hx:=Pass.samples V hx (((le_max_left ..).trans hh).trans (by norm_num)); have ht:‖w.1‖≤ 1/4:=(le_max_left ..).trans he
    have hQ : ‖y.2‖≤1/4:= by
        have h:‖y.2-x.2‖≤1/8:=(le_max_right ..).trans hh; linarith [norm_sub_norm_le y.2 x.2]
    let f(t:sun):= glades H (y+t.val • w); refine Muse.roundTrip (fun t:ℝ=> E (glades H (unwrap (z+t • v)))) (h f (trailP V f y w Hx (ht.trans (by norm_num)) (fun i=>?_))) hp.1
    exact gleans H _ (Pass.band_full _ V Hx (ht.trans (by norm_num)) i) (Ba hQ ((le_max_right ..).trans he))
lemma anima (f:sun→ Ticket A N m n)(g:sun→ℝ × Nilot T)(hf:∀ t:sun,mild Ω (g t).1)(hv: ‖(g tip).2‖≤1/8)(he:∀ t:sun, ReadsF (f t) (g t))(B:Beam (ℝ × Guild T))(hB:‖B‖≤1/4) (hP:∀ t:sun,Guild.groupB T (g t)=Guild.groupB T (g tip)+Beam.read _ t B):∃ T_:Beam Y, ‖T_‖≤4*c∧∀ s:sun, E (f s)= Beam.read _ s T_:=by
   let x:ℝ × Nilot T:=g tip; let Vt:=Guild.groupB T
   obtain ⟨p,hp'⟩:= theme H V hp E h (hf tip) hv
   let W:= E (glades H x); let y:=bead p B; refine ⟨Beam.arm W+y,?_ ,fun s:sun=> ?_⟩
   · have hs:=Pass.samples V (hf tip) (show |x.1-(g tip).1|≤2 by unfold x;simp); have ht:= (he tip).norm; have ht':= Pass.simple_full _ V hs
     have hu: ‖W‖≤c:= Pass.solo (h (fun _=>glades H x) (trailP V _ x 0 hs (by change |(0:ℝ)| ≤ 1;simp) (fun i=>by rw [smul_zero,add_zero]; exact gleans H x ht' ht))) tip
     have hc:0≤c:= (norm_nonneg _).trans hu
     apply (norm_add_le ..).trans; rw [Beam.armN]; exact (add_le_add hu (p.liftN B hB)).trans (by linarith)
   have hz:‖tie (g s)-tie (g tip)‖≤1/4:= (proot x B (hP s)).trans hB
   rw [sprung H V hp E h (f s) (he s) (Pass.samples V (hf s) (by simp)),map_add,Beam.armL, show Beam.read Y s y=_ from p.liftL _ hB _]; have hk:Vt (g s)-Vt x= Beam.read _ s B := by unfold Vt x; rw [hP]; abel
   rw [← hk]; change _= _+sees p ((Guild.groupB T) (g s)-(Guild.groupB T) x);rw [show sees p ((Guild.groupB T) (g s)-(Guild.groupB T) x)= E (glades H (g s))-E (glades H x) from hp'.jingle (y:=tie (g s)) hz]; unfold W; abel
end often
end YM.PhysicalNext.Repeat.Muse.Veil
