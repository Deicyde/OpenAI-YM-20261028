import YM.FullVolume.Spiral.Chrome
import YM.FullVolume.Gain.Resolve
import YM.FullVolume.Amp.Ledge
/- analytic Chart controls spin in Slots FULL ancestor.E leaving R.C normalization ∆. -/
set_option autoImplicit false
set_option maxHeartbeats 690000
set_option synthInstance.maxHeartbeats 160000
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
open Contest
open FullVolume Paint Paint.Tower Amp.Beam Contest
lemma truncateD (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X](B:Beam X)(a:ℝ)(ha:a∈sun): ∃ C:Beam X, ‖C‖≤‖B‖∧ ∀ s:sun, read _ (slash a ha s) B= read _ s C:= by
   have h: PaidBeam (fun s:sun=> read _ s B) ‖B‖:= ⟨B,le_rfl,fun _=>rfl⟩; exact (Muse.slashes ha h).arrives
variable (Φ: Plato L q v d t') (O:Ops L N n) (F:sun→ Contest N n L)
variable {a:ℝ}(ha:a∈sun)(hF:∀ s, (F s).bonusB=ask A.B.a (slash a ha s).val)
local notation "θ!"=> Φ
local notation "H0"=> Fin (N+1)
variable (i:Fin (N+1))
local notation "K"=> O.plan i (headB i)
variable (hx:∀ s,HasSlots (stageP A.B.a i n).p (observe (O.plan i (headB i)) ((F s).chair Φ O i)))
local notation "U"=> Guild.groupB K
local notation "A_"=> fun s:sun=> pose Φ O F i hx s
include Φ F O hx hF
omit hx in
lemma jacket : ∃ P:Beam ℝ,∃ B:Beam (World K), ‖P‖≤ lux ∧ ‖B‖≤ lux ∧ ∀ s:sun,(F s).pitch i=(F tip).pitch i+ read _ s P ∧ realm Φ O (F s) i=realm Φ O (F tip) i + read _ s B:=by
    let p:= F Jams.tip; have he : p.bonusB=A.B.a.clock.bar:=by unfold p; rw [hF]; unfold ask; change _+(0*a)*_=_; ring
    obtain ⟨B,hB,h'⟩:= Contest.score Φ O p he
    obtain ⟨P,hP,h⟩:= truncateD _ (B.1 i) a ha; obtain ⟨Q,hQ,hR⟩:= truncateD _ (B.2 i) a ha; refine ⟨P,Q,hP.trans (Rally.perN hB i|>.1),hQ.trans (Rally.perN hB i|>.2),fun s=> ?_⟩; rw [←h,← hR]; exact h' (slash a ha s) (F s) (hF s) i
lemma gloaming : ∃ B:Beam (ℝ × Guild K), ‖B‖≤1/4∧ ∀ s:sun, U (A_ s)= U (A_ Jams.tip)+ read _ s B:=by
    obtain ⟨P,B,hP,hB,hY⟩:= jacket Φ O F ha hF i; let V:= O.plan i (headB i); let S:=Guild.extend V
    have hG(s): realm Φ O (F s) i=S (Guild.canonical V (hues Φ O F i hx s)):= (Guild.wordy V (hues Φ O F i hx s)).symm
    simp_rw [hG] at hY; obtain ⟨T,hT,h⟩:= Beam.slate B S (Guild.isos V) (fun s=> ⟨(Guild.canonical V (hues Φ O F i hx s))-(Guild.canonical V (hues Φ O F i hx tip)),(map_sub S _ _).trans (by rw [(hY s).2]; change _= read (World K) s B; abel)⟩)
    refine ⟨Beam.lay P T,(Beam.layN ..).trans ?_,fun s=>?_⟩
    · rw [hT]; exact (add_le_add hP hB).trans (by norm_num [lux])
    rw [Beam.layL]; refine Prod.ext (hY s).1 ((Guild.isos V).injective ?_); change S _= S (_ +Beam.read _ s T); rw [map_add,h]; exact (hY s).2
omit hx in
lemma terrace : ∃ B:Beam (World K), ‖B‖≤1∧∀ s:sun, realm Φ O (F s) i=read _ s B:=by
   obtain ⟨P,B,hP,hB,h⟩:=jacket Φ O F ha hF i; let C:= realm Φ O (F tip) i
   have hp:‖C‖ ≤ 1/8:= (Completion.norm_coe (chair Φ O _ i)).trans_le (Contest.sparkN Φ O (F tip) i)
   exact ⟨arm C+B,(norm_add_le ..).trans ((add_le_add ((armN C).trans_le hp) hB).trans (by norm_num [lux])),fun i=>by rw [map_add,armL]; exact h i|>.2⟩ -- shadow i
end YM.PhysicalNext.Repeat.Muse.Veil
