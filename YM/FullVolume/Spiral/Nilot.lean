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
section stage
variable {c:Side}{Q:Price G c}
def Nilot (K:Team Q) : Submodule ℝ (Home K) where
  carrier:={x|HasSlots Q.p (observe K x)}
  zero_mem':= ⟨rfl,rfl,fun _=> rfl,fun _=> rfl⟩
  add_mem' {x} {y} (h:HasSlots _ _) (h': HasSlots _ _) := by
    refine ⟨rfl,rfl,fun i=>?_,fun i=>?_⟩
    · change (observe K x|>.E _) + (observe K y|>.E _) = _
      rw [h.regular,h'.regular,add_zero]
    change (observe K x|>.K _) + (observe K y|>.K _) = _; rw [h.forced_zero,h'.forced_zero,add_zero]
  smul_mem' a x (h:HasSlots _ _):= by
    refine ⟨rfl,rfl,fun i=>?_,fun i=>?_⟩
    · change a • (observe K x|>.E _) = _; rw [h.regular,smul_zero]
    change a • (observe K x|>.K _) = _; rw [h.forced_zero,smul_zero]
variable (K:Team Q)
def Guild : Type:= Completion (Nilot K)
namespace Guild
instance: NormedAddCommGroup (Guild K):=inferInstanceAs (NormedAddCommGroup (Completion (Nilot K)))
instance: NormedSpace ℝ (Guild K):= by exact (_root_.UniformSpace.Completion.instNormedSpace ℝ (↥(Nilot K)))
instance: CompleteSpace (Guild K):=inferInstanceAs (CompleteSpace (Completion (Nilot K)))
abbrev act (x: Completion (Nilot K)): Guild K:=x
def extend : Guild K →L[ℝ] World K:=
   show Completion (Nilot K) →L[ℝ] Completion (Home K) from ((Completion.toComplL (𝕜:=ℝ) (E:=Home K)).comp (Nilot K).subtypeL).extend (Completion.toComplL (𝕜:=ℝ) (E:=Nilot K))
lemma wordy (x:Nilot K): extend K (act K (x:Completion (Nilot K)))= World.ready (x.val: Completion (Home K)):=by
   let e:= Completion.toComplL (𝕜:=ℝ) (E:=Nilot K); have hd:DenseRange e:= Completion.denseRange_coe (α:= Nilot K); have he:Isometry e:=Completion.coe_isometry; exact ContinuousLinearMap.extend_eq ((Completion.toComplL (𝕜:=ℝ) (E:=Home K)).comp (Nilot K).subtypeL) hd he.isUniformInducing x
lemma isos : Isometry (extend K):= by
   let X:= Completion (Nilot K); let e:=Completion.toComplL (𝕜:=ℝ) (E:=Nilot K); have he: DenseRange e:= Completion.denseRange_coe; let f:X→L[ℝ] World K:= extend K
   suffices hz:∀ x:X, ‖f x‖ =‖x‖ from AddMonoidHomClass.isometry_of_norm (extend K) hz
   apply isClosed_property he (isClosed_eq f.continuous.norm continuous_norm); intro x; unfold f; change ‖extend K (act K (x:Completion (Nilot K)))‖=‖(x:Completion (Nilot K))‖; rw [wordy]; exact (Completion.norm_coe x.val).trans (Completion.norm_coe x).symm
abbrev canonical (x:Nilot K): Guild K:= act K (x:Completion (Nilot K))
def groupB : (ℝ × Nilot K)→L[ℝ](ℝ × Guild K):= by
    exact ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) (Completion.toComplL (𝕜:=ℝ) (E:=Nilot K))
lemma grouped: Isometry (groupB K)∧ DenseRange (groupB K):= by
  constructor
  · exact Isometry.prodMap (show Isometry (@id ℝ) from isometry_id) (Completion.coe_isometry (α:= Nilot K))
  exact DenseRange.prodMap denseRange_id (show DenseRange ((↑): Nilot K → Completion (Nilot K)) from Completion.denseRange_coe)
end Guild
end stage
open Contest
variable (Φ: Plato L q v d t') (O:Ops L N n) (F:sun→ Contest N n L)(hF:∀ s, (F s).bonusB=ask A.B.a s)
local notation "Q"=> A.B.a
local notation "θ!"=> Φ
local notation "H0"=> Fin (N+1)
variable (i:Fin (N+1))
local notation "K"=> O.plan i (headB i)
variable (hx:∀ s,HasSlots (stageP A.B.a i n).p (observe (O.plan i (headB i)) ((F s).chair Φ O i)))
abbrev hues (s:sun): Nilot (O.plan i (headB i)):= ⟨(F s).chair Φ O i,hx s⟩
def pose (s:sun):ℝ × Nilot (O.plan i.val (headB i)):= ((F s).pitch i,hues Φ O F i hx s)
local notation "U"=> Guild.groupB K
local notation "A_"=> fun s:sun=> pose Φ O F i hx s
-- true aperture Parameter Stage.Actor before horizontal.X Risk. Glyph.In.Id observes valid. ∆ size ℓ max. Real.Sector opacity.
include Φ F O hx hF
set_option maxHeartbeats 560000 in
lemma hearth : ∃ B:Beam (ℝ × Guild K), ‖B‖≤ 1/4 ∧ ∀ s:sun,U (A_ s)= U (A_ Jams.tip)+ Beam.read _ s B:=by
    let p:= F Jams.tip; have he : p.bonusB=A.B.a.clock.bar:=by unfold p; rw [hF]; unfold ask; change _+0*_=_; ring
    obtain ⟨B,hB,h'⟩:= Contest.score Φ O p he
    let V:= O.plan i (headB i); let S:=Guild.extend V; have hQ (s:sun): (F s).pitch i = p.pitch i+Beam.read _ s (B.1 i) ∧ S (Guild.canonical V (hues Φ O F i hx s)) = S (Guild.canonical V (hues Φ O F i hx tip))+Beam.read _ s (B.2 i):= by
       unfold S Guild.canonical; rw [Guild.wordy V, Guild.wordy V]; exact h' s (F s) (hF s) i
    let Z:Beam (World K):=B.2 i
    obtain ⟨T,hT,h⟩:= Beam.slate Z S (Guild.isos V) (fun s=> ⟨(Guild.canonical V (hues Φ O F i hx s))-(Guild.canonical V (hues Φ O F i hx tip)), (map_sub S _ _).trans (by rw [(hQ s).2]; change _ = Beam.read (World K) s Z; unfold Z; abel)⟩)
    refine ⟨Beam.lay (B.1 i) T,(Beam.layN ..).trans ?_,fun s=>?_⟩
    · rw [hT]; exact (add_le_add (Rally.perN hB i|>.1) (Rally.perN hB i|>.2)).trans (by norm_num [lux])
    rw [Beam.layL]; refine Prod.ext (hQ s).1 ((Guild.isos V).injective ?_); change S _= S (_ +Beam.read _ s T); rw [map_add,h]; exact (hQ s).2
end YM.PhysicalNext.Repeat.Muse.Veil
