import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Jets
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Card
import YM.Progress.STATIONARY_SCENES.Spend

/-!
# Affine kinetic VALUE minus match. Linear vanishes for the ACTUAL cut integral combined cost.
 Use coordinate loop mirror; no claim thermal alone, full R0 still has flags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Token
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare  Exterior
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (B : BudgetPoint) (β : ℝ)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:Xs=> represent (tint G _ x))
local notation "R₀" => Pane.virgin T B β
abbrev shift (s : Signed) (b : Site c) (G : Gauge) : Positions (Uniform.Primary c G)→L[ℝ] Positions (Uniform.Primary c G):= (tint G _).symm.toContinuousLinearMap ∘L (AnalyticNext.QuarticMatch.Joint.shifts s b) ∘L (tint G _).toContinuousLinearMap
lemma slip (s : Signed) (b : Site c) (x:Xs) : V (shift s b G x)=pull s b (V x) := AnalyticNext.QuarticMatch.Joint.rep_shifts ..
section go
open AnalyticNext.QuarticMatch.Joint
lemma loopChannel (s:Signed) (b:Site c) (R:PathData G) (U:Config G c): Precision.loop R (pull s b U)=Precision.loop R U:= by
  unfold Precision.loop Patch.average; apply congr_arg; conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  refine Finset.sum_congr rfl fun i _=> ?_; dsimp only; rw [pull_pull,translate_by, uncut_translate]; rfl
lemma secondChannel (s:Signed) (b:Site c) (R:PathData G) (p:Clip) (U:Config G c): secondTerm p R (pull s b U)=secondTerm p R U:= by
  unfold secondTerm Patch.average; apply congr_arg; conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  refine Finset.sum_congr rfl fun i _=> ?_; dsimp only; rw [pull_pull,translate_by, quadratic_translate]; rfl
lemma sparked (s:Signed) (b:Site f) (U:Config G f) : (R₀).eval (pull s b U)=(R₀).eval U:= by
  have hx : flags B.threshold (pull s b U)=∅ ↔ flags B.threshold U=∅:= by
    nth_rw 2 [← Work.H03.flags_send s b]; rw [Finset.image_eq_empty]
  rw [Pane.sparkling,Pane.sparkling]
  simp only [hx]; rw [loopChannel,main_pull]
lemma pushSpin (s:Signed) (b:Site c) (U: Config G c) (he : S.patch.Branches S.kernel G): S.push β (R₀).eval (pull s b U) = S.push β (R₀).eval U:= by
  let t:= S.ratio.embed b
  have hs : MeasurePreserving (pull s t (K:=G.El)) (prior G _) (prior G _):= prior_pull ..
  have hn : Injective (pull s t (K:=G.El)):= by
    apply HasLeftInverse.injective; refine ⟨pull s⁻¹ (-s⁻¹.act t),fun i=>?_⟩; rw [pull_pull, mul_inv_cancel,affine, Signed.act_neg,s.act_inv,neg_add_cancel,pull_id]
  unfold StepData.push; rw [← hs.integral_comp (continuous_pull s t|>.isClosedEmbedding hn|>.measurableEmbedding)]
  unfold t; simp_rw [sparked, S.channel he]
end go
variable (α : ℝ)
-- exact per F V arbitrary. Use when all weights evaluate on V*
def arrayE (Vp:Config G c) := Real.log (S.push β (R₀).eval Vp)+β* mainTerm T.low T.down Vp+
    (α* secondTerm T.low T.down Vp+ Precision.loop T.down Vp) -- signs
abbrev harmony (x:Xs) := arrayE T B β α (V x)
lemma hymn (s:Signed) (b:Site c) (U:Config G c) (h:S.patch.Branches S.kernel G) : arrayE T B β α (pull s b U)=arrayE T B β α U := by
  unfold arrayE; rw [pushSpin T B β s b U h,loopChannel,secondChannel,AnalyticNext.QuarticMatch.Joint.main_pull]
lemma lines (x:Xs) : harmony T B β α x=pures T B β x+ β* mainTerm T.low T.down (V x)+draft α T.down T.low (tint G _ x):= rfl

section first
open AnalyticNext.QuarticMatch

def inverseS : Signed := ⟨Equiv.refl _,fun _=>true⟩
lemma polarity (i: Uniform.Primary c G) : ∃ y : Site c, let s := inverseS; shift s y G (bolt i) = -bolt i := by
  obtain ⟨⟨b,k⟩,r⟩:=i; obtain ⟨k,rfl⟩:= Exterior.axisEquiv.surjective k
  let s:=inverseS; let i : Uniform.Primary c G:=((b,coord k),r)
  let v:= b+step k - s.act b
  refine ⟨v,?_⟩; change shift s v G (bolt i)=_
  ext1 ⟨⟨x,j⟩,t⟩; obtain ⟨j,rfl⟩:= axisEquiv.surjective j; let q:= sendEdge s v (x,j)
  change Joint.shifts s v (tint G _ (bolt i)) (x,coord j) t = -bolt i ((x,coord j),t)
  have hk : axisEquiv.symm (coord j)=j := axisEquiv.symm_apply_apply j
  unfold Joint.shifts; rw [ContinuousLinearMap.pi_apply,hk]
  rw [if_pos (show ((posDir j).rotate s).neg=true from rfl)]; change -bolt i (Work.E03.poleEquiv c q,t)=_
  have hx : sendEdge s v (b,k)=(b,k):= by
    unfold sendEdge; change (Step.used _ (s.act b+v))=(b,k); rw [show s.act b+v=b+step k from (by unfold v; abel)]
    simp [Step.used,Step.rotate,s,inverseS,posDir]
  by_cases ht:x=b ∧ j=k
  · have he : q=(b,k):=congr_arg (sendEdge s v) (Prod.ext ht.1 ht.2)|>.trans hx; rw [ht.1,ht.2] -- he let binder dependent?
    exact congr_arg (fun w : Bond c => -bolt i (Work.E03.poleEquiv c w,t)) he
  have hq : q ≠ (b,k):= fun he=> ht (Prod.mk.inj ((sendEdge_injective s v) (he.trans hx.symm)))
  have h₁ :(Work.E03.poleEquiv c q,t)≠i:=fun he=>hq ((Work.E03.poleEquiv c).injective (congr_arg Prod.fst he))
  have h₂ :((x,coord j),t) ≠ i:=fun he=>ht (Prod.mk.inj ((Work.E03.poleEquiv c).injective (show Work.E03.poleEquiv c (x,j)=Work.E03.poleEquiv c (b,k) from congr_arg Prod.fst he)))
  simp [bolt,h₁,h₂]
lemma crest {f : Xs→ℝ} (h:∀ s b, f ∘ shift s b G=f) (he : DifferentiableAt ℝ f 0): fderiv ℝ f 0=0 := by
  let A:= fderiv ℝ f 0
  have hk (i:Uniform.Primary c G): A (bolt i)=0:= by
    obtain ⟨b,hz⟩:= polarity i
    let L:= shift inverseS b G
    have hw := congr_arg (fun f : Xs→ℝ=> fderiv ℝ f 0) (h inverseS b)
    change fderiv ℝ (f ∘ L) 0=fderiv ℝ f 0 at hw; rw [fderiv_comp _ (by rwa [map_zero]) L.differentiableAt,map_zero,L.fderiv] at hw
    have hK : A (L (bolt i))=A (bolt i):= DFunLike.congr_fun hw (bolt i)
    rw [(show L (bolt i)=_ from hz),map_neg] at hK; linarith only [hK]
  ext1 x; rw [← Uniform.combine x,map_sum]; change ∑ i,A _=_; simp_rw [map_smul,hk,smul_zero,sum_const_zero]; rfl
lemma chant (he:S.patch.Branches S.kernel G) (hp : DifferentiableAt ℝ (harmony T B β α) 0) : fderiv ℝ (harmony T B β α) 0=0:= crest (fun s b=> funext fun x=> by change arrayE _ _ _ _ (V (shift s b G x))=_; rw [slip]; exact hymn T B β α s b (V x) he) hp
end first
end YM.PhysicalNext.Repeat.Token
