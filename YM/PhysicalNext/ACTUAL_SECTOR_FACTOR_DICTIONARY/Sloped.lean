import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Desk
import YM.Next.FREE_KERNELS.Lifts
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Author


/-!
Measurable dictionary values even **off** Clearing. The only branch
jet we need to patch in the energy kernel is the noise fderiv in
Rows.move/bump (incl in bias). This spot matters because the standard
measurability lemmas about parameterized fderiv have strong continuity
hypotheses on *full* function domain and here even StepData prediction
may have fallback boundaries. Instead extend the directional jet by
forward difference quotients with a fixed limit rule. This introduces no
new tag or stencil accesses. Will equal true blockJet when (and only need
when) that row is selected at the V and production heights where
`Authorized` receipt is bought (not: a version of the kernel equally
licensed off the mask or smooth across switches). For plaquetteJet agree
everywhere. This is not a pricing assertion on the extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Curve

def dt (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
private lemma pin : Tendsto dt atTop (𝓝[≠] (0:ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R:=ℝ))),
    Eventually.of_forall fun i => Set.mem_compl_singleton_iff.mpr (by unfold dt; positivity)⟩

variable {E H : Type} {Y : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]

def quote (P : E → H) (b : E) :=
  limUnder atTop fun n : ℕ => (dt n)⁻¹ • (P (dt n • b)-P 0)

theorem attends {P : E → H} (h : DifferentiableAt ℝ P 0) (b : E) :
    quote P b=fderiv ℝ P 0 b := by
  have hf := (YM.Push.side P h b).tendsto_slope_zero.comp pin
  apply Filter.Tendsto.limUnder_eq
  simpa only [Function.comp_apply, zero_add, zero_smul] using! hf

theorem motionless {P : E → H} : quote P 0=0 := by
  simp only [quote,smul_zero,sub_self]
  exact Filter.Tendsto.limUnder_eq tendsto_const_nhds

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [CompleteSpace H]

theorem stamped {P : Y → E → H} {b : Y → E} (h : Measurable (uncurry P)) (hl : Measurable b) :
    Measurable (fun y => quote (P y) (b y)) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n; apply Measurable.stronglyMeasurable
  have he (a : Y→E) (hx : Measurable a) : Measurable (fun y => P y (a y)) :=
    h.comp (measurable_id.prodMk hx)
  exact measurable_const.smul ((he _ (measurable_const.smul hl)).sub (he _ measurable_const))
end Curve

variable {c f n : Side} {G : Gauge} {S : StepData c f} {x : ℝ}
    {V V' : Config G c} {k k' : S.Choices}
namespace FieldJet

private lemma coat (s : Signed) :
    Measurable (fun p : Config G c × Directions G f => facade S s p.1 p.2) := by
  refine (continuous_pull s 0).measurable.comp ?_
  change Measurable (fun p : Config G c × Directions G f => increment (replica S.ratio p.1) p.2)
  unfold increment replica
  refine measurable_pi_lambda _ fun i => ?_
  split <;> apply Continuous.measurable <;> fun_prop

set_option maxHeartbeats 300000 in
theorem facePrice (s : Signed) (i : Cell f) :
    Measurable (fun p : Config G c × Directions G f => plaquetteJet S p.1 s i p.2) := by
  let P := fun (V : Config G c) (b : Directions G f) => G.curvature (faceValue (facade S s V b) i)
  have hf (V : Config G c) : DifferentiableAt ℝ (P V) 0 := ((Motion.plaquette_turn s V i (S:=S)
    (LocalJet.face_smooth ..).contDiffAt).1).differentiableAt (by simp)
  simp_rw [show ∀ (p : Config G c) (b : Directions G f), plaquetteJet S p s i b=Curve.quote (P p) b
    from fun p b => (Curve.attends (hf p) b).symm]
  apply Curve.stamped (b:=Prod.snd) _ measurable_snd
  have ht : Measurable (uncurry P) := by
    have hw := continuous_travel (G:=G) (square i.2.val.1 i.2.val.2) i.1
    exact G.continuous_curvature.measurable.comp (hw.measurable.comp (coat (G:=G) (S:=S) s))
  exact ht.comp (f:=fun (y : (Config G c × Directions G f) × Directions G f) => (y.1.1,y.2)) ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

def trial (V : Config G c) (k : S.Choices) (s : Signed) (i : Bond c) (b : Directions G f) :=
    Curve.quote (fun a => G.curvature (predictorTurn V k s i a)) b

theorem trial_meas (k : S.Choices) (s : Signed) (i : Bond c) (h : S.patch.Branches S.kernel G) :
    Measurable (fun p : Config G c × Directions G f => trial p.1 k s i p.2) := by
  unfold trial
  have he : Measurable (fun p : Config G c × Directions G f => predictGroup p.1 k s i p.2) :=
    (measurable_pi_apply i).comp ((S.prediction_meas h (choice s k)).comp (coat s))
  apply Curve.stamped (b:=Prod.snd) _ measurable_snd
  let L (p : (Config G c × Directions G f) × Directions G f) : Config G c × Directions G f := (p.1.1,p.2)
  let T (p : (Config G c × Directions G f) × Directions G f) : Config G c × Directions G f := (p.1.1,0)
  exact G.continuous_curvature.measurable.comp ((he.comp (f:=L) (by unfold L; fun_prop)).mul
    (he.comp (f:=T) (by unfold T; fun_prop)).inv)

lemma stands {A : Stores S} {F : Tree.Forest S.ratio} {B : ℝ} (h : Authorized A V F x B)
    (k : S.Choices) (s : Signed) (i : Bond c) (he : curb (shots S x) A F x s (.inr i)) (b : Directions G f) :
    trial V k s i b=blockJet V k s i b := by
  apply Curve.attends
  exact ((Motion.block_turn s V i k (h.noise s k i he).2.1).1).differentiableAt (by simp)

lemma changes (i : Bond c) (s : Signed) (h : S.patch.Branches S.kernel G)
    (hr : AgreeNear id (s.act i.1) (predReach S.patch+3) V V')
    (hl : TagNe S (s.act i.1) (predReach S.patch+3) k k')
    (a b : Directions G f) (hz : echo S (s.act i.1) (predReach S.patch+1) a b) :
    trial V k s i a = trial V' k' s i b := by
  have he (t : ℝ) : predictGroup V k s i (t • a) = predictGroup V' k' s i (t • b) := by
    rw [noise_dep V k s i (t • a) (t • b) h (fun e hi => congr_arg (fun x : G.Color => t • x)
      (hz e (by omega)))]
    unfold predictGroup
    have hy := orient_view (S:=S) V V' i.1 (predReach S.patch) s (anchored hr (by omega)) (t • b)
    have hf := prediction_near_eq h _ _ (choice s k) i hy
    rw [hf]
    refine same_tags (choice s k) i (choice s k') _ ?_
    apply TagNe.pull s i.1 1
    apply TagNe.close _ _ k k' hl
    rw [separation_self]; omega
  have ht : predictGroup V k s i 0 = predictGroup V' k' s i 0 := by simpa using he (0:ℝ)
  unfold trial Curve.quote predictorTurn
  simp_rw [he,ht]

/-- Stable surrogate even on unselected noise rows. -/
def bump' (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (a : Directions G f) : LogArray G (Slots S) := fun i => i.2.elim (fun j => faceKick T x V a i.1 j)
      (fun j => -(Real.sqrt S.kernel.penalty • trial V k i.1 j a))

lemma bump'_zero (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) : bump' T x V k 0=0 := by
  funext i
  obtain ⟨s,i|i⟩ := i
  · simp only [bump',Sum.elim_inl, Pi.zero_apply]; simp [faceKick,barrel]
  simp [bump',trial,Curve.motionless]

lemma agrees (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    {A : Stores S} {F : Forest S.ratio} {B : ℝ} (H : Authorized A V F x B) (a : Directions G f)
    (i : Slots S) (h : keep x (shots S x) A F i) : bump' T x V k a i = Rows.bump T x V k a i := by
  rcases i with ⟨s,i|i⟩
  · rfl
  simp only [bump',Sum.elim_inr,bump,noiseKick,stands H k s i (show curb _ _ _ _ _ _ from h)]

theorem around (T : Tube G S) (x : ℝ) (a b : Directions G f) (i : Slots S)
    (hl : Map.Aperture S T x)
    (h : AgreeNear id (spot S i) (4*radiusB x) V V') (he : TagNe S (spot S i) (4*radiusB x) k k')
    (hz : ∀ j, separation (spot S i) (portOf S j) ≤ radiusB x → a j=b j) :
    bump' T x V k a i = bump' T x V' k' b i := by
  rcases i with ⟨s,i|i⟩
  · exact bump_with T x k k' V V' hl _ _ _ h he hz
  have hp := hl.spans
  unfold Next.SectorChange.span at hp
  change -(Real.sqrt S.kernel.penalty • _) = -(Real.sqrt S.kernel.penalty • _)
  rw [changes i s hl.branched (anchored h (by omega)) (TagNe.close _ _ k k' he (by
    change separation (s.act i.1) (s.act i.1)+_ ≤ _; rw [separation_self]; omega)) _ b (fun j hj => hz j (by change separation (s.act i.1) (portOf S j) ≤ _; unfold portOf; omega))]

lemma adjoint_continuous : Continuous (fun z : G.El × G.Color => G.adjoint z.1 z.2) := by
  let F := G.colorMat.toContinuousLinearMap
  change Continuous (fun z : G.El × G.Color => G.projectColor (G.conjugate z.1 (G.colorMat z.2)))
  apply G.projectColor.toContinuousLinearMap.continuous.comp (f:=fun z : G.El × G.Color => G.conjugate z.1 (G.colorMat z.2))
  unfold Gauge.conjugate
  exact ((G.continuous_mat.comp continuous_fst).mul (F.continuous.comp continuous_snd)).mul ((continuous_star.comp G.continuous_mat).comp continuous_fst)

lemma transport_mask {X : Type*} [MeasurableSpace X] (c : ℝ) (u : X → G.El) (y : X → G.Color)
    (h : Measurable u) (he : Measurable y) : Measurable (fun x => c • (G.adjoint (u x)) (y x)) := by
  have hf : Measurable (fun x => (G.adjoint (u x)) (y x)) := by
    let f : X → G.El × G.Color := fun x => (u x,y x)
    have hm : Measurable f := h.prodMk he
    have hh : Measurable (fun z : G.El × G.Color => G.adjoint z.1 z.2) := (adjoint_continuous (G:=G)).measurable
    exact hh.comp (f:=f) hm
  exact (measurable_const (a:=c)).smul hf

set_option maxHeartbeats 400000 in
theorem bump'_meas (T : Tube G S) (x : ℝ) (h : S.patch.Branches S.kernel G) (k : S.Choices) (i : Slots S) :
    Measurable (fun p : Config G c × Directions G f => bump' T x p.1 k p.2 i) := by
  obtain ⟨s,j|j⟩ := i
  · change Measurable (fun p : Config G c × Directions G f => faceKick T x p.1 p.2 s j)
    unfold faceKick
    split
    · unfold barrel
      refine Measurable.tsum fun n => ?_
      dsimp only
      split
      next hl =>
        let i := (T.up.row j.1.2 n).2
        have hB : Measurable (fun p : Config G c × Directions G f => travel (facade S s p.1 (0:Directions G f)) j.1.1 i.walk) :=
          (continuous_travel (G:=G) i.walk j.1.1).measurable.comp ((coat (G:=G) (S:=S) s).comp (f:=fun p : Config G c × Directions G f => (p.1, (0:Directions G f))) (measurable_fst.prodMk measurable_const))
        have hF := facePrice (S:=S) (G:=G) s (Work.F03.slotFace i j.1.1)
        exact transport_mask _ _ _ hB hF
      exact measurable_const
    exact (measurable_const (a:=Real.sqrt T.high.direct)).smul (facePrice (S:=S) (G:=G) s j.1)
  exact ((measurable_const (a:=Real.sqrt S.kernel.penalty)).smul (trial_meas k s j h)).neg

end FieldJet
end YM.PhysicalNext.Dictionary
