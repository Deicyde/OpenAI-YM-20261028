import YM.Push.SECTOR_MEASURE.Gauges
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Flat



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Affine D covariance and orientation rules

Read from actual group functions first, including transforming the
displacement into a pulled field's own canonical positive bonds at barV. No claimed equality with V-transport for a Q-tangent on reversal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Motion
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
  YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure YM.Push
open YM.Push.SectorMeasure.Oriented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f n : Side} {S : StepData c f}

def swing (w : Site n → G.El) : Directions G n →L[ℝ] Directions G n :=
  (LinearMap.pi (fun i : Bond n => (G.adjoint (w i.1)).comp (LinearMap.proj i))).toContinuousLinearMap

lemma swing_eval (w : Site n → G.El) (a : Directions G n) (i : Bond n) : swing w a i=G.adjoint (w i.1) (a i) := rfl
@[simp] lemma swing_size (w : Site n → G.El) (a : Directions G n) (i : Bond n) : ‖swing w a i‖=‖a i‖ := by rw [swing_eval,G.norm_adjoint]

lemma swing_increment (w : Site n → G.El) (U : Config G n) (a : Directions G n) :
    increment (Lattice.gauge w U) (swing w a) = Lattice.gauge w (increment U a) := by
  funext e
  unfold increment Lattice.gauge; rw [swing_eval, exp_adjoint]; group

def pTest (U : Config G f) (i : Cell f) (a : Directions G f) := G.curvature (faceValue (increment U a) i)
def out (U : Config G f) (k : S.Choices) (i : Bond c) (a : Directions G f) :=
  S.prediction (increment U a) k i * (S.prediction U k i)⁻¹
def bTest (U : Config G f) (k : S.Choices) (i : Bond c) (a : Directions G f) := G.curvature (out U k i a)

lemma p_swing (w : Site f → G.El) (U : Config G f) (i : Cell f) (a : Directions G f) :
    pTest (Lattice.gauge w U) i (swing w a) = G.adjoint (w i.1) (pTest U i a) := by
  rw [pTest,pTest,swing_increment]; unfold faceValue
  rw [travel_gauge,square_stop,G.curvature_conjugate] 

lemma b_swing (hp : S.patch.Branches S.kernel G) (w : Site f → G.El) (U : Config G f) (i : Bond c)
    (k : S.Choices) (a : Directions G f) :
    bTest (Lattice.gauge w U) k i (swing w a) = G.adjoint (w (S.ratio.embed i.1)) (bTest U k i a) := by
  rw [bTest,bTest,out,out,swing_increment,(choice_gauge hp _ k w).2,(choice_gauge hp U k w).2]; unfold Lattice.gauge
  rw [← G.curvature_conjugate]; dsimp only [Function.comp_apply]; congr 1; group


private lemma right_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F H' : E → G.Color}
    (L : E →L[ℝ] E) (w : G.El) (he : ∀ a, F (L a)=G.adjoint w (H' a)) (h : ContDiffAt ℝ ω F 0) :
    ContDiffAt ℝ ω H' 0 := by
  have ht : H' = fun a => ((G.adjoint w⁻¹).toContinuousLinearMap) (F (L a)) := by
    funext a; change _ = (G.adjoint w⁻¹) _
    rw [he,← G.adjoint_mul,inv_mul_cancel,G.adjoint_one]
  rw [ht]
  refine ((G.adjoint w⁻¹).toContinuousLinearMap.contDiff.contDiffAt).comp (f:=fun a => F (L a)) _
    (ContDiffAt.comp _ ?_ L.contDiff.contDiffAt)
  rw [map_zero]; exact h

private lemma right_covary {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F H : E → G.Color}
    (L : E →L[ℝ] E) (w : G.El) (he : ∀ a, F (L a)=G.adjoint w (H a)) (h : ContDiffAt ℝ ω F 0) :
    ∀ a, fderiv ℝ F 0 (L a)=G.adjoint w (fderiv ℝ H 0 a) := by
  intro a
  have hL := YM.Push.side F (h.differentiableAt (by simp)) (L a)
  let u := (G.adjoint w).toContinuousLinearMap
  simp_rw [← map_smul L,he] at hL
  exact hL.unique (u.hasFDerivAt.comp_hasDerivAt 0 (YM.Push.side H ((right_smooth L w he h).differentiableAt (by simp)) a))

lemma p_auth (w : Site f → G.El) (U : Config G f) (i : Cell f)
    (hs : ContDiffAt ℝ ω (pTest (Lattice.gauge w U) i) 0) :
    ContDiffAt ℝ ω (pTest U i) 0 ∧ ∀ a, fderiv ℝ (pTest (Lattice.gauge w U) i) 0 (swing w a) =
      G.adjoint (w i.1) (fderiv ℝ (pTest U i) 0 a) := by
  have hv := p_swing w U i
  exact ⟨right_smooth _ _ hv hs, right_covary _ _ hv hs⟩

lemma b_auth (hp : S.patch.Branches S.kernel G) (w : Site f → G.El) (U : Config G f) (i : Bond c) (k : S.Choices)
    (hs : ContDiffAt ℝ ω (bTest (Lattice.gauge w U) k i) 0) :
    ContDiffAt ℝ ω (bTest U k i) 0 ∧ ∀ a, fderiv ℝ (bTest (Lattice.gauge w U) k i) 0 (swing w a) =
      G.adjoint (w (S.ratio.embed i.1)) (fderiv ℝ (bTest U k i) 0 a) := by
  have hv := b_swing hp w U i k
  exact ⟨right_smooth _ _ hv hs,right_covary _ _ hv hs⟩

lemma canon_p (V : Config G c) (i : Cell f) :
    plaquetteJet S V 1 i = fderiv ℝ (pTest (replica S.ratio V) i) 0 := by
  unfold plaquetteJet facade pTest
  have ht {U : Config G f} : pull 1 0 U=U := by rw [pull_one]; ext e; simp [Lattice.translate]
  simp_rw [ht]

@[simp] lemma increment_zero (U : Config G f) : increment U 0=U := by
  funext i; simp only [increment,Pi.zero_apply,G.mat_lieExp_zero,one_mul]

lemma canon_b (V : Config G c) (k : S.Choices) (i : Bond c) (hp : S.patch.Branches S.kernel G) :
    blockJet V k 1 i = fderiv ℝ (bTest (replica S.ratio V) k i) 0 := by
  unfold blockJet bTest predictorTurn predictGroup out facade
  simp_rw [(carry 1 hp k _).2]
  have ht {U : Config G c} : pull 1 0 U=U := by rw [pull_one]; ext e; simp [Lattice.translate]
  simp_rw [increment_zero, ht]

lemma p_empty (S : StepData c f) (i : Cell f) (a : Directions G f) :
    fderiv ℝ (pTest 1 i) 0 a = Work.F03.faceCurl i (Flat.labels a) := by
  rw [← replica_one S.ratio, ← canon_p (S:=S)]
  rw [Flat.flat_curl,Flat.stationary_labels]
lemma b_empty (i : Bond c) (a : Directions G f) (k : S.Choices) (hp : S.patch.Branches S.kernel G) :
    fderiv ℝ (bTest 1 k i) 0 a = bills S (Flat.labels a) (pole i) := by
  rw [← replica_one S.ratio, ← canon_b (1:Config G c) _ _ hp, Flat.flat_probe 1 _ _ _ hp,Flat.stationary_labels]; rfl

def inChannel (s : Signed) (U : Config G f) : Directions G f →L[ℝ] Directions G f :=
  (LinearMap.pi (fun i => ((if s.flip i.2 then - G.adjoint ((U (sendEdge s 0 i))⁻¹) else LinearMap.id).comp
    (LinearMap.proj (sendEdge s 0 i))))).toContinuousLinearMap

lemma turn_read (s : Signed) (U : Config G f) (i : Bond f) : pull s 0 U i =
    if s.flip i.2 then (U (sendEdge s 0 i))⁻¹ else U (sendEdge s 0 i) := by
  unfold pull sendEdge Step.read Step.rotate posDir
  cases s.flip i.2 <;> rfl

lemma in_eval (s : Signed) (U : Config G f) (a : Directions G f) (i : Bond f) :
    inChannel s U a i = (if s.flip i.2 then - G.adjoint ((U (sendEdge s 0 i))⁻¹) else LinearMap.id) (a (sendEdge s 0 i)) := rfl

lemma in_size (s : Signed) (U : Config G f) (a : Directions G f) (i : Bond f) :
    ‖inChannel s U a i‖ = ‖a (sendEdge s 0 i)‖ := by rw [in_eval]; split <;> first | rfl | simp [G.norm_adjoint]

lemma mount (U : Config G f) (a : Directions G f) (s : Signed) :
    pull s 0 (increment U a)=increment (pull s 0 U) (inChannel s U a) := by
  funext i; rw [turn_read]; unfold increment; rw [in_eval,turn_read]; split
  · rw [LinearMap.neg_apply,exp_negative,exp_adjoint]; group
  rfl

lemma plaquette_turn (s : Signed) (V : Config G c) (i : Cell f)
    (h : ContDiffAt ℝ ω (pTest (pull s 0 (replica S.ratio V)) i) 0) :
    let F := fun y : Directions G f => G.curvature (faceValue (facade S s V y) i)
    ContDiffAt ℝ ω F 0 ∧ ∀ a, fderiv ℝ F 0 a = fderiv ℝ (pTest (pull s 0 (replica S.ratio V)) i) 0 (inChannel s (replica S.ratio V) a) := by
  intro F
  let L := inChannel s (replica S.ratio V)
  have he : F = pTest (pull s 0 (replica S.ratio V)) i ∘ L := funext fun a => by
    unfold Function.comp F pTest facade L; rw [mount]
  rw [he]
  constructor
  · apply ContDiffAt.comp _ _ L.contDiff.contDiffAt
    simpa using h
  intro a
  have hp : DifferentiableAt ℝ (pTest (pull s 0 (replica S.ratio V)) i) (L 0) := by simpa using h.differentiableAt (by simp)
  rw [fderiv_comp _ hp L.differentiableAt, map_zero,L.fderiv]; rfl

lemma block_turn (s : Signed) (V : Config G c) (i : Bond c) (k : S.Choices)
    (h : ContDiffAt ℝ ω (bTest (pull s 0 (replica S.ratio V)) (choice s k) i) 0) :
    let e := fun y : Directions G f => G.curvature (predictorTurn V k s i y)
    ContDiffAt ℝ ω e 0 ∧ ∀ a, fderiv ℝ e 0 a = fderiv ℝ (bTest (pull s 0 (replica S.ratio V)) (choice s k) i) 0 (inChannel s (replica S.ratio V) a) := by
  intro F
  let L := inChannel s (replica S.ratio V)
  let H := bTest (pull s 0 (replica S.ratio V)) (choice s k) i
  have he : F=H ∘ L := funext fun a => by
    unfold F H bTest out predictorTurn predictGroup facade L Function.comp
    rw [increment_zero,mount]
  change ContDiffAt _ _ H _ at h
  change _ ∧ ∀ a, _ = fderiv ℝ H 0 _
  rw [he]
  constructor
  · apply ContDiffAt.comp _ _ L.contDiff.contDiffAt; simpa using h
  intro a
  have hp : DifferentiableAt ℝ H (L 0) := by simpa using h.differentiableAt (by simp)
  rw [fderiv_comp _ hp L.differentiableAt,map_zero,L.fderiv]; rfl
end YM.Next.SectorChange.Motion
