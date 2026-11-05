import YM.Push.LOOP_COEFFICIENT.Completion
import YM.Push.LOOP_COEFFICIENT.Pinning

/-!
# Jacobian from actual free slice-chart coordinates plus gauge parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Lattice Wilson RG Precision Tree Matrix Function NormedSpace Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f}

abbrev Stem (G : Gauge) (F : Forest S.ratio) := Array G F.Free
abbrev Pack (F : Forest S.ratio) (G : Gauge) := (SiteKey G f ⊕ Key F G) → ℝ

def mounted (F : Forest S.ratio) (V : Config G c) (b : AxisChart G F) : Loops.Inputs G c f :=
  Sum.elim (lifting F V b) (fun _ => 1)

lemma mounted_pins (F : Forest S.ratio) (V : Config G c) (b : AxisChart G F) (x) : mounted F V b (fixedSlot F x)=1 := by
  unfold mounted fixedSlot; split
  · exact F.on_tree _ ⟨_,(F.trunk_mem_iff _).mpr ⟨x,‹_›,rfl⟩⟩
  rfl

lemma mounted_free (F : Forest S.ratio) (V : Config G c) (b : AxisChart G F) (x : F.Free) :
    mounted F V b (.inl x.val) = G.lieExp (b x) * replica S.ratio V x := F.off_tree _ x

abbrev inGauge {F : Forest S.ratio} (z : Pack F G) : Nodes G f := z ∘ Sum.inl
abbrev inField (F : Forest S.ratio) (z : Pack F G) : AxisChart G F := paint G F.Free (z ∘ Sum.inr)

def arrival {F : Forest S.ratio} (b : AxisChart G F) : Pack F G := Sum.elim 0 (fromColor G F.Free b)

def ride (F : Forest S.ratio) (V : Config G c) (z : Pack F G) :=
    gaugeJoint S (vary 1 (inGauge z)) 1 (mounted F V (inField F z))

def steering (F : Forest S.ratio) (V : Config G c) (b : AxisChart G F) (z : Pack F G) : Loops.Dual G c f :=
    displacement (mounted F V b) (ride F V z)

variable (F : Forest S.ratio) (V : Config G c) (b : AxisChart G F)

lemma steering_zero : steering F V b (arrival b) = 0 := by
  simp only [steering,ride,inField, show (arrival b ∘ Sum.inr)=(paint G F.Free).symm b from rfl,
    show inGauge (arrival b)=0 from rfl, LinearEquiv.apply_symm_apply,vary_zero,gaugeJoint_one,displacement_self]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma mounted_diff {V : E → Config G c} {y : E → AxisChart G F} {x : E}
    (hy : ContDiffAt ℝ ω y x) (hV : MatDiffAt V x) : MatDiffAt (fun t => mounted F (V t) (y t)) x := by
  rintro (i|i)
  · by_cases h : i ∈ F.trunks
    · have he t : mounted F (V t) (y t) (.inl i) = 1 := F.on_tree _ ⟨_,h⟩
      simp only [he]; exact contDiffAt_const
    let j : F.Free := ⟨i,h⟩
    simp only [show ∀ t, mounted F (V t) (y t) (.inl i) = _ from fun t => mounted_free F (V t) (y t) j, G.mat_mul]
    refine (G.exp_jet.contDiffAt.comp _ ((contDiff_apply ℝ _ j).contDiffAt.comp x hy)).mul ?_
    unfold replica; split
    · exact contDiffAt_const
    exact hV _
  exact contDiffAt_const

lemma ride_diff (x : Pack F G) : MatDiffAt (ride F V) x := gaugeJoint_diff
  (mounted_diff F ((fromColor G F.Free).symm.contDiff.contDiffAt.comp (f:=fun a => a ∘ Sum.inr) x (contDiffAt_pi.mpr fun _ => contDiffAt_apply ..)) (matDiffAt_const _))
  (matDiffAt_const _) ((matDiffAt_const _).vary (contDiffAt_pi.mpr fun _ => contDiffAt_apply ..))

lemma ride_arrive : ride F V (arrival b) = mounted F V b := by
  rw [ride, show inField F (arrival b)=b from (paint G F.Free).apply_symm_apply b,show inGauge (arrival b) = 0 from rfl,vary_zero,gaugeJoint_one]

lemma steering_diff : ContDiffAt ℝ ω (steering F V b) (arrival b) :=
  (matDiffAt_const _ ).displacement (ride_diff F V (arrival b)) (ride_arrive ..)

def steered := linearAt (steering F V b) (arrival b)

def thrown := linearAt (fun z : Stem G F => displacement (mounted F V b) (mounted F V (paint G F.Free z))) (fromColor G F.Free b)

lemma steered_eq : steered F V b = sides (R_tot S (mounted F V b)) (thrown F V b) := by
  ext i j
  cases j with
  | inl j =>
    let H := fun z : Nodes G f => Sum.elim z (fromColor G F.Free b)
    have hd : HasFDerivAt H (ContinuousLinearMap.pi (Sum.elim (fun i => ContinuousLinearMap.proj (R:=ℝ) i) (fun _ => 0))) 0 := by
        refine hasFDerivAt_pi.mpr ?_; rintro (i|i)
        · exact (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ => ℝ) i).hasFDerivAt
        exact hasFDerivAt_const ..
    have he : steering F V b ∘ H = fun v => displacement (mounted F V b) (gaugeJoint S (vary 1 v) 1 (mounted F V b)) := by
      ext1 v; dsimp only [steering,ride,Function.comp_apply]
      rw [show inField F (H v)=b from (paint G F.Free).apply_symm_apply _]; rfl
    have ht : DifferentiableAt ℝ (steering F V b) (H 0) := (steering_diff ..).differentiableAt (by simp)
    rw [steered, sides_left,← joint_generator, ← he, linearAt,linearAt,fderiv_comp 0 ht hd.differentiableAt,hd.fderiv]
    rw [LinearMap.toMatrix'_apply,LinearMap.toMatrix'_apply]
    apply congr_fun (DFunLike.congr_arg (fderiv ℝ (steering F V b) (arrival b)) ?_) i
    ext (x|x) <;> simp [Pi.single_apply]
  | inr j =>
    let H := fun z : Stem G F => (Sum.elim 0 z : Pack F G)
    have hd : HasFDerivAt H (ContinuousLinearMap.pi (Sum.elim (fun _ => 0) (fun i => ContinuousLinearMap.proj (R:=ℝ) i))) (fromColor G F.Free b) := by
        refine hasFDerivAt_pi.mpr ?_; rintro (i|i)
        · exact hasFDerivAt_const ..
        exact (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ => ℝ) i).hasFDerivAt
    have he : steering F V b ∘ H = fun v => displacement (mounted F V b) (mounted F V (paint G F.Free v)) := by
      ext1 v; dsimp only [steering,ride,Function.comp_apply]
      rw [show inGauge (H v)=0 from rfl,vary_zero,gaugeJoint_one]; rfl
    have ht : DifferentiableAt ℝ (steering F V b) (H (fromColor G F.Free b)) := (steering_diff ..).differentiableAt (by simp)
    rw [steered,sides_right, thrown, ← he,linearAt,linearAt, fderiv_comp _ ht hd.differentiableAt,hd.fderiv]
    rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
    apply congr_fun (DFunLike.congr_arg (fderiv ℝ (steering F V b) (arrival b)) ?_) i
    ext (x|x) <;> simp [Pi.single_apply]

lemma thrown_pins (x : Site f) (a : G.ColorIndex) (j) : thrown F V b (fixedSlot F x,a) j = 0 := by
  let L := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : JointKey G c f => ℝ) (fixedSlot F x,a))
  let H := fun z : Stem G F => displacement (mounted F V b) (mounted F V (paint G F.Free z))
  have h : DifferentiableAt ℝ H (fromColor G F.Free b) := ((matDiffAt_const _).displacement
    (mounted_diff F ((fromColor G F.Free).symm.contDiff.contDiffAt (x:=fromColor G F.Free b)) (matDiffAt_const V))
    (by rw [ContinuousLinearEquiv.symm_apply_apply])).differentiableAt (by simp)
  have he := fderiv_comp _ L.differentiableAt h
  rw [L.fderiv,show L ∘ H = fun _ : Stem G F => 0 by
        ext1 z; change delta _ _ a = _; rw [mounted_pins,mounted_pins,delta_self]; rfl,
    fderiv_fun_const] at he
  exact DFunLike.congr_fun he.symm _

lemma thrown_free (j k : Key F G) : thrown F V b (Sum.inl j.1.val,j.2) k =
    linearAt (fun z => displacement (vary (1:PatchField G F.Free) (fromColor G F.Free b)) (vary 1 z))
      (fromColor G F.Free b) j k := by
  let a := fromColor G F.Free b
  let L := (LinearMap.pi (R:=ℝ) fun j : Key F G => LinearMap.proj (φ:=fun _ => ℝ) ((Sum.inl j.1.val,j.2) : JointKey G c f)).toContinuousLinearMap
  let H := fun z : Stem G F => displacement (mounted F V b) (mounted F V (paint G F.Free z))
  have h : DifferentiableAt ℝ H a := ((matDiffAt_const _).displacement
    (mounted_diff F ((fromColor G F.Free).symm.contDiff.contDiffAt (x:=a)) (matDiffAt_const V))
    (by unfold a; rw [ContinuousLinearEquiv.symm_apply_apply])).differentiableAt (by simp)
  have he : L ∘ H = fun z : Stem G F => displacement (vary (1:PatchField G F.Free) a) (vary 1 z) := by
    funext z i
    change delta _ _ i.2 = delta _ _ i.2
    rw [mounted_free,mounted_free,vary_one,vary_one, show paint G F.Free a=b from (paint G F.Free).apply_symm_apply _]
    unfold delta; group
  rw [← he,linearAt,fderiv_comp _ L.differentiableAt h,L.fderiv]; rfl

section exp
open ContinuousLinearMap
variable {m : Type} [Fintype m] [DecidableEq m]

lemma displacement_det {P : ChartRatio G} (hp : LocalRatio P) (b : m → G.Color) (hb : ∀ i, b i∈Metric.ball 0 P.radius) :
    let a := fromColor G m b
    |(linearAt (fun z => displacement (vary (1:PatchField G m) a) (vary 1 z)) a).det| = ∏ i, P.J (b i) := by
  intro a
  let L := fromColor G m
  let H (i : m) (z : G.Color) := delta (G.lieExp (b i)) (G.lieExp z)
  have he (i : m) : DifferentiableAt ℝ (H i) (b i) := (delta_diff contDiffAt_const G.exp_jet.contDiffAt rfl).differentiableAt (by simp)
  let W := ContinuousLinearMap.pi fun i => (fderiv ℝ (H i) (b i)).comp (.proj i)
  have ht : HasFDerivAt (fun z : m → G.Color => fun i => H i (z i)) W b :=
    hasFDerivAt_pi.mpr fun i => (he i).hasFDerivAt.comp (g:=H i) b (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ => G.Color) i).hasFDerivAt
  have hh : (fun z => displacement (vary (1:PatchField G m) a) (vary 1 z)) =
      L ∘ (fun z i => H i (z i)) ∘ L.symm := by
    funext z ⟨i,j⟩; change delta _ _ j = _
    rw [vary_one,vary_one,show paint G m a=b from (paint G m).apply_symm_apply b]; rfl
  have hd : HasFDerivAt _ (L.toContinuousLinearMap.comp (W.comp L.symm.toContinuousLinearMap)) a :=
    L.hasFDerivAt.comp a ((show HasFDerivAt _ W (L.symm a) by simpa [a,L] using ht).comp a L.symm.hasFDerivAt)
  rw [linearAt_det, hh, hd.fderiv, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,ContinuousLinearMap.toLinearMap_comp]
  calc
    _ = |W.det| := congr_arg abs (LinearMap.det_conj W.toLinearMap L.toLinearEquiv)
    _ = ∏ i, |(fderiv ℝ (H i) (b i)).det| := by unfold W; rw [ContinuousLinearMap.det_pi,Finset.abs_prod]
    _ = _ := ?_
  exact Finset.prod_congr rfl fun i _ => exp_delta_det hp (hb i)
end exp

lemma steered_det {P : ChartRatio G} (hp : LocalRatio P) (hb : ∀ i, b i ∈ Metric.ball 0 P.radius) :
    |((steered F V b).submatrix (pins F G) id).det| = ∏ i, P.J (b i) := by
  let A := (steered F V b).submatrix (pins F G) id
  have h1 : A.toBlocks₁₁ = (R_tot S (mounted F V b)).submatrix (pins F G ∘ Sum.inl) id := by
    ext i j; change steered _ _ _ _ _ = _; rw [steered_eq]; rfl
  have h2 : A.toBlocks₁₂ = 0 := by
    ext i j; change steered _ _ _ _ _ = _; rw [steered_eq]; exact thrown_pins F V b i.1 i.2 j
  have h3 : A.toBlocks₂₂ = linearAt (fun z => displacement (vary (1:PatchField G F.Free) (fromColor G F.Free b)) (vary 1 z))
      (fromColor G F.Free b) := by
    ext i j; change steered _ _ _ _ _ = _; rw [steered_eq]; exact thrown_free F V b i j
  change |A.det|=_
  rw [← A.fromBlocks_toBlocks,h1,h2,h3, det_fromBlocks_zero₁₂,abs_mul,pins_det F _ (mounted_pins F V b),one_mul]; exact displacement_det hp b hb
end YM.Push.Loops
