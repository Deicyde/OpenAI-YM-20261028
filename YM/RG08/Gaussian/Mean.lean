import YM.RG08.Gaussian.Covariance

/-! # Conditional kernel on cover: mean, precision and response lemmas
With color indices, tree-fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Precision Exterior Bloch Matrix
open Next.Free Work.F08 Tree Stationary FreeResolvent
open scoped Topology BigOperators Classical
variable {G : Gauge} {P : Patch} {c f : Side} {k : KernelChoices}

def probeRow (G : Gauge) (P : Patch) (k : KernelChoices) :=
    Classical.choose (Classical.choose_spec (frame_offer G P k 1 zero_lt_one)|>.2)
lemma probe_recites (G : Gauge) (P : Patch) (k : KernelChoices) :
    let A:= probeRow G P k
    Whole A ∧ ∀ (c f) (h : f.val=c.val*P.L.val), A.acts c=frameOffer G P k c f h :=
  ⟨⟨_,_,zero_lt_one,(Classical.choose_spec (Classical.choose_spec (frame_offer G P k 1 zero_lt_one)|>.2)).1⟩,
    (Classical.choose_spec (Classical.choose_spec (frame_offer G P k 1 zero_lt_one)|>.2)).2⟩
lemma probe_budget (G : Gauge) (P : Patch) (k : KernelChoices) (σ : ℝ) (hp : 0<σ) :
    ∃ A : ℝ, 0≤A ∧ (probeRow G P k).strip σ A := by
  obtain ⟨A,hA,F,h,H⟩ := frame_offer G P k σ hp
  refine ⟨A,hA,?_⟩
  have hu := probe_recites G P k
  rw [bank_injective hu.1.safe (Whole.safe ⟨_,_,hp,h⟩) (fun c => Eq.trans (hu.2 c (c*P.L) rfl) (H c (c*P.L) rfl).symm)]
  exact h

def coarseMean (G : Gauge) (X : Repeated P.L) (k : KernelChoices) (w : Train P.J) :=
    scaleRows k.penalty (composeRows (conditionalCov G X k w) (transRows (probeRow G P k)))

lemma determinant_weight (S : StepData c f) {A A' : FreeResolvent.FaceRow}
    {U : Matrix (Body 1 f) (Body 1 c) ℝ} (h : Inputs S U (A.acts f) (A'.acts c))
    (T : Forest S.ratio) : baseMatrix S A * extracted S T U = S.kernel.penalty • (probe S)ᵀ := by
  obtain ⟨hx,hY⟩:= stationed T _ _ _ h
  rw [baseMatrix, Matrix.add_mul,hY,Matrix.smul_mul, Matrix.mul_assoc,hx, Matrix.mul_sub,
      Matrix.mul_one,Matrix.mul_smul,smul_sub, smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]
  abel
lemma vanishes_mean (S : StepData c f) (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ) :
    let Q:=patron G (extracted S T U)
    ∀ x,Vanishes (S:=S) T (Q*ᵥ x) := by
  intro Q x i j hj
  unfold Q; rw [tensor_same, component_mul]; exact Precision.stays T U _ j hj
lemma linear_mean (S : StepData c f) (T : Forest S.ratio) {A A' : FreeResolvent.FaceRow}
    (hu : IsUnit (treeMatrix G S T A)) {U : Matrix (Body 1 f) (Body 1 c) ℝ}
    (h : Inputs S U (A.acts f) (A'.acts c)) :
    S.kernel.penalty • (FreeResolvent.covariance G S T A * (patron G (probe S))ᵀ) = patron G (extracted S T U) := by
  let Q := patron G (extracted S T U)
  let F:=treeMatrix G S T A
  let I:= sprig S T G
  let N:= fullMatrix G S A
  have hf : F=Iᵀ*N*I := (insertion.compress ..).symm
  have hz : I*(Iᵀ*Q)=Q := matrix_eq (fun x => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact projects T _ (vanishes_mean (G:=G) S T U x))
  have hp : N*Q=S.kernel.penalty • (patron G (probe S))ᵀ := by
    unfold Q N fullMatrix; rw [← tensor_same, ← patron_mul, determinant_weight S h T, patron_scale, patron_star]
  unfold FreeResolvent.covariance
  -- bring tree inverse through zero padding
  rw [← Matrix.mul_smul,← hp]
  change I* resolve F 0 * Iᵀ * (N*Q) = Q
  rw [resolve,zero_smul, add_zero]
  calc
    _ = I*F⁻¹*(Iᵀ * N* Q) := by simp only [Matrix.mul_assoc]
    _ = I * F⁻¹ * (F * (Iᵀ*Q)) := by rw [hf]; simp only [Matrix.mul_assoc,hz]
    _ = Q := by rw [← Matrix.mul_assoc (I*F⁻¹) F _, Matrix.mul_assoc I _ _, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one,hz]

/- finite sliced covariance laws for all tori compatible with the cover -/
theorem slice_compute (X : Repeated P.L) (w : Train P.J) (h : P.Branches k G) (c f : Side)
    (hu : f.val=c.val*P.L.val) :
    let S := linked P k c f hu
    let V := X.forest S.ratio; let M:=pink k.penalty w
    (conditionalCov G X k w).acts c = repackM (unitSplit G S 1) (unitSplit G S 1) (FreeResolvent.covariance G S V M) ∧
    treeInverse G S V M 0 * treeMatrix G S V M=1 ∧ (treeMatrix G S V M).PosDef ∧
    (coarseMean G X k w).acts c=k.penalty • ((conditionalCov G X k w).acts c * ((probeRow G P k).acts c)ᵀ) ∧
    ∀ (U : Matrix (Body 1 f) (Body 1 c) ℝ) (A' : FreeResolvent.FaceRow), Inputs S U (M.acts f) (A'.acts c) →
      (coarseMean G X k w).acts c=repackM (unitSplit G S 1) (Equiv.refl _) (patron G (extracted S V U)) := by
  intro S V M
  have hv := forest_precision G k w c f hu h V
  obtain ⟨hg,hQ⟩ := conditional_truth G X k w h
  obtain ⟨he,H⟩ := probe_recites G P k
  have ht : (coarseMean G X k w).acts c=_ := (acts_scale (composeRows (conditionalCov G X k w) (transRows (probeRow G P k))) k.penalty c).trans (by rw [hg.acts he.flipped,acts_trans])
  refine ⟨hQ c f hu, ?_, hv, ht,fun U A hX => ?_⟩
  · unfold treeInverse resolve; rw [zero_smul,add_zero]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hv.isUnit)
  have hc : (conditionalCov G X k w).acts c=_ := hQ c f hu
  have hF := H c f hu
  rw [ht,hc,hF]
  let p := unitSplit G S 1
  let R := Equiv.refl (Lines G c 1)
  change S.kernel.penalty • (repackM p p _ * (repackM R p _)ᵀ) = _
  have hx := linear_mean (G:=G) S V hv.isUnit hX
  rw [← hx, ← repack_rotate]; erw [← repack_multiply]; rfl

/- frame reset gain: a strip estimate for the rank-unprojected (tree) mean.
Only strict uses, since absolute constant may be L-dependent. -/
lemma mean_budget (G : Gauge) (X : Repeated P.L) (k : KernelChoices)
    {w : Train P.J} {σ A B : ℝ} (hp : (conditionalCov G X k w).strip σ A)
    (ht : (probeRow G P k).strip σ B) (hs : 0≤σ) :
    (coarseMean G X k w).strip σ (‖k.penalty‖*(Fintype.card (Co P.L (Loc G 1))*(A*B))) :=
  strip_scale (strip_compose hs hp (strip_trans ht)) _
end YM.RG08
