import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
A compatibility consumer *of the same affvd*. Cut difference kept as a
sum of limits when taking uncut gram. Here no claim that at the physical
field we can replace one by the other! Identify the *uncut flat* gram with
the Hess entry used by Gap. Separately prove PriceGap‐like gap even with the
ℓ truncation via the canonical oriented direct and predictor responses.
Both count physical tangent directions including the harmonic perturbations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Flat
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
  YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
  YM.Next.Fluctuations YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented Rows
open scoped Topology BigOperators Classical InnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

def labels (a : Directions G f) : Dir G f := fun i => a (i.1, axisEquiv.symm i.2)
@[simp] lemma collected (a : Directions G f) : collect G (labels a) = a := by
  funext i; unfold labels collect; rcases i with ⟨x,v⟩; exact congr_arg (fun j => a (x,j)) (axisEquiv.symm_apply_apply v)

lemma labels_pull_smooth (s : Signed) : ContDiff ℝ ω (fun a : Directions G f => pulled (labels a) s) := by
  apply contDiff_pi.mpr
  intro i; dsimp only [pulled, labels]; split
  · exact (contDiff_apply _ _ _).neg
  · exact (contDiff_apply _ _ _)

lemma facade_at (s : Signed) (a : Directions G f) (t : ℝ) :
    facade S s 1 (t • a)=represent (t • pulled (labels a) s) := by
  unfold facade; rw [replica_one, ← Work.F03.represent_pulled]; congr 1
  unfold represent
  congr 1
  change _ = t • collect G (labels a)
  rw [collected]

lemma facade_all (s : Signed) (a : Directions G f) :
    facade S s 1 a=represent (pulled (labels a) s) := by simpa using facade_at (S:=S) s a 1

lemma flat_curl (S : StepData c f) (s : Signed) (p : Cell f) (a : Directions G f) :
    plaquetteJet S 1 s p a=Work.F03.faceCurl p (pulled (labels a) s) := by
  let F := fun y : Directions G f => G.curvature (faceValue (facade S s 1 y) p)
  have he : DifferentiableAt ℝ F 0 := by
    suffices ContDiffAt ℝ ω F 0 from this.differentiableAt (by simp)
    apply curvature_diff_mat
    simp_rw [facade_all]
    -- plaquette mat is analytic
    unfold faceValue square travel Step.read
    simp only [G.mat_mul,G.mat_inv,G.mat_one]
    have hp (e : Bond f) : ContDiff ℝ ω (fun y : Directions G f => G.mat (represent (pulled (labels y) s) e)) :=
      (Work.F03.represent_smooth _).comp (labels_pull_smooth s)
    have hh (e : Bond f) := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (hp e)
    simp only [negDir,posDir,Bool.false_eq_true, ↓reduceIte,G.mat_inv] at *
    apply ContDiff.contDiffAt; apply ContDiff.mul (hp _); apply ContDiff.mul (hp _); exact (hh _).mul ((hh _).mul contDiff_const)
  unfold plaquetteJet; apply (YM.Push.side F he a).unique
  unfold F; simp_rw [facade_at]
  exact Work.F03.curvature_of_hasDerivAt (Work.F03.face_deriv p _)

lemma flat_probe (s : Signed) (k : S.Choices) (b : Bond c) (a : Directions G f) (h : S.patch.Branches S.kernel G) :
    blockJet 1 k s b a=bills S (pulled (labels a) s) (b.1,coord b.2) := by
  let F := fun y : Directions G f => G.curvature (predictorTurn 1 k s b y)
  have hz : pulled (labels (0:Directions G f)) s = 0 := by funext; unfold pulled labels; dsimp only [Pi.zero_apply]; split <;> simp
  have ht : predictGroup (1:Config G c) k s b 0=1 := by rw [predictGroup,facade_all,hz,link_one]; exact YM.Push.settled S h b _
  have he : DifferentiableAt ℝ F 0 := by
    suffices ContDiffAt ℝ ω F 0 from this.differentiableAt (by simp)
    apply curvature_diff_mat
    simp_rw [predictorTurn,ht,inv_one,mul_one,predictGroup,facade_all]
    have he := YM.Push.prediction_cont S h b (choice s k)
    rw [← hz] at he
    exact he.comp (f:=fun a => pulled (labels a) s) (0 : Directions G f) (labels_pull_smooth s).contDiffAt
  apply (YM.Push.side F he a).unique
  simp_rw [F, predictorTurn,ht,inv_one,mul_one,predictGroup,facade_at]
  exact Work.F03.curvature_of_hasDerivAt (YM.Push.prices S h b (choice s k) _)

lemma stationary_labels (a : Directions G f) : pulled (labels a) 1=labels a := by
  funext i
  unfold pulled
  simp only [affine,Signed.act_one,add_zero]
  have he (k : TypeFace 1) : coord (axisEquiv.symm k) = k := axisEquiv.apply_symm_apply k
  simp only [Step.rotate_one,posDir,Step.used,Bool.false_eq_true, ↓reduceIte,he,Prod.mk.eta]

/-- Pulls of the prediction really give the physical permuted block
terms at this order, even across the signed discrepancy noted at 
(which is a *non-flat* issue). -/
lemma bills_signed (S : StepData c f) (s : Signed) (k : S.Choices) (b : Bond c) (a : Dir G f) (h : S.patch.Branches S.kernel G) :
    bills S (pulled a s) (pole b) = pulled (bills S a) s (pole b) := by
  have hl := YM.Push.prices S h b (choice s k) (pulled a s)
  have hr := YM.Push.prices S h (sendEdge s 0 b) k a
  change HasDerivAt (fun v : ℝ => G.mat (S.prediction (represent (v • pulled a s)) (choice s k) b)) (G.colorMat (bills S (pulled a s) (pole b))) 0 at hl
  change HasDerivAt (fun v : ℝ => G.mat (S.prediction (represent (v • a)) k (sendEdge s 0 b))) (G.colorMat (bills S a (pole _))) 0 at hr
  simp_rw [← Work.F03.represent_pulled, (carry s h k _).2] at hl
  let e := (posDir b.2).rotate s
  have he : axisEquiv.symm (pole b).2=b.2 := axisEquiv.symm_apply_apply b.2
  dsimp only [pulled]; rw [he]
  unfold pull Step.read at hl
  by_cases hx : e.neg
  unfold e at hx
  · rw [if_pos hx]
    simp_rw [if_pos hx,G.mat_inv] at hl
    apply G.colorMat_injective
    rw [map_neg, ← Gauge.colorMat_skew]
    exact hl.unique hr.star
  unfold e at hx
  rw [if_neg hx]; simp_rw [if_neg hx] at hl
  exact G.colorMat_injective (hl.unique hr)



section price
variable (T : Tube G S) (V : Config G c) (k : S.Choices) (x : ℝ)

/-- ideal uncut bump (defined on all directions, even off tree). -/
def ideal (a : Directions G f) : LogArray G (Slots S) := fun i =>
  i.2.elim (fun j => xLin T.high T.up (pulled (labels a) i.1) j) (fun b => zLin S (pulled (labels a) i.1) 0 b)

variable (H : Bed) {o r E σ Λ : ℝ}
include k


end price
end YM.Next.SectorChange.Flat
