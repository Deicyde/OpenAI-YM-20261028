import YM.RG08.Gaussian.TreeProjection

/-! # Inverting the quadratic slice Hessian
Metric positive. Auxiliary square not part of prescription on tree slice.
Algebra valid for any slice, projections to a crop not silently commuting
with inversion. Later cost result uses only repeated tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Exterior Precision Bloch Matrix
open Stationary Laurent Next.Free Work.F08 Tree FreeResolvent
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side}

lemma joint_vanish (S : StepData c f) {H : Row (TypeFace 2) (TypeFace 2)}
    : quadraticJoint G S (K (H.acts f))*spreadM (G:=G) S=0 := by
  -- `mean S * gradient = gradient * average` exactly
  have hv (x : BaseSites G f) : bondsM G S *ᵥ gradient x = tensor G (d 0 c) *ᵥ (curryG G S *ᵥ x) := by
    funext i; obtain ⟨i,a,b⟩ := i; obtain ⟨j,rfl⟩ := axisEquiv.surjective a
    unfold bondsM; rw [tensor_same,coord_map]; change component (tensor G (mean S) *ᵥ gradient x) b (i,coord j) =
      component (tensor G (d 0 c) *ᵥ (curryG G S *ᵥ x)) b (i,coord j)
    rw [component_mul, gradient,component_mul,component_mul,mean_site, d_sites]; simp only [component, ix,curry_at, mul_sub, Finset.sum_sub_distrib]
    rw [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply j]
  have hY v : butt G c f *ᵥ (spreadM (G:=G) S*ᵥ v) = -gradient v := by
    rw [parliament, helmet_butt,sliceX,helmet_ear,first_gradient]; rfl
  have hz v : brim G c f *ᵥ (spreadM (G:=G) S*ᵥ v) = -(curryG G S *ᵥ v) := by
    rw [parliament, helmet_brim,sliceY,helmet_ear]; rfl
  have hC : fortune G S * spreadM (G:=G) S =0 := by
    apply matrix_eq; intro x; rw [← Matrix.mulVec_mulVec,fortune, add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,hY,hz, neg_mulVec,
      mulVec_neg, hv, neg_neg, Matrix.mulVec_neg,tensor_same, add_neg_cancel,zero_mulVec]
  apply matrix_eq; intro x; rw [quadraticJoint,Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc (fortune G S)ᵀ,hC,Matrix.mul_zero,smul_zero,add_zero]
  let U := K (H.acts f)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec, mulVec_neg]
  change _ *ᵥ -(patron G U *ᵥ gradient x)=_
  have hx : patron G U *ᵥ gradient x=0 := by
    rw [gradient,← tensor_same, Matrix.mulVec_mulVec, ← patron_mul]; unfold U; rw [K_kills]; ext; rw [patron_fee]; simp [uniformM]
  rw [hx, neg_zero,Matrix.mulVec_zero,zero_mulVec]

lemma joint_vertical (S : StepData c f) (H : Row (TypeFace 2) (TypeFace 2)) :
    (cropJoint S G)ᵀ * quadraticJoint G S (K (H.acts f)) * cropJoint S G = fullMatrix G S H := by
  let A := cropJoint S G
  have ht : fortune G S*A= -(patron G (probe S)) := by
    rw [fortune, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, picks_butt, picks_brim, Matrix.mul_neg, Matrix.mul_one,
        base_test, tensor_same G (d 0 c), neg_add]; unfold stampZone; abel
  have hp := picks_butt (G:=G) S
  calc
    _ = ((butt G c f*A)ᵀ * patron G (K (H.acts f))* (butt G c f*A)) +
        S.kernel.penalty • ((fortune G S*A)ᵀ*(fortune G S*A)) := by
      simp only [quadraticJoint,A, Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul, transpose_mul, Matrix.mul_assoc]
    _ = fullMatrix G S H := by
      unfold fullMatrix baseMatrix
      rw [ht, show butt G c f * A=1 from hp,transpose_one,Matrix.one_mul, Matrix.mul_one,← tensor_same,patron_add,
        patron_scale, patron_mul,patron_star,transpose_neg,Matrix.neg_mul, Matrix.mul_neg,neg_neg]

lemma joint_symm (S : StepData c f) {H : Row (TypeFace 2) (TypeFace 2)}
    (hh : (H.acts f)ᵀ=H.acts f) : let K' := quadraticJoint G S (K (H.acts f)); K'ᵀ=K' := by
  intro K'; unfold K' quadraticJoint; rw [transpose_add,transpose_smul]; simp only [transpose_mul,
    transpose_transpose, ← patron_star,k_symmetric hh,Matrix.mul_assoc]

/-- The tree inverse from projecting the joint completion, not an estimate
    transported via closeness of kernels. -/
theorem projecting (S : StepData c f) (hS : S.patch.Branches S.kernel G)
    (T : Forest S.ratio) (t : S.Choices) {H : Row (TypeFace 2) (TypeFace 2)}
    {N : Matrix (Bodies G c f) (Bodies G c f) ℝ}
    (hr : (H.acts f)ᵀ=H.acts f)
    (hu : wideH G S t (K (H.acts f)) * N = 1) :
    let Z := (sprig S T G)ᵀ * projection S T G
    treeMatrix G S T H * (Z*N*Zᵀ) = 1 ∧
      projection S T G*N*(projection S T G)ᵀ=FreeResolvent.covariance G S T H := by
  intro Z
  let W := spreadM S (G:=G)
  let P := turnParameter S T G
  let V := postroom S t (inch S.patch.L) (G:=G)
  let M := quadraticJoint G S (K (H.acts f))
  let I := sprig S T G
  let F := cropJoint S G * I
  have hZ : Z*W=0 := by unfold Z; rw [Matrix.mul_assoc,tree_kills,Matrix.mul_zero]
  have hI : I*Z=projection S T G := by unfold I Z; rw [← Matrix.mul_assoc]; exact life S T
  have h₁ : Z*F=1 := by
    unfold Z F; rw [Matrix.mul_assoc,← Matrix.mul_assoc (projection S T G), show projection S T G * cropJoint S G * I=_ from tree_go ..]; exact insertion.orthogonal (plant T) (plant_inj T)
  have hM : treeMatrix G S T H=Fᵀ*M*F := by
    calc
      _ = Iᵀ*fullMatrix G S H*I := (insertion.compress (plant T) (fullMatrix G S H)).symm
      _ = _ := by rw [← joint_vertical]; unfold F M; rw [transpose_mul]; simp only [Matrix.mul_assoc]
  have hTr : V*W=grenade (inch S.patch.L) (1:Config G f) := fired S t hS
  have hL : IsUnit ((V*W)ᵀ) := by
    rw [transpose_mul,← transpose_mul,Matrix.isUnit_iff_isUnit_det, det_transpose,hTr]; exact fund_det (grenade_safe _ (inch_pos _))
  have hk : M*W=0 := joint_vanish S
  have ha : Wᵀ*M=0 := by
    calc
      _ = (M*W)ᵀ := by rw [transpose_mul,joint_symm S hr]
      _ = 0 := by rw [hk,transpose_zero]
  have he : (M+Vᵀ*V)*(N*Zᵀ)=Zᵀ := by rw [← Matrix.mul_assoc, show (M+Vᵀ*V)*N=1 from hu, Matrix.one_mul]
  have hg : V*(N*Zᵀ)=0 := by
    have hx : Wᵀ*((M+Vᵀ*V)*(N*Zᵀ))=0 := by rw [he,← transpose_mul, hZ, transpose_zero]
    rw [← Matrix.mul_assoc Wᵀ,Matrix.mul_add,ha,zero_add, ← Matrix.mul_assoc Wᵀ Vᵀ V, ← transpose_mul, Matrix.mul_assoc] at hx
    calc
      _ = ((V*W)ᵀ)⁻¹*((V*W)ᵀ*(V*(N*Zᵀ))) := by
        rw [← Matrix.mul_assoc ((V*W)ᵀ)⁻¹,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL), Matrix.one_mul]
      _ = _ := by rw [hx,Matrix.mul_zero]
  rw [Matrix.add_mul,Matrix.mul_assoc Vᵀ,hg,Matrix.mul_zero,add_zero] at he
  have hw : treeMatrix G S T H * (Z*N*Zᵀ)=1 := by
    rw [hM]
    have hh : F*Z=1+W*P := by unfold F; rw [Matrix.mul_assoc,hI]; exact tree_path S T
    calc
      _ = Fᵀ*(M*(F*Z))*(N*Zᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hh,Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc M W P,hk,Matrix.zero_mul,add_zero,Matrix.mul_assoc,he,← transpose_mul,h₁,transpose_one]
  constructor
  · exact hw
  unfold FreeResolvent.covariance
  change _ = I * resolve (treeMatrix G S T H) 0 * Iᵀ
  rw [resolve,zero_smul,add_zero,Matrix.inv_eq_right_inv hw,← hI]
  simp only [transpose_mul, Matrix.mul_assoc]

lemma psd_tree (S : StepData c f) (T : Forest S.ratio) {H : Row (TypeFace 2) (TypeFace 2)}
    (he : PosSemidef (H.acts f)) : PosSemidef (treeMatrix G S T H) := by
  have hx : PosSemidef (K (H.acts f)) := he.conjTranspose_mul_mul_same _
  have hu : PosSemidef (baseMatrix S H) :=
    hx.add ((posSemidef_conjTranspose_mul_self (probe S)).smul S.kernel.penalty_pos.le)
  apply PosSemidef.submatrix (M:=fullMatrix G S H)
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_,fun x => ?_⟩
  · exact full_symmetric H he.isHermitian
  let M := baseMatrix S H
  change 0 ≤ dotProduct (star x) (tensor G M*ᵥ x)
  rw [star_trivial,component_dot]; simp_rw [component_mul]
  apply Finset.sum_nonneg; intro i _; simpa using hu.dotProduct_mulVec_nonneg (component x i)

lemma origins_psd (k : ℝ) (hk : 0<k) {j : ℕ} (hj : 4≤j) (w : Train j) (m : Side) : ((pink k w).acts m).PosSemidef := by
  obtain ⟨v,D,hv,-,H⟩ := (heart_heats k hk hj (id : Train j → _)).1.funds
  have ⟨σ,c,hC,hc⟩ := (heart_saves k hk hj (id : Train j→_)).1.whole w
  obtain ⟨he,hr⟩ := obey_band _ (show Whole (pink k w) from ⟨σ,c,hC,hc⟩) (H w) m
  apply posSemidef_iff_dotProduct_mulVec.mpr; refine ⟨he,fun x => ?_⟩
  rw [star_trivial]; exact (mul_nonneg hv.le (normSum_nn _)).trans (hr x).1

end YM.RG08
