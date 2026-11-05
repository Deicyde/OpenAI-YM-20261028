import YM.Push.LOOP_COEFFICIENT.Grids
import YM.Push.LOOP_COEFFICIENT.Orientation

/-!
# Real kinetic precision in the actual normalized exponent and its unaveraged row
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Matrix Lattice RG Wilson Precision Exterior Bloch Bid
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {p : Clip} {T : PathData G} {H : Bed} {σ C Λ u v : ℝ}

def KRow (G : Gauge) (H : Bed) (n : Side) := liftMatrix G (Precision.K (H.metric.acts n))
lemma KRow_symm (H : Bed) (h : (H.metric.acts n).IsSymm) : (KRow G H n).IsSymm := by
  have he : (Precision.K (H.metric.acts n)).transpose = Precision.K (H.metric.acts n) := by rw [Precision.K,transpose_mul,transpose_mul,transpose_transpose,h,Matrix.mul_assoc]
  ext i j; rw [Matrix.transpose_apply]; unfold KRow; simp_rw [liftMatrix_entry]; split
  next h => simp only [h]; exact congr_fun (congr_fun he _) _
  next h => rw [if_neg (Ne.symm h)]

lemma lift_pair (M : Matrix (Body 1 c) (Body 1 f) ℝ) (v : Loops.Links G c) (w : Loops.Links G f) :
    v ⬝ᵥ (liftMatrix G M *ᵥ w) = ∑ i, layer G c i v ⬝ᵥ (M *ᵥ layer G f i w) := by
  simp only [dotProduct,Fintype.sum_prod_type,liftMatrix_apply]; conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun x _ => ?_))
  rw [← Equiv.sum_comp axisEquiv]; simp [layer_eq,parts]

lemma KRow_pair (H : Bed) (x y : Loops.Links G n) :
    x ⬝ᵥ (KRow G H n *ᵥ y) = gaugeFiscal H (chartEquiv G n x) (chartEquiv G n y) := by simp only [KRow,lift_pair,layer_eq,gaugeFiscal]

lemma paint_lift (M : Matrix (Body 1 c) (Body 1 f) ℝ) (v : Loops.Links G f) (i) : paint G _ (liftMatrix G M *ᵥ v) i =
    ∑ j, M (i.1,coord i.2) j • chartEquiv G f v j := by
  ext k; rw [paint_apply,liftMatrix_apply,layer_eq]; simp [Matrix.mulVec,dotProduct,parts]

lemma KRow_color (H : Bed) (u : G.El) : Carries (linkAdj (constantGauge (n:=n) u)) (linkAdj (constantGauge u)) (KRow G H n) (KRow G H n) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; apply (paint G (Bonds n)).injective; ext1 i
  simp_rw [KRow,paint_lift,linkAdj,paint_adjoints,paint_lift,map_sum,map_smul]; refine Finset.sum_congr rfl fun j _ => ?_
  rcases j with ⟨z,j⟩; obtain ⟨a,rfl⟩ := axisEquiv.surjective j
  simp [paint_adjoints,constantGauge]

lemma KRow_ward (H : Bed) : KRow G H n * R_g (1:Config G n) = 0 := by
  refine Matrix.ext_iff_mulVec.mpr fun w => ?_; rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]; funext i
  let v : form 0 n := fun j => w (j.1,i.2)
  have he : layer G n i.2 (R_g 1 *ᵥ w) = -(d 0 n *ᵥ v) := by
    funext ⟨x,j⟩; obtain ⟨j,rfl⟩ := axisEquiv.surjective j
    rw [coord_map,R_g, LinearMap.toMatrix'_mulVec]; change paint G (Bonds n) (brace 1 w) (x,axisEquiv.symm (coord j)) i.2 = _
    rw [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply j,paint_brace, Pi.one_apply,G.adjoint_one, Pi.neg_apply,d_sites]; change w _ - w _ = -(_-_); dsimp [v]; abel
  rw [KRow,liftMatrix_apply, he,Precision.K,← Matrix.mulVec_mulVec,Matrix.mulVec_neg,Matrix.mulVec_mulVec,closed, Matrix.zero_mulVec,neg_zero,Matrix.mulVec_zero]; rfl

lemma chart_pulled (s : Signed) (v : Loops.Links G n) : chartEquiv G n (linkSpin s (1:Config G n) *ᵥ v) = pulled (chartEquiv G n v) s := by
  funext ⟨x,j⟩; obtain ⟨j,rfl⟩ := axisEquiv.surjective j
  rw [coord_map,chartEquiv_apply,linkSpin,paint_direct,pulled,show axisEquiv.symm (coord j) = j from axisEquiv.symm_apply_apply j]; simp only [spins,Step.rotate,posDir,Bool.false_xor]; split <;> simp [sendEdge,posDir,Step.rotate]

lemma KRow_spin (h : Sworn H n G) (s : Signed) : (linkSpin s 1).transpose * KRow G H n * linkSpin s 1 = KRow G H n := by
  refine pairing_ext fun x y => ?_; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
  rw [KRow_pair,KRow_pair,chart_pulled,chart_pulled,h]






end YM.Push.Loops
