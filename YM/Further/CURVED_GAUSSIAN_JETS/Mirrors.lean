import YM.Further.CURVED_GAUSSIAN_JETS.Colors
import YM.Further.CURVED_GAUSSIAN_JETS.Nozzle
import YM.Further.CURVED_GAUSSIAN_JETS.Signed
import YM.Further.CURVED_GAUSSIAN_JETS.Spine
/-! # Identification at trivial field of affine coefficient tables -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Shape
open Function Filter Matrix Gauge Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum FlatTree Progress.StationaryScenes Work Pockets
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f c n : Side} {S : StepData c f} {F : Forest S.ratio} (H : Finset F.Free)

def hide {X : Type*} (M : Matrix X (Body 1 f) ℝ) : Matrix (X×G.ColorIndex) (Bits H G) ℝ := Tint.row G.ColorIndex (M.submatrix id (free S H))
lemma chart_column {X : Type*} [Fintype X] (M : Matrix X (Body 1 f) ℝ) (x : Vec (Bits H G)) (i : X×G.ColorIndex) :
    (hide H M*ᵥx) i = (M*ᵥparts G 1 (test H x) i.2) i.1 := by
  unfold hide Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_of_injective _ (free S H).injective
  · intro j hj; suffices test H x j=0 by simp [parts,this]
    unfold test blank Function.comp Pockets.use; dsimp only
    split_ifs; rfl; rfl
    exact (hj ⟨⟨⟨(wheel f).symm j, by assumption⟩, by assumption⟩,(wheel f).apply_symm_apply _⟩).elim
  · intro j; change _= _ * (collect G (test H x) j.val.val).ofLp _; rw [test_eq,FlatTree.blank,dif_neg j.val.property, Pockets.use,dif_neg j.property]; simp [Tint.row_apply,linkBits,ite_mul]

lemma pull_flat (s : Signed) (v : Dir G n) : pull s 0 (represent v)=represent (Bid.pulled v s) := by
  funext ⟨x,b⟩
  unfold pull Lattice.Step.read represent increment collect Bid.pulled; simp only [show axisEquiv.symm (coord b) = b from axisEquiv.symm_apply_apply _, Pi.one_apply,mul_one]
  split; · exact (ProjectorNext.Equivariance.exp_opposite _).symm
  rfl
lemma pulled_smul (s : Signed) (v : Dir G n) (r : ℝ) : Bid.pulled (r • v) s = r • Bid.pulled v s := by
  funext i; unfold Bid.pulled; simp only [Pi.smul_apply]; split <;> simp
lemma partMap (s : Signed) (v : Dir G n) (i : G.ColorIndex) : parts G 1 (Bid.pulled v s) i=Rot.map n s*ᵥ(parts G 1 v i) := by
  rw [Rot.swing_eq]; funext j; unfold FlatTree.swing FlatTree.beam parts Bid.pulled; dsimp only; split <;> rfl
lemma direct_flat (s : Signed) : Shape.basic (G:=G) H 1 s = hide H (d 1 f * Rot.map f s) := by
  apply Matrix.ext_of_mulVec_single; intro j; funext i
  obtain ⟨p,hp⟩ := (Cut.turn f).surjective i.1
  rw [Shape.basic,row_test,chart_column,← hp]
  let x : Vec (Bits H G) := Pi.single j (1:ℝ); let v := test H x
  have he := direct_eq H (1:Config G f) s (Cut.turn f p) x
  have hm (r : ℝ) : restore H 1 (r • x) = represent (r • v) := by rw [restore,test_smul]; rfl
  simp_rw [hm,pull_flat,pulled_smul, Equiv.symm_apply_apply] at he
  rw [←mulVec_mulVec, show Shape.direct H 1 s (Cut.turn f p) x = _ from he.unique (F03.curvature_of_hasDerivAt (F03.face_deriv p (Bid.pulled v s))),←partMap]; rfl
lemma noise_flat (k : S.Choices) (hh : S.patch.Branches S.kernel G) :
    Shape.fluid (G:=G) H 1 k = hide H (Precision.probe S) := by
  apply Matrix.ext_iff_mulVec.mpr; intro x; funext i
  rw [chart_column,Shape.fluid,row_test,nozzle,Push.settled S hh _ _,inv_one,G.mat_one]
  obtain ⟨p,hp⟩ := (wheel c).surjective i.1
  simp_rw [←hp,Equiv.symm_apply_apply]
  let g x := G.mat (readBond H 1 k p x)
  suffices he : fderiv ℝ g 0 x = G.colorMat (bills S (test H x) (wheel c p)) by
    change (G.projectColor (fderiv ℝ g 0 x * 1)).ofLp i.2 = _
    rw [mul_one,he,G.project_colorMat]; rfl
  have hg : ContDiffAt ℝ ω g 0 := ((show (test H (0:Vec (Bits H G)))=0 from (Shape.translate H G).map_zero).symm ▸ Push.prediction_cont S hh p k).comp _ (test_smooth H).contDiffAt
  have hx := read_deriv H _ (hg.differentiableAt (by simp)) x
  unfold g readBond restore at hx; simp_rw [test_smul] at hx
  exact hx.unique (Push.prices S hh p k (test H x))
end YM.Further.CurvedGaussianJets.Shape
