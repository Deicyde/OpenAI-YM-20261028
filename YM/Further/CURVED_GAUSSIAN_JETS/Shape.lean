import YM.Further.CURVED_GAUSSIAN_JETS.Funding
import YM.Further.CURVED_GAUSSIAN_JETS.Law


/-!
# Common-key functions for the a coefficients of one actual affine prescription

All eventual identities `row *ᵥ x` in the F.Free physical
coordinates stretched with tree and inactive both zero in a. `V`
external, held Y not an input to the linear coefficients. K-dependent
terms in the actual integral, the affine constant part (including held
chart extensions) etc. handled elsewhere; here only the a slopes D.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets.Shape
open Function Filter Matrix Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum FlatTree Progress.StationaryScenes Pockets
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} (H : Finset F.Free)

abbrev Page (G : Gauge) (n : Side) (k : ℕ) := Body k n × G.ColorIndex
abbrev free (S : StepData c f) {F : Forest S.ratio} (H : Finset F.Free) : Soft H ↪ Body 1 f := (Embedding.subtype _).trans (Green.link F)

def translate (G : Gauge) : Vec (Bits H G) →ₗ[ℝ] Dir G f where
  toFun := test H
  map_add' x y := by
    ext i j; obtain ⟨p,rfl⟩ := (FlatTree.wheel f).surjective i
    change (collect G (test H (x+y)) p).ofLp j = (collect G (test H x) p).ofLp j + (collect G (test H y) p).ofLp j
    simp_rw [test_eq]; unfold FlatTree.blank; split <;> try simp
    unfold Pockets.use; split <;> try simp [linkBits]
  map_smul' r x := by
    ext i j; obtain ⟨p,rfl⟩ := (FlatTree.wheel f).surjective i
    change (collect G (test H (r • x)) p).ofLp j = r * (collect G (test H x) p).ofLp j
    simp_rw [test_eq]; unfold FlatTree.blank; split <;> try simp
    unfold Pockets.use; split <;> try simp [linkBits]
lemma test_smooth : ContDiff ℝ ω (Pockets.test (G:=G) H) := (Shape.translate H G).toContinuousLinearMap.contDiff
lemma test_smul (r : ℝ) (x : Vec (Bits H G)) : test H (r • x)=r • test H x := (Shape.translate H G).map_smul r x
lemma test_unit (j : Bits H G) (i : Body 1 f) : test H (Pi.single j 1) i = if free S H j.1=i then (EuclideanSpace.basisFun _ ℝ) j.2 else 0 := by
  obtain ⟨p,rfl⟩ := (FlatTree.wheel f).surjective i
  change collect G (test H (Pi.single j 1)) p = _
  rw [test_eq]
  change _ = if FlatTree.wheel f j.1.1.val = FlatTree.wheel f p then _ else (0:G.Color)
  simp only [(FlatTree.wheel f).injective.eq_iff]
  unfold FlatTree.blank; split <;> rename_i h
  · rw [if_neg (fun (he : j.1.1.val=p) => j.1.1.2 (he.symm ▸ h))]
  unfold Pockets.use; split <;> rename_i he
  · rw [if_neg (fun (h : j.1.1.val=p) => j.1.2 ((show (⟨p,_⟩:F.Free)=j.1.val from Subtype.ext h.symm) ▸ he))]
  unfold linkBits; split <;> rename_i hp
  · rw [show (⟨⟨p,h⟩,he⟩:Soft H)=j.1 from Subtype.ext (Subtype.ext hp.symm)]; ext z; by_cases hz : z=j.2 <;> simp [Prod.ext_iff,hz,EuclideanSpace.basisFun_apply]
  ext z; simp only [Pi.single_apply]; rw [if_neg (fun hq => hp ((congr_arg (fun t : Bits H G => t.1.1.1) hq).symm))]; rfl
lemma test_unit_norm (j : Bits H G) : ‖test H (Pi.single j 1)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> by rw [test_unit]; split <;> simp


def row {I X : Type*} [Fintype X] [DecidableEq X] (D : I → Vec X →L[ℝ] G.Color) := LinearMap.toMatrix'
    (LinearMap.pi (fun i : I × G.ColorIndex => (LinearMap.proj i.2) ∘ₗ (WithLp.linearEquiv 2 ℝ (Vec G.ColorIndex)).toLinearMap ∘ₗ (D i.1).toLinearMap))
lemma row_test {I X : Type*} [Fintype X] [DecidableEq X] (D : I → Vec X →L[ℝ] G.Color) (x : Vec X) (i : I × G.ColorIndex) :
    (row D *ᵥ x) i = (D i.1 x).ofLp i.2 := by rw [row,LinearMap.toMatrix'_mulVec]; rfl
lemma row_unit {I X : Type*} [Fintype X] [DecidableEq X] (D : I → Vec X →L[ℝ] G.Color) (i : I × G.ColorIndex) (j : X) :
    row D i j = (D i.1 (Pi.single j 1)).ofLp i.2 := rfl
lemma coord_paid (x : G.Color) (i : G.ColorIndex) : ‖x.ofLp i‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]; exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j (_:j∈Finset.univ)=>sq_nonneg ‖x.ofLp j‖) (Finset.mem_univ _))

def restore (U : Config G f) (x : Vec (Bits H G)) := increment U (collect G (test H x))
lemma restore_zero (U : Config G f) : restore H U 0=U := by unfold restore; rw [show test (G:=G) H 0=0 from (Shape.translate H G).map_zero]; exact Work.G07.at_zero_increment U
lemma restore_line (U : Config G f) (r : ℝ) (x : Vec (Bits H G)) : restore H U (r • x)=Pockets.step U (test H x) r := by rw [restore,test_smul]; rfl
lemma read_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Vec (Bits H G) → E) (h : DifferentiableAt ℝ u 0) (x : Vec (Bits H G)) :
    HasDerivAt (fun r : ℝ => u (r • x)) (fderiv ℝ u 0 x) 0 := by simpa only [zero_smul, one_smul] using!
      ((show DifferentiableAt ℝ u ((0:ℝ) • x) by simpa only [zero_smul] using h).hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hasDerivAt_id' (0:ℝ)).smul_const x))
end YM.Further.CurvedGaussianJets.Shape
