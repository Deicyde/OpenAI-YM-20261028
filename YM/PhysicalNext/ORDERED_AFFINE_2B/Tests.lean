import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen
import YM.AnalyticBridge.RESET_INCOME_PORT.Split
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.PhysicalNext.ORDERED_AFFINE_2B.Lift
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Charts

/-!
# Compare the actual ACTIVE argument and the cut/signed plaquette rows

Every comparison on the common sector `Plate e`; no other PathData
hypothesis/repair. `PathData.Bounds` from funding. Include every real color
and both plaquette-stack pieces, with the true channel transforms (cases
without a potential stencil still in both enumerations, zero a-rows as
proved when comparing to the kept data). No claim of row agreement after
forgetting/changing the true path lengths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Mapper
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome SectorTools.ActualScalar
open Further Further.CurvedGaussianJets
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f} (e : Plate G S) (A : Stores S)

abbrev Action := GaussianScalar.VV (GaussianScalar.Bits G (held e A))

/-- CGJ test array comes from the active log argument in common
positive orientation, extended by zero on frozen AND trunk.
No orthogonal axes chosen independent of Counting. -/
def logTest (x : Action e A) := Rows.fresh e.x (shots S e.x) A e.forest (Next.SectorChange.tape (chartMap e A x))

lemma comparing (x : Action e A) : collect G (Pockets.test (held e A) x) = logTest e A x := by
  funext p
  rw [Pockets.test_eq]; unfold SectorNext.Vacuum.FlatTree.blank logTest Rows.fresh; split <;> rename_i h
  · rfl
  · unfold Pockets.use; split <;> rename_i hp
    · rw [dif_neg (by simpa [held_iff] using hp)]
    rw [dif_pos (by simpa [held_iff] using hp)]
    let i : GaussianScalar.Standing (held e A) := ⟨⟨p,h⟩,hp⟩
    exact (tape_reads e A x i).symm

lemma test_restore (x : Action e A) (U : Config G f) (r : ℝ) :
    Shape.restore (held e A) U (r • x) = increment U (r • logTest e A x) := by
  unfold Shape.restore; rw [Shape.test_smul,← comparing e A]; rfl

variable (k : S.Choices) (V : Config G c)

def scheme := Mapping.table (held e A) e.tube.up e.tube.high (Stores.till e.x) V k

def values (x : Action e A) : SourceVec G c f := scheme e A k V *ᵥ x

lemma price_face0 (x : Action e A) (s : Signed) (i : Cell f) (j : G.ColorIndex) :
    let B0 := Shape.basic (held e A) (replica S.ratio V) s (G:=G)
    values e A k V x (faceAddr s i false j) = slip * (Real.sqrt e.tube.high.direct * ((B0 *ᵥ x) (Cut.turn f i,j))) := by
  intro B0; unfold values mulVec dotProduct scheme Mapping.table faceAddr Stacks.tall Stacks.stack Stacks.normalize
  simp only [Matrix.of_apply, Bool.false_eq_true,reduceIte, Sum.elim_inl, Matrix.smul_apply,smul_eq_mul, Finset.mul_sum,slip]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma price_face1 (x : Action e A) (s : Signed) (i : Cell f) (j : G.ColorIndex) :
    let U := replica S.ratio V
    values e A k V x (faceAddr s i true j) = slip * (((Shape.ell e.tube.up (Stores.till e.x) (pull s 0 U) * Shape.basic (held e A) U s) *ᵥ x) (Cut.turn f i,j)) := by
  intro U; unfold values mulVec dotProduct scheme Mapping.table faceAddr Stacks.tall Stacks.stack Stacks.normalize
  simp only [Matrix.of_apply, if_true, Sum.elim_inr,Sum.elim_inl,Matrix.smul_apply, Finset.mul_sum,slip]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma price_noise (x : Action e A) (i : Bond c) :
    solo (values e A k V x) i = -(Real.sqrt S.kernel.penalty • Shape.nozzle (held e A) (replica S.ratio V) k i x) := by
  ext j; change ((-(Real.sqrt S.kernel.penalty • Shape.fluid (held e A) (replica S.ratio V) k) *ᵥ x)
    (SectorNext.Vacuum.FlatTree.wheel c i,j))=_
  rw [Matrix.neg_mulVec,smul_mulVec,Shape.fluid]; simp_rw [Pi.neg_apply, Pi.smul_apply, Shape.row_test,Equiv.symm_apply_apply]; rfl

lemma face_direct (s : Signed) (i : Cell f) (x : Action e A) :
    Shape.direct (held e A) (replica S.ratio V) s (Cut.turn f i) x = plaquetteJet S V s i (logTest e A x) := by
  have h := Shape.direct_eq (held e A) (replica S.ratio V) s (Cut.turn f i) x
  simp_rw [Equiv.symm_apply_apply, test_restore e A] at h
  let X := fun a : Directions G f => G.curvature (faceValue (facade S s V a) i)
  have he : ContDiffAt ℝ ω X 0 := (Motion.plaquette_turn s V i (LocalJet.face_smooth _ i |>.contDiffAt)).1
  exact h.unique (Push.side X (he.differentiableAt (by simp)) (logTest e A x))

lemma basic_apply (s : Signed) (x : Action e A) (i : Cell f) (j : G.ColorIndex) :
    ((Shape.basic (held e A) (replica S.ratio V) s)*ᵥ x) (Cut.turn f i,j)=plaquetteJet S V s i (logTest e A x) j := by
  rw [Shape.basic,Shape.row_test]; exact congr_arg (fun u:G.Color=>u j) (face_direct e A V s i x)

lemma applied {C σ Λ : ℝ} {p : Clip} (h : e.tube.up.Bounds p σ C Λ) (s : Signed)
    (x : Action e A) (i : Cell f) (j : G.ColorIndex) :
    let U := replica S.ratio V; let N := Stores.till e.x
    ((Shape.ell e.tube.up N (pull s 0 U) * Shape.basic (held e A) U s)*ᵥ x) (Cut.turn f i,j) =
      barrel e.tube.up N (facade S s V 0) (fun p=>plaquetteJet S V s p (logTest e A x)) i j := by
  intro U N
  let v (p) := plaquetteJet S V s p (logTest e A x)
  let g (t) := v ((Cut.turn f).symm t)
  have hA := Shape.applied N h (pull s 0 U) g (Cut.turn f i,j)
  dsimp only at hA
  simp only [Equiv.symm_apply_apply] at hA
  have he (p : Shape.Page G f 2) : (Shape.basic (held e A) U s *ᵥ x) p = g p.1 p.2 := by
    rcases p with ⟨p,j⟩; obtain ⟨p,rfl⟩ := (Cut.turn f).surjective p
    rw [basic_apply]; unfold g; rw [Equiv.symm_apply_apply]
  rw [← Matrix.mulVec_mulVec, funext he, ← hA.tsum_eq, fixed_facade]
  let L := EuclideanSpace.proj (𝕜:=ℝ) j
  unfold barrel
  change _ = L _
  rw [L.map_tsum (barrel_summed e.tube.up N (pull s 0 U) (fun p=> v p) i h)]
  apply tsum_congr; intro t
  unfold Shape.amp g; dsimp only; split_ifs with ht
  · simp only [Equiv.symm_apply_apply]; rfl
  exact (map_zero L).symm

lemma faces {C σ Λ : ℝ} {p : Clip} (hb : e.tube.up.Bounds p σ C Λ) (x : Action e A) (s : Signed)
    (i : Twin f) (j : G.ColorIndex) :
    values e A k V x (faceAddr s i.1 i.2 j) = slip * ((Rows.faceKick e.tube e.x V (logTest e A x) s i) j) := by
  rcases i with ⟨p,b⟩; cases b
  · rw [price_face0,basic_apply]; rfl
  · rw [price_face1,applied _ _ _ hb]; rfl
end YM.PhysicalNext.OrderedAffine2B.Mapper
