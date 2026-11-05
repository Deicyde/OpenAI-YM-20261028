import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.AffineRows
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Geometry
import YM.Push.FREE_RESOLVENT.Columns
import YM.Push.FREE_RESOLVENT.TrackBill


/-!
# The two actual ordered matrices read on the same flat comparison step

No permission to exchange matrices of the same size: mandatory boundary
and channel contributions. Even flat there is a path-length cut before
taking the Gram. General active-certificate correspondence first, then
specialize to all just tree-free and no flags (E's A_R(0)), and to
A_R(B) with B in the common neighborhood (eg for probing low Taylor
jets). Never replace that cut tree R by `treeMatrix` with full recursive H
by a projection identity; latter correspondence is on the FULL path
matrix and requires the appropriate Retained PathData and the other
H receipts. Price of cutting in a later file.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

namespace Assembly

lemma extended {A : Stores S} {F : Forest S.ratio} {x : ℝ} (v : Prices G (SectorChange.Active A x F)) (W : Stencils S) :
    actual (FreeResolvent.insertion (register A F x G) *ᵥ v)=Rows.fresh x W A F (tape v) := by
  funext i
  ext j
  let r := register A F x G; let k := (i.1,coord i.2,j)
  change (FreeResolvent.insertion r *ᵥ v) k = _
  unfold fresh
  by_cases hi : i∈F.trunks
  · rw [dif_neg (not_not_intro hi)]
    rw [FreeResolvent.insertion_misses r v k ?_]; rfl
    rintro ⟨a,ha⟩
    have hb : ((i,j):RawLink G _) = originLink A F x G a := (rawEquiv G _).injective ha.symm
    apply a.1.val.property; exact (show i=a.1.val.val from congr_arg Prod.fst hb) ▸ hi
  let l : F.Free := ⟨i,hi⟩
  rw [dif_pos hi]
  by_cases he : chill A x F l
  · rw [dif_neg (show ¬¬chill A x F l from not_not_intro he)]
    rw [FreeResolvent.insertion_misses r v k ?_]; rfl
    rintro ⟨a,ha⟩
    have hb : ((i,j):RawLink G _) = originLink A F x G a := (rawEquiv G _).injective ha.symm
    apply a.1.property; exact (show l=a.1.val from Subtype.ext (congr_arg Prod.fst hb)) ▸ he
  rw [dif_pos he]
  let a : In x A F (G:=G) := (⟨l,he⟩,j)
  exact insertion_at r v r.injective a

lemma path_raw (S : StepData c f) (s : Signed) (p : Cell f) (B : Coarse G c) (T : Tube G S)
    (v : Warm G f) (R : ℕ) {σ C Λ : ℝ} (hT : T.up.Bounds T.high σ C Λ) :
    let e := Affine.response S s B *ᵥ v
    let n := Affine.tracks S s T.up (Affine.shorter R) B *ᵥ e
    Affine.decode n (p.1,plaquette p.2)=barrel T.up R (facade S s (enroll B) 0)
      (fun i => oldFace S B s i v) p := by
  intro e n
  have hP := Affine.reads_row S s T.up (Affine.shorter R) hT.width.le (show Affine.Sheet T.up σ C from hT.rows) B (Affine.decode e) p
  rw [Affine.flat_decode] at hP
  refine hP.tsum_eq.symm.trans (tsum_congr (fun i => ?_))
  unfold Affine.shorter
  -- maybe barrel already unfolded
  dsimp only; simp only [decide_eq_true_eq]
  split
  next H =>
    let u := (T.up.row p.2 i).2
    have hh : facade S s (enroll B) 0=Affine.shone S s B := by rw [fixed_facade]; rfl
    rw [hh]
    change (T.up.row p.2 i).1 • G.adjoint _ (Affine.decode e (wrap _ u.offset+p.1,plaquette u.plaq))= _
    exact congr_arg (fun z => (T.up.row p.2 i).1 • G.adjoint (travel (Affine.shone S s B) p.1 u.walk) z) (respond S B s v (Work.F03.slotFace u p.1))
  rfl

/-- E selected raw at arbitrary V(B) including where FR.duct does
NOT authorize any response. Keep distinct from FR.block, even though
we can align near zero below. -/
def repaired (S : StepData c f) (T : Tube G S) (x : ℝ) (k : S.Choices) (B : Coarse G c) :=
    (Fintype.card Signed:ℝ)⁻¹ • ∑ s : Signed,
    let H := Affine.response S s B
    let Q := individual S B s k
    T.high.direct • Affine.squareQ H + Affine.squareQ (Affine.tracks S s T.up (Affine.shorter (till x)) B * H)+ S.kernel.penalty • Affine.squareQ Q

theorem repaired_of_collective (S : StepData c f) (T : Tube G S) (x : ℝ) (k : S.Choices) (B : Coarse G c)
    (h : ∀ (s : Signed), Affine.duct S s k B=individual S B s k) :
    Affine.block S k T.high T.up (Affine.shorter (till x)) B=repaired S T x k B := by
  unfold Affine.block repaired; simp only [Affine.channel,h]

section
variable (S : StepData c f) (T : Tube G S) (x : ℝ) (B : Coarse G c) (k : S.Choices) (V : Stores S) (F : Forest S.ratio)
  {σ C Λ : ℝ} (hT : T.up.Bounds T.high σ C Λ)
include hT

private lemma repairs (v w : Warm G f) :
    v ⬝ᵥ (repaired S T x k B *ᵥ w) =
      tape.symm (slip • bump T x (enroll B) k (actual v)) ⬝ᵥ tape.symm (slip • bump T x (enroll B) k (actual w)) := by
  have hx (u v : LogArray G (Slots S)) : tape.symm u ⬝ᵥ tape.symm v = ∑ i, inner ℝ (u i) (v i) := by
    simp_rw [dotProduct,Fintype.sum_prod_type,Work.F03.inner_color]; rfl
  have hsp : slip*slip=(Fintype.card Signed:ℝ)⁻¹ := by
    unfold slip; rw [← mul_inv,Real.mul_self_sqrt (by positivity)]
  rw [hx,Fintype.sum_prod_type]
  simp_rw [Pi.smul_apply,real_inner_smul_left,real_inner_smul_right,← mul_assoc slip, hsp,← Finset.mul_sum]
  rw [repaired,Matrix.smul_mulVec,Matrix.sum_mulVec,dotProduct_smul,dotProduct_sum,smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  let H := Affine.response S s B
  let U := Affine.tracks S s T.up (Affine.shorter (till x)) B
  let A := individual S B s k
  let u := enroll B; let c0 := T.high.direct; let k0 := S.kernel.penalty
  let I (x y : G.Color) := inner ℝ x y
  have hF : Real.sqrt c0 * Real.sqrt c0 = c0 := Real.mul_self_sqrt T.high.quadratic_pos.le
  have hA : Real.sqrt k0 * Real.sqrt k0 = k0 := Real.mul_self_sqrt S.kernel.penalty_pos.le
  have hh {ι : Type} [Fintype ι] (N : Matrix ι (Affine.raw G f) ℝ) :
      v ⬝ᵥ (Affine.squareQ N *ᵥ w) = (N *ᵥ v) ⬝ᵥ (N *ᵥ w) := by rw [Affine.squareQ,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,dotProduct_comm]
  have hg {n : Side} {l : ℕ} (v w : FreeResolvent.Vec G n l) :
      v ⬝ᵥ w = ∑ i, I (Affine.decode v i) (Affine.decode w i) := FreeResolvent.flat_dot (Affine.decode v) (Affine.decode w)
  change v ⬝ᵥ ((c0 • Affine.squareQ H + Affine.squareQ (U*H) + k0 • Affine.squareQ A) *ᵥ w) =
    ∑ i : Twin f ⊕ Bond c,I (bump T x u k (actual v) (s,i)) (bump T x u k (actual w) (s,i))
  rw [Matrix.add_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_add,dotProduct_smul,dotProduct_smul]
  simp_rw [smul_eq_mul, hh]
  rw [Fintype.sum_sum_type]
  congr 1
  · let P i (z : Warm G f) := Affine.decode (H*ᵥz) (i.1,plaquette (i : Cell f).2)
    let Q i (z : Warm G f) := Affine.decode ((U*H)*ᵥz) (i.1,plaquette (i : Cell f).2)
    let E := Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv
    have he (F : FreeResolvent.Vec G f 2) (N : FreeResolvent.Vec G f 2) := (hg F N).trans (E.sum_comp (fun i => I (Affine.decode F i) (Affine.decode N i))).symm
    have hL (i : Cell f) (d : Bool) (z : Warm G f) : bump T x u k (actual z) (s,.inl (i,d)) = if d then Q i z else Real.sqrt c0 • P i z := by
      change faceKick T x u (actual z) s (i,d) = _
      unfold faceKick; cases d
      · dsimp only
        have hh : P i z=_ := respond S B s z i
        simp [hh,oldFace]; rfl
      · dsimp only
        have h : Q i z=_ := (show Q i z=Affine.decode (U*ᵥ(H*ᵥz)) _ from (by unfold Q; rw [Matrix.mulVec_mulVec])).trans (path_raw S s i B T z (till x) hT)
        simp [h,oldFace]; rfl
    rw [he,he,Finset.mul_sum,← Finset.sum_add_distrib]
    conv_rhs => unfold Twin; rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp_rw [hL,I]
    simp only [Bool.false_eq_true,↓reduceIte,real_inner_smul_left,real_inner_smul_right,← mul_assoc,hF]
    change c0 * inner ℝ (P i v) (P i w) + _ = _
    rw [add_comm]; rfl
  · let E := Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv
    have he := E.sum_comp (fun i => I (Affine.decode (A *ᵥ v) i) (Affine.decode (A *ᵥ w) i))
    rw [hg,← he, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change k0 * I (Affine.decode (A *ᵥ v) (pole i)) (Affine.decode (A*ᵥw) (pole i))=I (noiseKick u k (actual v) s i) (noiseKick u k (actual w) s i)
    unfold I; rw [individual_read S B s k v, individual_read S B s k w]
    unfold oldNoise noiseKick
    rw [inner_neg_left,inner_neg_right,neg_neg,real_inner_smul_left,real_inner_smul_right,← mul_assoc]
    rw [show Real.sqrt S.kernel.penalty*Real.sqrt S.kernel.penalty = S.kernel.penalty from hA]

/-- Exact counting identity for the actual cut selected precision,
including holes; valid even where FR doesn't have differentiable noise
by keeping `individual` (b premise not used). -/
theorem sub_gram (hP : S.patch.Branches S.kernel G) :
    Rows.gram T x (enroll B) k (shots S x) V F=(repaired S T x k B).submatrix (register V F x G) (register V F x G) := by
  let M := move T x (enroll B) k (shots S x) V F
  let J := FreeResolvent.insertion (register V F x G)
  have he (v w : Prices G (SectorChange.Active V x F)) :
      v ⬝ᵥ (Rows.gram T x (enroll B) k (shots S x) V F *ᵥ w)= (J*ᵥv) ⬝ᵥ (repaired S T x k B *ᵥ (J*ᵥw)) := by
    rw [Rows.gram,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,dotProduct_comm (_ *ᵥ w)]
    simp_rw [moved T x (enroll B) k (shots S x) V F hT,selected_all T x (enroll B) k V F _ hP]
    rw [repairs S T x B k hT]
    unfold J; rw [extended v (shots S x),extended w (shots S x)]
  ext i j
  have ht := he (Pi.single i 1) (Pi.single j 1)
  unfold J at ht; rw [FreeResolvent.insertion.dot_compress] at ht
  simpa only [Matrix.mulVec_single_one,single_dotProduct,one_mul, Matrix.col_apply] using ht
end
end Assembly
end YM.AnalyticBridge.LocalGaussianLaws
