import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Frozen
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Scans
import YM.Extra.ITERATION_NO_LOSS.Kernels
import YM.Extra.ITERATION_NO_LOSS.Scales
import YM.Extra.WILSON_STARTUP.Builder
import YM.PhysicalNext.ORDERED_AFFINE_2B.Fixed
import YM.Progress.DIRECTED_RECIPE.Rollout
import YM.Progress.JOINT_CALENDAR.Period
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Picks
import YM.Push.ABSOLUTE_SUMS.Path
import YM.Push.GRID_APPROXIMATION.Roll
import YM.Push.PRICE_COMPILER.Builders
import YM.Push.STRESS_FLUX.FreeBridge
import YM.SectorNext.VACUUM_NORMALIZATION.Clinic
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques
import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
import YM.UVNext.PRICED_KERNELS.Crews

/-!
# On all positive coordinate keys

Use the full-key prescriptions for recording also reads which might not
be active, such that even local comparisons across changes away from a
site keep ALL these addresses. This compares Means **because only the
active block and its zero cross act**. Not claiming a full C completion
away from the authorized/gapped values. Even proves the required lookup
eqs with dummy inverse if singular at some wrong-flag distant tables, no
conventions on Y. No spectral estimate on the broader domain is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Footprint
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.Covariance AnalyticBridge.Covariance.Terrain
open AnalyticBridge.SectorAffine NonflatCovarianceLocality
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Completion
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f}

namespace Padded
variable (T : Tube G S) (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c)




-- spelling with `scanD` = reads all columns with zero even on tree
-- and frozen. `Rf` either actual/hard or our extension R-map.
def send (v : Prices G (Slots S)) := (scanD T A F k x V)ᵀ *ᵥ v
def align (v : Prices G (Slots S)) := -(lookPi T A F k x 0 V)ᵀ *ᵥ send T x k A F V v
def owed (v : Prices G (Slots S)) := scanA T A F k x V *ᵥ align T x k A F V v + send T x k A F V v
def bill (v : Prices G (Slots S)) := scanD T A F k x V *ᵥ align T x k A F V v + v

def widen (v : Prices G (Active A x F)) : Covariance.Atom G f → ℝ := (Sum.elim v (fun _=>0)) ∘ (sorted A F).symm
lemma widen_at (v : Prices G (Active A x F)) (j : Layer G A F x) :
    widen x A F v (sorted A F j) = j.elim (v ·) (fun _=>0) := by rw [widen,Function.comp_apply,Equiv.symm_apply_apply]
lemma widen_cost (v : Prices G (Active A x F)) (j : Covariance.Atom G f) (he : ¬ onStage A F x j.1) : widen x A F v j = 0 := by
  obtain ⟨(i|i),rfl⟩ := (sorted A F (G:=G) (x:=x)).surjective j <;> rw [widen_at]
  · exact False.elim (he ((Terrain.acts_here A F).2 ⟨i.1,rfl⟩))
  rfl

lemma push_if (y : Covariance.Atom G f) (h : 120 ≤ radiusB x) : y ∈ unitWin S x y := by
  intro i hi j hj
  apply (separation_triangle i (home S y) j).trans
  have he : separation i (home S y) ≤ 1 := by rw [separation_comm]; exact meetings _ hi
  have hf : separation (home S y) j ≤ 1 := meetings _ hj; omega

lemma complete_A (w : Prices G (Active A x F)) :
    scanA T A F k x V *ᵥ widen x A F w = widen x A F (Fixed.precision T x A F k V *ᵥ w) := by
  let r := sorted A F (G:=G) (x:=x)
  let L := scanA T A F k x V
  let M := Fixed.precision T x A F k V
  funext j; obtain ⟨j,rfl⟩ := r.surjective j
  have hv : L.submatrix r r = wide M 1 := backA ..
  let w' : Layer G A F x → ℝ := Sum.elim w 0
  have he := congr_fun (Matrix.submatrix_mulVec_equiv L w' (⇑r) r) j
  rw [hv, Completion.wide_move,Matrix.one_mulVec] at he
  rw [widen_at]; exact he.symm

lemma send_through (v : Prices G (Slots S)) :
    send T x k A F V v=widen x A F ((Fixed.D T x A F k V)ᵀ *ᵥ v) := by
  funext j; obtain ⟨(i|i),rfl⟩ := (sorted A F (G:=G) (x:=x)).surjective j <;> rw [widen_at] <;>
      simp_rw [send,mulVec,dotProduct,Matrix.transpose_apply,pick]
  · rfl
  simp


private lemma only_side {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {W : α⊕β → Set (α⊕β)} (hW : ∀ i, i∈W i) {s : α→Set α} (hs : s = fun i => Sum.inl ⁻¹' W (.inl i))
    (M : Matrix α α ℝ) (z : α → ℝ) :
    -(panes W 0 (wide M 1))ᵀ *ᵥ (Sum.elim z 0) = Sum.elim (-(Schur.per s M)ᵀ *ᵥ z) 0 := by
  have hP i j := Full.side W M 0 le_rfl (fun i => hW (.inl i)) hs i j
  have hC := Full.across W M 0 le_rfl hW
  simp_rw [panes_zero s M] at hP
  funext i; rcases i with i|i
  · simp only [mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]
    refine Finset.sum_congr rfl fun j _=> ?_
    rw [Matrix.neg_apply,Matrix.neg_apply, Matrix.transpose_apply,Matrix.transpose_apply, hP]
  simp only [mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]
  refine Finset.sum_eq_zero fun j _=>?_ ; rw [Matrix.neg_apply,Matrix.transpose_apply,(hC j i).1,neg_zero,zero_mul]

lemma per_complete (z : Prices G (Active A x F)) (hx : 120 ≤ radiusB x) :
    -(lookPi T A F k x 0 V)ᵀ *ᵥ widen x A F z = widen x A F (-(Schur.per (panels A F) (Fixed.precision T x A F k V))ᵀ *ᵥ z) := by
  let r := sorted A F (G:=G) (x:=x); let W := allPanels A F (G:=G) (x:=x)
  let L := lookPi T A F k x 0 V; let M := Fixed.precision T x A F k V
  have hr1 := backPi T A F k x 0 V
  have he : L.submatrix r r = panes W 0 (wide M 1) := by
    unfold L r W M NonflatCovarianceLocality.panes Fixed.precision; unfold backPrice at hr1; convert hr1 using 2
  have hW (i : Layer G A F x) : i∈W i := push_if x (S:=S) (r i) hx
  let z' : Layer G A F x → ℝ := Sum.elim z 0
  let N := panes W 0 (wide M 1)
  have hB : (-(Lᵀ)).submatrix r r = -(Nᵀ) := by rw [←show L.submatrix r r=N from he]; rfl
  have h := Matrix.submatrix_mulVec_equiv (-Lᵀ) z' (⇑r) r; rw [hB] at h
  have hN : -Nᵀ *ᵥ z'= Sum.elim (-(Schur.per (panels A F) M)ᵀ *ᵥ z) (fun _=>0) := by
    unfold N z'
    convert only_side (α:=In x A F (G:=G)) (β:=vacant A F x G) hW (s:=panels A F) rfl M z using 5; first | apply Subsingleton.elim | rfl
  funext j; obtain ⟨j,rfl⟩ := r.surjective j; rw [widen_at]; have hh := congr_fun (h.symm.trans hN) j;
  exact hh

lemma align_pay (v : Prices G (Slots S)) (hx : 120 ≤ radiusB x) :
    align T x k A F V v = widen x A F (- (Schur.per (panels A F) (Fixed.precision T x A F k V))ᵀ *ᵥ ((Fixed.D T x A F k V)ᵀ *ᵥ v)) := by
  unfold align; rw [send_through,per_complete _ _ _ _ _ _ _ hx]

lemma product_D (z : Prices G (Active A x F)) :
    scanD T A F k x V *ᵥ widen x A F z = Fixed.D T x A F k V *ᵥ z := by
  funext i; let r := sorted A F (G:=G) (x:=x); unfold Matrix.mulVec dotProduct; rw [← Equiv.sum_comp r,Fintype.sum_sum_type];
  -- simp by pick
  unfold r; simp_rw [pick,widen_at]; simp

variable (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F))

theorem exact (h : 120 ≤ radiusB x) :
    let v := Fixed.zeroRow T x A F k q d Y V
    send T x k A F V v=widen x A F (Fixed.forceB T x A F k q d Y V) ∧
    align T x k A F V v=widen x A F (Fixed.mean T x A F k q d Y V) ∧
    owed T x k A F V v=widen x A F (Fixed.rest T x A F k q d Y V) ∧
    bill T x k A F V v=Fixed.tip T x A F k q d Y V := by
  intro v; let b := Fixed.forceB T x A F k q d Y V; let μ := Fixed.mean T x A F k q d Y V
  have hb : send T x k A F V v=widen x A F b := send_through ..
  have hm : align T x k A F V v=widen x A F μ := align_pay T x k A F V v h
  refine ⟨hb,hm,?_,?_⟩
  · unfold owed; rw [hb,hm,complete_A]
    change widen _ _ _ _ + widen _ _ _ _=widen _ _ _ (_+_)
    funext i; obtain ⟨(i|i),rfl⟩ := (sorted A F (G:=G) (x:=x)).surjective i <;> rw [Pi.add_apply,widen_at, widen_at, widen_at]
    · rfl
    exact zero_add _
  unfold bill; rw [hm,product_D]; rfl
end Padded
end YM.PhysicalNext.OrderedAffine2B.Footprint
