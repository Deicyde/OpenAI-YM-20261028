import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.ColumnL


/-!
 Adapted (necessary new cross-Forest support) from accepted E6 Lodge.
# Endpoints in one Tuft matrix window, logs
Spatial dependencies at numerical o. No inverse column leakage in L^−1 (only at
principal windows). Use gliding powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {x : Site c} {X : Coat T F} {X' : Coat T F'} {a : ℕ} {η r Q Y : ℝ}


namespace Tuft
variable (h : Tuft X X' x a) (p : Room P S T X.x) (q : Tubular f G) (he : x=along S q)
include h he p

lemma inverse_w (i : Tubular f G) (ha : 15*X.B ≤ a) (s : ℝ) :
    X.shutter.pad (glide X.plate s) i q=X'.shutter.pad (glide X'.plate s) i q := by
  have hk := h.B
  -- shutter dependent
  unfold shutter; rw [hk]
  let D:= X.shutter; let Y := D.take q
  by_cases hi : i∈Y
  swap; · rw [D.outside _ i q hi,D.outside _ i q hi]
  rw [D.inside (glide X.plate s) q ⟨i,hi⟩, D.inside (glide X'.plate s) q ⟨i,hi⟩];
  suffices hf : D.principal (glide X.plate s) q=D.principal (glide X'.plate s) q by rw [hf]
  ext u v
  have ht : separation x (along S u.val)≤X.B+2 := by rw [he,separation_comm]; exact D.high _ q u.property
  have hZ := (h.tune_down (q:=along S u.val) (b:=13*X.B) (by have hz : 100 ≤ X.B := p.sight.1; omega)).plateL p
    u.val rfl (le_refl _) v.val
  change glide X.plate s u.val v.val=glide X'.plate s u.val v.val
  unfold glide; simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,hZ]

lemma changeL (i : Tubular f G) (ha : 15*X.B ≤ a) : X.kernelA i q=X'.kernelA i q := by
  unfold kernelA; nth_rw 1 [← glide_end X.plate]; nth_rw 1 [← glide_end X'.plate]; exact h.inverse_w p q he i ha 1

lemma cL (i : Tubular f G) (ha : 17*X.B ≤ a) : X.relating i q=X'.relating i q := by
  have hx := h.changeL p q he i (by omega)
  have hk : X.kernelA q i=X'.kernelA q i := by
    by_cases hi : separation x (along S i) ≤ X.B+2
    · exact (h.tune_down (q:=along S i) (b:=15*X.B) (by have hv : 100 ≤ X.B := p.sight.1; omega)).changeL p i rfl q le_rfl
    rw [he] at hi
    unfold kernelA; rw [X.shutter.thin _ q i (lt_of_not_ge hi), X'.shutter.thin _ q i (by rw [h.B]; exact lt_of_not_ge hi)]
  unfold relating frameMean; simp only [Matrix.smul_apply,Matrix.transpose_apply,Matrix.add_apply]
  unfold kernelA at hx hk; rw [hx,hk]

lemma driftL (ha : 17*X.B ≤ a) : X.driftM q=X'.driftM q := by
  unfold driftM; rw [Pi.neg_apply,Pi.neg_apply]; apply congr_arg Neg.neg
  unfold Matrix.mulVec dotProduct; refine sum_congr rfl fun i _ => ?_; dsimp only; rw [Matrix.transpose_apply,Matrix.transpose_apply,← h.changeL p q he i (by omega)]
  by_cases hi : separation x (along S i) ≤ X.B+2
  · have hF : 100≤X.B := p.sight.1
    rw [(h.tune_down (q:=along S i) (b:=13*X.B) (by omega)).billL p i rfl le_rfl]
  rw [he,separation_comm] at hi; rw [kernelA,X.shutter.thin _ i q (lt_of_not_ge hi),zero_mul,zero_mul]

lemma scrapsL (ha : 17*X.B ≤ a) (i : Tubular f G) : X.shreds i q=X'.shreds i q := by
  unfold shreds flawed; rw [Matrix.sub_apply,Matrix.sub_apply]; apply congrArg₂ (·-·) _ rfl
  rw [Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro j _
  change _*X.relating j q=_*X'.relating j q; rw [← h.cL p q he j ha]
  by_cases hj : separation x (along S j) ≤ X.B+2
  · have hF : 100≤X.B := p.sight.1
    have hi' := (h.tune_down (q:=along S j) (b:=13*X.B) (by omega)).plateL p j rfl le_rfl i
    have ht {F : Forest S.ratio} (X : Coat T F) : X.plate i j=X.plate j i := by nth_rw 2 [← X.toned]; rfl
    rw [ht X,hi',ht X']
  rw [he,separation_comm] at hj; rw [relating,X.shutter.width X.plate j q (lt_of_not_ge hj),mul_zero,mul_zero]

lemma glideL (ha : 17*X.B ≤ a) (i : Tubular f G) (s : ℝ) :
    X.shutter.error (glide X.plate s) i q=X'.shutter.error (glide X'.plate s) i q := by
  unfold Window.error; rw [Matrix.sub_apply,Matrix.sub_apply]; apply congrArg₂ (·-·) _ rfl
  rw [Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro j _
  rw [← h.inverse_w p q he j (by omega) s]; by_cases hj : separation x (along S j) ≤ X.B+2
  · have hF : 100≤X.B := p.sight.1
    have hi' := (h.tune_down (q:=along S j) (b:=13*X.B) (by omega)).plateL p j rfl le_rfl i
    unfold glide; simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply]
    rw [show X.plate i j=X.plate j i from congr_fun (congr_fun X.toned j) i,hi',← show X'.plate i j=X'.plate j i from congr_fun (congr_fun X'.toned j) i]
  rw [he,separation_comm] at hj; rw [X.shutter.thin _ j q (lt_of_not_ge hj),mul_zero,mul_zero]

lemma joints (ha : 17*X.B≤a) : Pulse.Batch.joint X.plate X.shutter q.1=Pulse.Batch.joint X'.plate X'.shutter q.1 := by
  have hz j (s) : intensity X.shutter X.plate s 0 (q.1,j) (q.1,j)=intensity X'.shutter X'.plate s 0 (q.1,j) (q.1,j) := by
    unfold intensity; rw [pow_zero,pow_zero,mul_one,mul_one,Matrix.mul_apply,Matrix.mul_apply]; refine sum_congr rfl fun v _=> ?_
    simp only [Matrix.sub_apply]; rw [h.plateL p (q.1,j) he (by omega), h.inverse_w p (q.1,j) he v (by omega)]
  have ht : Pulse.Batch.joint X.plate X.shutter q.1=Pulse.Batch.joint X'.plate X'.shutter q.1 := by
    unfold Pulse.Batch.joint localBase lact; simp_rw [hz]
  exact ht
lemma condensates (ha : 17*X.B≤a) : X.condensation q.1=X'.condensation q.1 := by
  unfold condensation
  rw [h.joints p q he ha,show Pulse.Batch.joint X.blank.plate X.shutter q.1=Pulse.Batch.joint X'.blank.plate X'.shutter q.1 from h.blanked.joints p q he ha]

end Tuft
end YM.ConnectedActivityE6
