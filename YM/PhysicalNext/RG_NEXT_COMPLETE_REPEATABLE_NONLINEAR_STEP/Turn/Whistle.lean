import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Pollen

/-! # Color-trace and work-path calls, with actual ordered book tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory Matrix
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
open ConnectedActivityE6 Shell Coat SliceRows Pulse Itinerary Control Window
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open OrderedAffine2B.SymWhole
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (s : Signed) (b : Site c) (V : Config G c)

def sequence (e : Equiv.Perm (Bond f)) : (n : ℕ) → Equiv.Perm (Itinerary f n)
  | 0 => Equiv.refl _
  | k+1 => ((Itinerary.chart f k).trans (e.prodCongr (sequence e k))).trans (Itinerary.chart f k).symm

lemma proceed (e : Equiv.Perm (Bond f)) (i : Bond f) {n : ℕ} (p : Itinerary f n) : arrive (e i) (sequence e n p)=e (arrive i p) := by
  induction n generalizing i with
  | zero => simp [arrive]
  | succ n ih => rw [arrive,arrive]; exact ih _ (Itinerary.after p)

lemma yarn (O : ColorOrtho G (Bond f)) (e : Equiv.Perm (Bond f)) (M : Mat f G) (i j : Bond f) :
    Itinerary.restrict (warp O e M) i j= (asMatrix O i * Itinerary.restrict M (e i) (e j)) * (asMatrix O j).transpose := by
  ext a b; change Orthogonal.warp _ _ _ (i,a) (j,b)=_; unfold Orthogonal.warp; rw [dressed_apply,Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]; rfl

lemma thrust (O : ColorOrtho G (Bond f)) (e : Equiv.Perm (Bond f)) {n : ℕ} (p : Itinerary f n) (M P : ℕ→Mat f G)
    (h : ∀ i<n, P i=warp O e (M i)) (i : Bond f) :
    combo i p P= (asMatrix O i*combo (e i) (sequence e n p) M) * (asMatrix O (arrive i p)).transpose := by
  induction n generalizing i P M with
  | zero => rw [arrive,combo,combo,mul_one]; exact (mul_eq_one_comm.mp (matrix_orth O i)).symm
  | succ k ih =>
    rw [combo,combo, h 0 (by omega), yarn,arrive]
    let p':=Itinerary.next p
    change _ * _= (_ * (restrict _ _ (e p') * combo (e p') (sequence _ k (Itinerary.after p)) _)) * _
    rw [ih (Itinerary.after p) _ _ (fun a ha=>h (a+1) (by omega))]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (_ᵀ) _ (combo _ _ _ * _), matrix_orth O, Matrix.one_mul]

lemma stamped (O : ColorOrtho G (Bond f)) (e : Equiv.Perm (Bond f)) {n : ℕ} (p : Itinerary f n) (M P : ℝ→ℕ→Mat f G)
    (h : ∀ t i, i<n → P t i=warp O e (M t i)) (i : Bond f)
    (hx : ∀ i,i<n→ ContinuousOn (fun t=> P t i) (Set.uIcc 0 1)) (hz : ∀ i,i<n→ ContinuousOn (fun t=> M t i) (Set.uIcc 0 1)) :
    stamp P i p = stamp M (e i) (sequence e n p) := by
  by_cases he : arrive i p=i
  swap; · simp only [stamp,checkIn,proceed,Equiv.apply_eq_iff_eq]; simp [he]
  have ht (i) (p:Itinerary f n) (hp : arrive i p=i) (M : ℝ→ℕ→Mat f G) (hh : ∀ i,i<n→ ContinuousOn (fun t=> M t i) (Set.uIcc 0 1)) :
      stamp M i p=∫ t in (0:ℝ)..1, Matrix.trace (combo i p (M t)) := by
    unfold stamp checkIn; simp only [hp,↓reduceIte]
    have hf j : IntervalIntegrable (fun t => combo i p (M t) j j) volume 0 1 :=
      (continuousOn_pi.mp (continuousOn_pi.mp (combo_continuous i p M _ hh) j) j).intervalIntegrable
    exact (intervalIntegral.integral_finsetSum (fun j _=> hf j)).symm
  rw [ht i p he P hx,ht _ _ (by rw [proceed,he]) M hz]; apply intervalIntegral.integral_congr; intro t _
  dsimp only; rw [thrust O e p _ _ (h t),he,Matrix.trace_mul_comm,← Matrix.mul_assoc (_ᵀ),matrix_orth O, Matrix.one_mul]

def portage (s : Signed) (b : Site c) (S : StepData c f) (n) : Equiv.Perm (Ledger f n) := Equiv.sigmaCongrRight fun _ =>
  Equiv.prodCongr (diagram s b S) (sequence (diagram s b S) _)

lemma spray_glide (Q : Mat f G) (t : ℝ) : Window.glide (Spray s b V S Q) t=Spray s b V S (Window.glide Q t) := by
  unfold Spray Window.glide; rw [weave_add,weave_one,weave_scale,weave_sub,weave_one]
lemma spray_neg (Q : Mat f G) : Spray s b V S (-Q)= -Spray s b V S Q := by simpa using! weave_scale (diagram s b S) (fiber s b V S) Q (-1)

namespace Parked
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {s b} {X : Coat T F} {Y : Coat T (Locations.forest s b F)} (h : Parked s b X Y) (hp : P.Funds S T)
include h hp
lemma powers (t : ℝ) :
    (∀ j, aSeq Y.shutter Y.plate t j= Spray s b X.V S (aSeq X.shutter X.plate t j)) ∧
    ∀ j, sSeq Y.shutter Y.plate t j= Spray s b X.V S (sSeq X.shutter X.plate t j) := by
  have he:= h.coherent hp
  refine ⟨fun i=> ?_, fun i=>?_⟩
  · match i with
    | 0 => unfold aSeq Spray; rw [weave_sub,weave_one,he]
    | 1 => unfold aSeq shutter; rw [h.aligned.2.1, he,spray_glide,panelpad]
    | _+2 =>
      simp only [aSeq,shutter,he,spray_glide,spray_neg]
      unfold Window.error; rw [panelpad,h.aligned.2.1]; unfold Spray; rw [weave_sub,weave_one,weave_times]
  cases i
  · exact h.shuts hp
  next i =>
    change -(t • Y.shreds)=Spray s b X.V S (-(t • X.shreds)); rw [h.shuts hp,spray_neg]; unfold Spray; rw [weave_scale]

variable {η r Q Y' : ℝ} {L : Side}
    (hx : Rotator P L η r Q Y' X) (hy : Rotator P L η r Q Y' Y)
include hx hy
lemma transported_A (p : Ledger f 3) : ArmA Y.shutter Y.plate p= ArmA X.shutter X.plate (portage s b S 3 p) := by
  have hv (B) (M : Mat f G) (h : Allow M (Census.along S) (Census.tubularPrice G L) η r Q) (i : ℕ) : ContinuousOn
      (fun t=> aSeq (Coat.frames G S B) M t i) (Set.uIcc (0:ℝ) 1) := by
    match i with
    | 0=> exact continuousOn_const
    | 1=> exact vibrate _ _ h hx.full
    | _+2 => exact ContinuousOn.neg (ContinuousOn.sub ((strung M).continuousOn.mul (vibrate _ _ h hx.full)) continuousOn_const)
  exact stamped (fiber s b X.V S) (diagram s b S) p.2.2 (aSeq X.shutter X.plate) _ (fun t i _=> (h.powers hp t).1 i) p.2.1 (fun i _=> hv _ _ hy.scale i) (fun i _=> hv _ _ hx.scale i)

omit hx hy in
lemma transported_S (p : Ledger f 1) : ArmS Y.shutter Y.plate p=ArmS X.shutter X.plate (portage s b S 1 p) := by
  have hh (B) (M : Mat f G) (i : ℕ) : ContinuousOn (fun t=> sSeq (Coat.frames G S B) M t i) (Set.uIcc (0:ℝ) 1) := by
    cases i
    · exact continuousOn_const
    exact ContinuousOn.neg (continuousOn_id.smul continuousOn_const)
  exact stamped (fiber s b X.V S) (diagram s b S) p.2.2 (sSeq X.shutter X.plate) _ (fun t i _=> (h.powers hp t).2 i) p.2.1 (fun i _=> hh _ _ i) (fun i _=> hh _ _ i)

lemma transported_j (i : Bond f) : Batch.joint Y.plate Y.shutter i= Batch.joint X.plate X.shutter (diagram s b S i) := by
  rw [Batch.joint_coil _ Y.shutter hy.scale hy.full, Batch.joint_coil _ X.shutter hx.scale hx.full]; apply intervalIntegral.integral_congr; intro t _
  have hp : intensity Y.shutter Y.plate t 0=Spray s b X.V S (intensity X.shutter X.plate t 0) := by
    rw [← product_a, ← product_a]; simp only [Pulse.Itinerary.product,Matrix.mul_one]; rw [(h.powers hp t).1,(h.powers hp t).1]; exact (weave_times ..).symm
  dsimp only; rw [hp]; let O:= asMatrix (fiber s b X.V S) i
  change Matrix.trace (restrict (Spray _ _ _ _ _) i i)=Matrix.trace (restrict (intensity X.shutter X.plate t 0) _ _)
  unfold Spray; rw [yarn,Matrix.trace_mul_comm, ← Matrix.mul_assoc (_ᵀ), matrix_orth,Matrix.one_mul]
end Parked
end YM.PhysicalNext.Repeat.Turn
