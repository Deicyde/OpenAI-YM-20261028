import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.AnalyticBridge.RESET_INCOME_PORT.Plate
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Builder
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Balance
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.Rays
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.JOINT_CALENDAR.Branches
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Breadth
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.Shuffles
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Orbits
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current


set_option warningAsError false
set_option autoImplicit false

/-!
# Freeze and open the exact physical sector at the Scanner interface

Endpoint distance convention and positive common coordinates of SectorChange. The chart
requirement is only at *correct flags*, nonzero bill, living shared tag. But Opened must
hold for all fields, and for test functions of the whole actual slice. Frozen mass is
not replaced by a log or a background. Broad profiles used on the intact allocation.
-/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix
open RG Wilson Lattice Pressure Pressure.Stores Bid Precision Tree Push.SectorMeasure
  Next.SectorChange Further GaussianScalar AnalyticBridge.ResetIncome
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (e : Plate G S) (A : Stores S)

def held : Finset e.forest.Free := Finset.univ.filter (chill A e.x e.forest)
lemma held_iff (i : e.forest.Free) : i ∈ held e A ↔ chill A e.x e.forest i := Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

def heldEquiv : (↥(held e A)) ≃ Next.SectorChange.Frozen A e.x e.forest :=
  Equiv.subtypeEquiv (Equiv.refl _) (held_iff e A)

def going : GaussianScalar.Standing (held e A) ≃ Active A e.x e.forest :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun i => not_congr (held_iff e A i))

def moving : Bits G (held e A) ≃ Rows.In e.x A e.forest (G:=G) := Equiv.prodCongr (going e A) (Equiv.refl _)

def shellMap : GaussianScalar.Frozen (held e A) G ≃ᵐ LinkArray G (Next.SectorChange.Frozen A e.x e.forest) :=
  MeasurableEquiv.piCongrLeft (fun _ => G.El) (heldEquiv e A)

def chartMap : VV (Bits G (held e A)) ≃ᵐ Prices G (Active A e.x e.forest) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (moving e A)

lemma shell_paid : MeasurePreserving (shellMap e A) (bins (held e A) G) (piHaar G (Next.SectorChange.Frozen A e.x e.forest)) :=
  measurePreserving_piCongrLeft (fun _ => G.probHaar) (heldEquiv e A)

lemma chart_paid : MeasurePreserving (chartMap e A) volume volume := volume_measurePreserving_piCongrLeft (fun _ => ℝ) (moving e A)

lemma shell_reads (Y : GaussianScalar.Frozen (held e A) G) (i : ↥(held e A)) : shellMap e A Y (heldEquiv e A i) = Y i :=
  MeasurableEquiv.piCongrLeft_apply_apply ..
lemma chart_reads (z : VV (Bits G (held e A))) (i : Bits G (held e A)) : chartMap e A z (moving e A i) = z i :=
  MeasurableEquiv.piCongrLeft_apply_apply ..
lemma chart_ap (z : VV (Bits G (held e A))) : chartMap e A z = z ∘ (moving e A).symm := by
  funext i; obtain ⟨i,rfl⟩ := (moving e A).surjective i; rw [chart_reads]; simp
lemma chart_sym (a : Prices G (Active A e.x e.forest)) : (chartMap e A).symm a = a ∘ moving e A := by
  apply (chartMap e A).injective; rw [chart_ap _ _ (a ∘ _), MeasurableEquiv.apply_symm_apply]; funext i; exact (congr_arg a ((moving e A).apply_symm_apply i)).symm


lemma tape_reads (z : VV (Bits G (held e A))) (i : GaussianScalar.Standing (held e A)) :
    tape (chartMap e A z) (going e A i) = hue i z := by
  ext j; exact chart_reads e A z (i,j)

lemma included_eq (V : Config G c) (Y : GaussianScalar.Frozen (held e A) G) (z : VV (Bits G (held e A))) :
    included V Y z = returned A e.forest V (shellMap e A Y) (tape (chartMap e A z)) := by
  funext i; unfold included returned thaw
  split
  next hi =>
    change _ = freeze _ _ _ _ (heldEquiv e A ⟨i,hi⟩).val
    rw [freeze_held,shell_reads]
  next hi =>
    change _ = freeze _ _ _ _ (going e A ⟨i,hi⟩).val
    rw [freeze_regular]; unfold release; rw [tape_reads]; rfl

/-- Only the two radius facts needed to form a legit Curtain. -/
structure Doors (e : Plate G S) : Prop where
  pos : 0 < e.d
  radius : 2*e.d < e.chart.radius

def cover (h : Doors e) : Curtain e.chart (held e A) where
  size := 2*e.d
  pos := mul_nonneg (by norm_num) h.pos.le
  small := h.radius
  read _ := Next.SectorChange.broad e.chip e.d
  borel _ := (broad_smooth e.chip e.d).continuous.measurable
  nonneg _ a := (broad_range e.chip a e.d).1
  top _ a := (broad_range e.chip a e.d).2
  off _ a hx := not_not.mp (fun ha => (broad_span e.chip h.pos a ha).not_gt hx)

lemma leaf_match (h : Doors e) (z : VV (Bits G (held e A))) :
    leafPrice e.chart (cover e A h) z = let y := tape (chartMap e A z)
      doors e.chip e.d y * pay e.chart y := by
  rw [leafPrice,Finset.prod_mul_distrib]; unfold doors pay
  simp_rw [← Equiv.prod_comp (going e A), tape_reads]; rfl



private lemma strip_price (h : Doors e) (hZ : LocalRatio e.chart)
    (k : S.Choices) (V : Config G c) (hA : Next.SectorChange.Standing (A:=A) (F:=e.forest) e.book e.chart e.d k V)
    (L : e.forest.Slice G → ℝ) (Y : GaussianScalar.Frozen (held e A) G) (z : VV (Bits G (held e A))) :
    let p := shellMap e A Y; let a := tape (chartMap e A z); let u := returned A e.forest V p
    (mouth e.chart).indicator (fun a => pay e.chart a • (raw e.book A k V (u a)*L (u a))) a =
      coupon e.chart (cover e A h) e.book A k V L Y z := by
  intro p a u
  rw [coupon,leaf_match,included_eq]; dsimp only
  change _ = doors e.chip e.d a * pay e.chart a * (raw _ _ _ _ (u a)*L (u a))
  by_cases he : a ∈ mouth e.chart
  swap
  · rw [indicator_of_notMem he]
    rw [show doors e.chip e.d a=0 from not_not.mp (fun hh => he (protected_pay _ hZ h.pos h.radius hh).1),zero_mul,zero_mul]
  rw [indicator_of_mem he]; by_cases hx : raw e.book A k V (u a)=0
  · rw [hx,zero_mul,smul_zero,mul_zero]
  have hb := left_ne_zero_of_mul hx
  have ht : Alive S (e.forest.drape (u a)) k := by
    by_contra hp; unfold raw SectorNext.Vacuum.broad at hx; rw [dead hp,mul_zero,mul_zero] at hx; contradiction
  have hg (i : Active A e.x e.forest) : ‖a i‖ ≤ e.d := by
    obtain ⟨w,hw,hs,hj⟩ := hA _ hb ht i
    unfold u returned thaw at hj; rw [freeze_regular] at hj
    exact hZ.inject hs (he _ (mem_univ _)) (mul_right_cancel hj) ▸ hw
  rw [show doors e.chip e.d a=1 by unfold doors; simp_rw [broad_one _ h.pos (hg _),Finset.prod_const_one],one_mul, smul_eq_mul]

/-- All configurations. Uses only correct-flag chart receipts but proves the (wrong) flag
branches zero by the actual bill predicate. Apply with e.g. `committed` / `purchased`. -/
theorem opened (h : Doors e) (hZ : LocalRatio e.chart) (hm : S.patch.Branches S.kernel G)
    (k : S.Choices) (V : Config G c) (H : e.matched A V → Next.SectorChange.Standing (A:=A) (F:=e.forest) e.book e.chart e.d k V) :
    Opened e.chart (cover e A h) e.book A k V := by
  intro L hL
  let u (x : e.forest.Slice G) := raw e.book A k V x * L x
  have hw : Next.SectorChange.Standing (A:=A) (F:=e.forest) e.book e.chart e.d k V := by
    intro a ha hp; apply H _ a ha hp; exact (e.book.actual _ _ _ _ ha).exactFlags
  have hb (x) (hx : u x≠0) : e.book.bill A k (e.forest.drape x) V ≠ 0 ∧ Alive S (e.forest.drape x) k := by
    unfold u raw SectorNext.Vacuum.broad at hx
    refine ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hx),?_⟩
    by_contra h; simp [dead h] at hx
  obtain ⟨hg,C,hC⟩ := (raw_env e.book A k V (F:=e.forest) hm).mul hL
  have ht := thaw_integral e.forest (chill A e.x e.forest) hZ (replica S.ratio V) u hg.stronglyMeasurable C hC
    (fun x hx i => by obtain ⟨w,-,he,hx⟩ := hw _ (hb x hx).1 (hb x hx).2 i; exact ⟨_,⟨_,he,rfl⟩,hx⟩) |>.2.2.2
  change (∫ x, u x ∂_) = _; rw [ht, ← (shell_paid e A).integral_comp']
  refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
  dsimp only
  rw [← (tape_volume (G:=G) (ι:=Active A e.x e.forest)).integral_comp', ← (chart_paid e A).integral_comp']
  exact integral_congr_ae (Eventually.of_forall fun z => strip_price e A h hZ k V hw L Y z)

end YM.SectorTools.ActualScalar
