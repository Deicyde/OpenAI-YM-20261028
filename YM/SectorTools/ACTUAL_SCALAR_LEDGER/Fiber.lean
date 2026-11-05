import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Charts


set_option warningAsError false
set_option autoImplicit false
set_option synthInstance.maxSize 1024

/-!
# The four physical arrays and the blank-sector comparator

Keep the same true path cut, channel and counting orders (`Rows.move`, `Native.ground_gram`).
Never identify the cost after cutoff with the untruncated metric. The default for
matrix *pricing* (since Scanner requires all configurations even there) at mismatched
flags is the construction on this exact geometry and tag with predictor input field one,
**not** used to evaluate the physical reads or chart on the draped field (the bill is
identically zero there). Also give the everywhere-defined literal formula. `fieldLaw`
agrees with `Gaussian.cloud` in the relabeled coordinates (even with Mathlib's defaults);
no need to change from/to Lebesgue at a singular or indefinite Gaussian at the illegal flags.
-/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix
open RG Wilson Lattice Pressure Pressure.Stores Precision Tree Push.SectorMeasure
  Next.SectorChange Further GaussianScalar AnalyticBridge.ResetIncome
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (e : Plate G S) (h : Doors e) (A : Stores S)
    (k : S.Choices) (V : Config G c)

/-- Literal four inputs of SectorChange (cols relabeled, original row order). -/
abbrev page : Fiber e.forest e.chart (Rows.Receipt G S) where
  H := held e A
  veil := cover e A h
  D _ := (Rows.move e.tube e.x V k (shots S e.x) A e.forest).submatrix id (moving e A)
  b0 Y := Rows.source e.tube e.x V k (shots S e.x) A e.forest e.chip e.d (shellMap e A Y)
  C _ := (e.Cov A V k).submatrix (moving e A) (moving e A)
  μ Y := (chartMap e A).symm (e.center A V k (shellMap e A Y))

def supported := if e.matched A V then V else 1

abbrev sheets := page e h A k (supported e A V)
lemma opens_at_match (hm : e.matched A V) : sheets e h A k V=page e h A k V := by simp [sheets,supported,hm]

variable (Y : GaussianScalar.Frozen (held e A) G) (z : VV (Bits G (held e A)))

lemma moves : let u := page e h A k V
    u.D Y *ᵥ z = Rows.move e.tube e.x V k (shots S e.x) A e.forest *ᵥ chartMap e A z := by
  change Matrix.submatrix (Rows.move e.tube e.x V k (shots S e.x) A e.forest) id (moving e A) *ᵥ _ = _
  rw [submatrix_mulVec_equiv,chart_ap]; rfl
lemma prec_eq : precision ((page e h A k V).D Y) = (e.Gram A V k).submatrix (moving e A) (moving e A) := by
  let D := Rows.move e.tube e.x V k (shots S e.x) A e.forest
  change D.transpose.submatrix (moving e A) id * D.submatrix id (moving e A) = _
  exact Matrix.submatrix_mul_equiv _ _ (moving e A) (Equiv.refl (Rows.Receipt G S)) (moving e A)
lemma sigma_eq : (page e h A k V).sigma Y = filled (held e A) ((e.Gram A V k).submatrix (moving e A) (moving e A)) := by
  rw [Fiber.sigma,prec_eq]
lemma linear_eq : let u := page e h A k V
    linearCost (u.D Y) (u.b0 Y) = Rows.blame e.tube e.x V k (shots S e.x) A e.forest e.chip e.d (shellMap e A Y) ∘ moving e A := rfl







lemma eps_price : let u := page e h A k V; let Q := e.Gram A V k; let H := e.Cov A V k
    (u.sigma Y).det = Q.det ∧ (u.complete Y).det = H.det ∧ (1+u.eps Y).det = (1+(Q*H-1)).det := by
  intro u Q H
  have ht : (u.sigma Y).det = Q.det := by unfold u; rw [sigma_eq,paid_filled,Matrix.det_submatrix_equiv_self]
  have hr : (u.complete Y).det = H.det := by
    change Matrix.det (filled (held e A) (H.submatrix (moving e A) (moving e A))) = _
    rw [paid_filled,Matrix.det_submatrix_equiv_self]
  refine ⟨ht,hr,?_⟩; unfold Fiber.eps; rw [show 1+(u.sigma Y*u.complete Y-1)=u.sigma Y*u.complete Y by abel,
    show 1+(Q*H-1)=Q*H by abel,Matrix.det_mul,Matrix.det_mul,ht,hr]

/-- A-flat from V≡1 with empty Σ on this exact tree and allocation/four arrays;
proof irrelevant in h. No determinant-only assertion. -/
def noHole : Stores S := ⟨∅,∅,∅⟩
lemma clear (i : e.forest.Free) : i ∉ held e noHole := by
  rw [held_iff]; simp [chill,Stores.dome,Stores.place,halo_spec,noHole]

def benchmark := (page e h noHole e.tag 1).sigma 1
lemma flat_price_eq (hm : S.patch.Branches S.kernel G) : benchmark e h=e.Flat := by
  rw [benchmark,sigma_eq, Plate.Flat, ← Native.ground_gram e.tube e.forest e.tag e.x hm]
  ext i j
  let x (i : Key e.forest G) : Bits G (held e noHole) := (⟨i.1, clear _ _⟩,i.2)
  let C := (e.Gram noHole 1 e.tag).submatrix (moving e noHole) (moving e noHole)
  exact congr_fun (congr_fun (sortBits _ C 1) (.inl (x i))) (.inl (x j))








end YM.SectorTools.ActualScalar
