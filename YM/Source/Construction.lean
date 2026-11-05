import YM.Source.Preservation

/-!
# Single Wilson family, its primary cylinders

For each weight the levels `ref d` are fixed before any limits. For
convenience give transfers at all cutoffs (using e.g. zero or trivial padding
when the ref test doesn't fit). Soundness is demanded only down to the
fixed fitting levels; we concretize 'sufficiently fine' by allowing to
choose references sufficiently deep then asking whenever `ref d ≤ N`.
See . This supplies physical support O(a_N)
even though subsequent estimates may proceed via very different scales.
E outputs specialized to our choices of masks/paths/numerical gates; no
claim such a trajectory exists yet.
-/

set_option autoImplicit false
noncomputable section
namespace YM

open MeasureTheory RG Lattice Source Wilson Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators

structure Family (G : Gauge) where
  path : History G
  params : Hol G
  labels : Frames G
  localSection (d : ℕ) : SectionData (labels.level d)
  ref : ℕ → ℕ
  factory (d N p : ℕ) : TransferData (labels.level d) path N p

namespace Family
variable {G : Gauge} (C : Family G)
abbrev S := C.path.levels.S
abbrev side := C.S.side
abbrev label (d : ℕ) := (C.labels.level d).Coeff
abbrev refUnit (d : ℕ) := Source.unitVec (C.labels.level d) C.path (C.ref d)
abbrev beta (N p) := C.path.β N p N

def omega (N p) (F : Config G (C.side N p) → ℂ) := moment (C.beta N p) F

def O (N p) {d : ℕ} (v : C.label d) := (C.factory d N p).cylinder (C.localSection d) v

structure Makes : Prop where
  wilson : C.path.Selected
  sections (d : ℕ) : (C.localSection d).Sound C.params
  stages (d : ℕ) :
    d+3 ≤ C.path.levels.clock.J (C.ref d) ∧
    ∀ m, C.ref d ≤ m → d+1 ≤ (C.path.levels.params m).order ∧ d ≤ (C.path.levels.params m).power
  places (d N p : ℕ) : C.ref d ≤ N → ∀ x ∈ (C.localSection d).stencil,
    ∀ i : Axis, 20*((x i).natAbs + 1) ≤ (C.side N p).val
  /-- Section actually gives canonical mask test-size (cf eq:psect).
  Charge this constant before L. -/
  priced (d N p : ℕ) : C.ref d ≤ N →
    let P := C.path.levels.budget N
    let F := C.labels.level d
    let D := C.localSection d
    ∀ o : Site (C.side N p), ∀ i : F.Index,
      P.Regular (D.footprint o) (D.places (Pi.single i 1) o) ∧
      P.supBounds o (D.footprint o) (D.places (Pi.single i 1) o) ((C.path.levels.params N).columns *
        P.threshold^(F.grades i).2)
  calibrated (d N p : ℕ) : C.ref d ≤ N → (C.factory d N p).Based C.params (C.localSection d) (C.ref d)

/-- The normalized readout, not the actual value of a coarse field. -/
theorem normalized {N p d} (h : C.Makes) (hw : C.ref d ≤ N) (v : C.label d) :
    let M := C.factory d N p
    (M.entries (C.ref d) (M.terminal.symm v)).x = v := by
  intro M; rw [(show M.Based _ _ _ from h.calibrated d N p hw).reads, LinearEquiv.apply_symm_apply]

/-- Literal, no retuning at shifted anchors. -/
theorem translation {N p d} (o b : Site (C.side N p)) (v : C.label d) U : C.O N p v o (Lattice.translate b U) =
    C.O N p v (o+b) U := ((C.factory d N p).cylinder_shift _ v o b U).symm

theorem reality {N p d} (h : C.Makes) (hv : C.ref d ≤ N) (x : C.label d) o U :
    C.O N p (star x) o U = star (C.O N p x o U) := by
  unfold O TransferData.cylinder initial
  let T := C.factory d N p
  let S := C.localSection d
  let F := C.labels.level d
  have hb := show T.Based _ S _ from h.calibrated _ _ p hv
  rw [show (C.factory d N p).terminal.symm (star x) = star (T.terminal.symm x) by
    apply T.terminal.injective; rw [hb.realForm, LinearEquiv.apply_symm_apply T.terminal x]; exact T.terminal.apply_symm_apply _]
  have hs (t) (z : C.label d) : F.scaled (t : ℝ) (star z) = star (F.scaled t z) := by
    funext i; simp [mul_comm]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, SectionData.places, (h.sections d).ordinary_real]; simp [F,T]

theorem rotated {N p d} (h : C.Makes) (hv : C.ref d ≤ N) (x : C.label d) (s : Signed) (o b U) :
    C.O N p ((C.labels.level d).act s.ortho x) (affine s b o) U = C.O N p x o (pull s b U) := by
  unfold O TransferData.cylinder initial
  let T := C.factory d N p
  let Q := C.localSection d
  let F := C.labels.level d
  have hb := show T.Based _ Q _ from h.calibrated _ _ p hv
  rw [show T.terminal.symm (F.act s.ortho x) = F.act s.ortho (T.terminal.symm x) by
    apply T.terminal.injective
    rw [hb.orients, LinearEquiv.apply_symm_apply T.terminal x]; exact T.terminal.apply_symm_apply _]
  simp only [T,F,Pi.smul_apply, Frame.scaling, SectionData.placed_signed (C.localSection d) (h.sections d)]

theorem constant {N p} (h : C.Makes) (d : ℕ) (hv : C.ref d ≤ N) (o : Site (C.side N p)) :
    C.O N p (C.refUnit d) o = 1 :=
  (C.factory d N p).origin_unit (h.sections d) _ (h.calibrated _ _ _ hv) o

theorem invariant (h : C.Makes) (N p d : ℕ) (v : C.label d) o : GaugeInvariant (C.O N p v o) := by
  intro t U
  simp only [O, TransferData.cylinder, initial, Pi.smul_apply]
  rw [(C.localSection d).placed_invariant (h.sections d) o _]

theorem localO (N p d : ℕ) (v : C.label d) o : LocalOn ((C.localSection d).footprint o) (C.O N p v o) := by
  intro U V hh
  simp only [O,TransferData.cylinder,initial,Pi.smul_apply]
  rw [((C.localSection d).placed_local o _) U V hh]

theorem continuousO (N p d : ℕ) (v : C.label d) o : Continuous (C.O N p v o) :=
  (C.factory d N p).cylinder_cont _ _ _

theorem linearO (N p d : ℕ) (o : Site (C.side N p)) :
    IsLinearMap ℂ (fun (v : C.label d) => C.O N p v o) := by
  let h := (C.localSection d).eval_linear
  simp only [O,TransferData.cylinder,initial]
  constructor
  · intro x y
    funext U
    simp [SectionData.places, h.map_add, mul_add]
  intro q v
  funext U
  simp only [map_smul,SectionData.places, h.map_smul, Pi.smul_apply]; rw [smul_comm q]
end Family
end YM
