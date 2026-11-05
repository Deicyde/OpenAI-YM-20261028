import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.SOURCE_HISTORIES.Motion
import YM.Next.EXTRACTION.Base

/-!
# Chart at the fixed intermediate m. Don't project the wrong insertion.

`window` is from the **reference** normalization (includes inverse terminal
T) to the actual readout at LEVEL m in the same history. Applied only with
`C.ref d ≤ m ≤ N` (other values are totalization to identity). 
`ᵍ_m,N,R` matrix. `paper`-in-coordinates relations and integrated
physical formula below. These don't yet require choosing limits. All
here conditional on the Family,Makes — thus becomes available after Issue
on exactly its Printed family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Charts
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G) (h : C.Makes)

abbrev Exchange (d : ℕ) := C.label d ≃L[ℂ] C.label d

variable (d N p m : ℕ)
include h

private theorem isomorphism (hr : C.ref d ≤ m) (hm : m ≤ N) : ∃ t : Exchange C d, ∀ x,
    t x = ((C.factory d N p).entries m ((C.factory d N p).terminal.symm x)).x := by
  let F := C.labels.level d
  let T := C.factory d N p
  have ht : T.Based _ _ _ := h.calibrated d N p (hr.trans hm)
  let A := IsLinearMap.mk' (fun v => (T.entries m v).x) (ht.linear m hr hm).1
  have he : Injective A := by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr fun x hx => ?_
    have hh (i : ℕ) (hb : m ≤ i) (hu : i≤N) : (T.entries i x).x=0 := by
      induction i,hb using Nat.le_induction with
      | base => exact hx
      | succ i hI IH =>
        have he := ht.back i (hr.trans hI) hu x
        rw [IH (i.le_succ.trans hu)] at he
        exact Work.G08.size_separates F _ (by simpa [Frame.coeffSize] using he)
    exact (ht.bare_coord x).symm.trans (hh N hm le_rfl)
  exact ⟨(T.terminal.symm.trans (LinearEquiv.ofBijective A ⟨he,LinearMap.injective_iff_surjective.mp he⟩)).toContinuousLinearEquiv,
    fun _ => rfl⟩

-- Order indices d,m,N,p for matrix family. Use proofs explicitly, and in all
-- formulas state fitting when comparing to entries.
def window (d m N p : ℕ) : Exchange C d :=
  if hr : C.ref d ≤ m ∧ m ≤ N then (isomorphism C h d N p m hr.1 hr.2).choose else .refl _ _

lemma peek (hr : C.ref d ≤ m) (hm : m ≤ N) (x) : window C h d m N p x =
    ((C.factory d N p).entries m ((C.factory d N p).terminal.symm x)).x := by
  rw [window,dif_pos (And.intro hr hm)]
  exact (isomorphism C h d N p m hr hm).choose_spec x

lemma terminal_unit_vec (hr : C.ref d≤N) : (C.factory d N p).terminal.symm (C.refUnit d)=
    unitVec (C.labels.level d) C.path N := by
  let T := C.factory d N p
  have H := h.calibrated d N p hr
  apply T.terminal.injective
  unfold T
  rw [LinearEquiv.apply_symm_apply,← H.reads]
  rw [H.unit_coord _ le_rfl hr]

theorem ref_chart (hr : C.ref d ≤ N) : window C h d (C.ref d) N p = .refl _ _ := by
  ext1; funext v; rw [peek C h _ _ _ _ le_rfl hr]
  exact C.normalized h hr v



theorem chart_unit (hr : C.ref d ≤ m) (hm : m≤N) : window C h d m N p (C.refUnit d) =
    unitVec (C.labels.level d) C.path m := by
  rw [peek C h d N p m hr hm,terminal_unit_vec C h _ _ _ (le_trans hr hm)]
  exact (h.calibrated _ _ _ (le_trans hr hm)).unit_coord _ hr hm

/-- Looking up the literal column, now supplied via the packed
coordinates at level m. Does NOT recompute a Q for that location. -/
def column (v : C.label d) := C.O N p ((window C h d m N p).symm v)



/-- Transfer between two valid levels in this column space. Composes exactly
on chosen witness. -/
def cross (l i : ℕ) :=
  (window C h d l N p).symm.trans (window C h d i N p)



theorem same (l : ℕ) (v : C.label d) : column C h d N p l v=column C h d N p m (cross C h d N p l m v) := by
  simp [column,cross]

/-- The very entry and **unit/reference coefficients in it**, not a new field
assigned by fitting a conditional expectation. -/
def ink (v : C.label d) (l : ℕ) :=
    (C.factory d N p).entries l
      ((C.factory d N p).terminal.symm ((window C h d m N p).symm v))















end YM.Extra.Histories.Charts
