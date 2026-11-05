import YM.Next.FOUNDATIONS.Regular
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Candidates

/-!
# Actual Grid Plan for the matching probes at k

`C.priced` pays actual `Regular`, masked
norms at THIS cutoff (not an arbitrary supplied credit hypothesis). Full
group sup is essential for complements. Numerical additional prices
in `pricedBirth`, not presumed as part of Calendar; only sufficient. Use with `readiness` and `sails` to ask for true propagation on these
signals. Does not solve column matching.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Labels Source MeasureTheory Function Filter Finset Ac Marker Overlay Attach Cells
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G)

section coarse

variable {d N k p : ℕ}

/-- `Credit` incurred by the actual local-section of C on this lattice
level, extended to a vector. -/
lemma specific_price (H : C.Makes) (o : Site (C.side k p)) (he : C.ref d ≤ k) (hN : k≤N) (v : C.label d) :
    let T := C.localSection d; let B := (C.path.rep N p k).p
    B.Regular (T.footprint o) (T.places v o) ∧
    B.supBounds o (T.footprint o) (T.places v o) ((C.path.levels.params k).columns *
      (C.labels.level d).coeffSize ((C.labels.level d).scaled B.threshold v)) := by
  intro T B
  have hi := (H.wilson.represents N p k hN)
  let L : C.label d →ₗ[ℂ] Config G (C.side k p) → ℂ := {
    toFun v := T.places v o
    map_add' u v := funext fun U => congr_fun (T.eval_linear.map_add u v) (expandAt o U)
    map_smul' u v := funext fun U => congr_fun (T.eval_linear.map_smul u v) (expandAt o U) }
  let F := C.labels.level d
  let r (i : F.Index) := (C.path.levels.params k).columns * (B.threshold^(F.grades i).2)
  have hz (i : F.Index) : B.Regular (T.footprint o) (L (Pi.single i 1)) ∧
      B.supBounds o (T.footprint o) (L (Pi.single i 1)) (r i) := by
    unfold r B; rw [hi.vac]; exact H.priced d k p he o i
  have hx : T.places v o = ∑ i : F.Index, v i • L (Pi.single i 1) := by
    have ht := congr_arg L (coeff_sum C v)
    simp only [map_sum,map_smul] at ht; exact ht.symm
  have hu (i : F.Index) : (C.path.levels.params k).columns * ‖F.scaled B.threshold v i‖ = ‖v i‖ * r i := by
    rw [F.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg B.threshold_pos.le _)]
    unfold r; ring
  rw [hx]; change _ ∧ B.supBounds _ _ _ ((C.path.levels.params k).columns * F.coeffSize (F.scaled B.threshold v))
  unfold Frame.coeffSize; rw [Finset.mul_sum]; simp_rw [hu]
  exact Next.Foundations.regular_bound_sum _ _ _ fun i _ =>
    ⟨Next.Foundations.regular_smul _ (hz i).1,Next.Foundations.bound_smul _ (hz i).2⟩

/-- Unit split of coarse candidate (scaled bump attached in formula). -/
def paint (d k p : ℕ) (x : C.label d) (o : Site (C.side k p)) :=
    (C.localSection d).places ((C.labels.level d).scaled (C.path.levels.clock.threshold k)⁻¹ ((C.labels.level d).core x)) o

-- Binder order explicit since C.S.side depends on k p.
open scoped Classical in
def turns {h : ℕ} (hk : h ≤ k) (x : C.label d) (i : Site (C.side h p)) :=
    let T := tilesAt C.S p hk
    let y := (C.labels.level d).act (T.omega i).ortho x
    if T.hand i then star y else y



lemma paint_bounds (H : C.Makes) (o : Site (C.side k p)) (he : C.ref d ≤ k) (hN : k≤N) (v : C.label d) :
    let T := C.localSection d; let B := (C.path.rep N p k).p
    B.Regular (T.footprint o) (paint C d k p v o) ∧ B.supBounds o (T.footprint o) (paint C d k p v o)
      ((C.path.levels.params k).columns*(C.labels.level d).coeffSize ((C.labels.level d).core v)) := by
  intro T B; unfold paint
  let F := C.labels.level d; let θ := C.path.levels.clock.threshold k
  have ht := specific_price C H o he hN (F.scaled θ⁻¹ (F.core v))
  have hp : B.threshold=θ := by unfold B; rw [(H.wilson.represents N p k hN).vac]; rfl
  change B.Regular _ _ ∧ B.supBounds _ _ _ ((C.path.levels.params k).columns*F.coeffSize (F.scaled B.threshold (F.scaled θ⁻¹ (F.core v)))) at ht
  have hx : F.scaled B.threshold (F.scaled θ⁻¹ (F.core v)) = F.core v := by rw [← hp,F.scaled_inv B.threshold_pos.ne']
  rw [hx] at ht; exact ht


end coarse

section assigns
variable {C} {d h k N p : ℕ} (H : C.Makes)
variable (a : Bands (Joint.Markers C.path h p) (C.path.rep N p k))
variable (hk : h≤k) (hr : C.ref d≤k) (hn : k≤N)
variable (hv : ∀ i, a.origins i = anchor C.S p hk i)

def paintsAt (x : C.label d) : Attach.Plan a where
  Y i := (C.localSection d).footprint (a.origins i)
  c i := turns C hk x i 0
  F i := paint C d k p (turns C hk x i) (a.origins i)
  good i := (paint_bounds C H _ hr hn _).1
  origin i := Finset.mem_image.mpr ⟨0,(H.sections d).anchored,by simp⟩

include hv





end assigns
end YM.Push.GridApprox
