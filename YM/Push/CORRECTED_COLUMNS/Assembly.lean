import YM.Next.EXTRACTION.Use
import YM.Next.FOUNDATIONS.SU2
import YM.Next.PHASE.Assembly
import YM.Push.CORRECTED_COLUMNS.Rank

/-!
# The conditional RankWidths producer and phase consumers

Explanations/ledger in Program/Sampling and report. Keep `π` produced
before the final application. It can be asked e.g. before or after raw
extraction. Everything stays on C and these same Y/P data. This gives
also one route to the Detector *input* on this refinement; it isn't used
to prove its own rank comparison. Symmetries of kernels from accepted
ports; no claim here about continuous rotations or H-equivalence of
physical with Maxwell.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open Function Set Filter MeasureTheory Lattice Wilson Cells Extraction Dash Table Next.Extract
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {S R T : Table C.book} {W : DiffPlan T} {b : Presentation C}
variable {M : ℕ → Table C.book} {f g : Extraction.Order} {P : Bin S} {q : ∀ d, ℕ → CoordMap C d}

/-- One family of widths data specified at cutoffs. R phantom; production
may be before knowing T (use any table of this book). Should start after
location and free columns (`fitData`, `Sampling.columns`) or retain an
explicit X from a larger estimate. -/
structure Survey (C : Family G) (R : Table C.book) where
  X (d : ℕ) : Columns C R d
  Y (d) : Tests (X d)
  price (d : ℕ) : Prices

variable (π : Survey C R)

namespace Survey
abbrev Labels (π : Survey C R) := ∀ d, ℕ → AxisX (π.X d) → C.label d
abbrev PerLabels (π : Survey C R) := ∀ d, ℕ → AxisX (π.X d) → ℕ → C.label d

def Ready (π : Survey C R) (f : Extraction.Order) : Prop := ∀ d, (π.Y d).Offer (π.price d) f

def Read (f : Extraction.Order) (z : π.PerLabels) (t : π.Labels) : Prop := ∀ d, Settled f (π.Y d) (z d) (t d)

lemma tail (h : Tails g f) (H : π.Ready f) : π.Ready g := fun d => (H d).tails (π.Y d) h


/-- Fixed-index limits on common extraction. Also per projection data and
arbitrary other `Reserve`s can be included (see `common`). -/
theorem settles (H : π.Ready f) : ∃ g : Extraction.Order, ∃ z t, π.Read (f.refine g) z t := by
  let I := (d : ℕ) × (ℕ × AxisX (π.X d))
  let X (i : I) := C.label i.1
  let D (i : I) (N p : ℕ) : C.label i.1 := (π.Y i.1).tune i.2.1 N p i.2.2
  have he : Reserve (X:=fun i : I => C.label i.1) f (fun _ _ => True) D := by
    refine Reserve.of_norm (fun _ => Eventually.of_forall fun _=>trivial) ?_ ?_
    · intro i p _
      obtain ⟨u,hp,h⟩ := (H i.1).known i.2.1
      exact ⟨u,hp,(h p).mono fun j hj => hj i.2.2⟩
    intro i
    obtain ⟨u,hp,h⟩ := (H i.1).known i.2.1
    exact ⟨u,hp,Eventually.of_forall fun p => (h _).mono fun j hj => hj i.2.2⟩
  obtain ⟨g,w,y,h⟩ := he.gather
  exact ⟨g,fun d k i => w ⟨d,k,i⟩,fun d k i => y ⟨d,k,i⟩,
    fun d => ⟨fun k i p => h.rows ⟨d,k,i⟩ p trivial,fun k i => h.outer ⟨d,k,i⟩⟩⟩
lemma uses (p : Base C f S M P T W) (h : G.Simple) (H : π.Ready f) (u y) (hz : π.Read f u y)
    (ht : Projected b f P q) (ha : ∀ d, Persist.Count b f d) : RankWidths C f T := fun d =>
  ⟨retarget (π.X d) T, offered h ((π.Y d).take T) (π.price d) (y d),valid h p ((π.Y d).revoke T _ (H d))
    ((π.Y d).carry T _ _ (hz d)) (ha d) q ht⟩

end Survey

/-- Use on an order with the cutoff estimates. **No Detector premise**
here. Base proof application as in `Extract.finish`, now passing shortage
for the all-Shot monitor directly. Also recovers Detector on *this* order
(with a finite not-necessarily-pair set of smeared tests for each d).

Hinges on *both* quantitative norm estimates (Y Offers) and actual
upper rank/discrepancy physics including finite Counts. -/
theorem finish (hC : C.Makes) (c : CenterPort C f) (hG : G.Simple) (p : RawLimits C f S M) (hi : Projected b f P q)
    (he : ∀ d, RelayCosts b f d) (H : π.Ready f) (hw : ∀ d, Persist.Count b f d) (u y) (hz : π.Read f u y) :
    (∀ d, Detector b f d) ∧ ∃ (T : Table C.book) (W : DiffPlan T), Base C f S M P T W ∧
      (∀ d, Columns.Trials.Valid f (offered hG ((π.Y d).take T) (π.price d) (y d))) ∧ Spec.Seed C f T := by
  have hv := fun d => hi.ready d (he d)
  have hx (i : Live S) (d : ℕ) : Bin.shortage P i d := Persist.shortage hC p (H d) (hz d) hG (hw d) hi i
  have ha := Bid.arriving c hC Work.D01.answer Work.D02.answer Work.D03.answer Work.D04.answer M p P hv hx
  have hm : Spans ha.born P f := Work.D04.answer Work.D01.answer Work.D02.answer Work.D03.answer ha.born hC c
    p.integral P hv (hx ha.born)
  -- Detector now (only now, no circular use of D04)
  have hr d := detector_of_good ha.born p.integral (hi.approaches d) (hi.same d).symm
    (Bin.exactC P p.integral (hm.p d) (hm.q d))
  -- use original Extract finish; carries cleaner.
  obtain ⟨T,W,h⟩ := Next.Extract.finish hC c p hi he hr
  exact ⟨hr,T,W,h,(fun d => valid hG h ((π.Y d).revoke T _ (H d)) ((π.Y d).carry T _ _ (hz d)) (hw d) q hi),
    h.seed (π.uses h hG H _ _ hz hi hw)⟩



/-- Downstream. Normalized phase after these *finite* bills. `X : Algebra`
is what rotation/stress producers would provide at this smooth Base;
still need `Org.Grill` on this f (not from single-cell estimates), etc. -/
theorem phase (R0 : Base C f S M P T W) (hG : G.Simple) (H : π.Ready f) (hp : ∀ d, Persist.Count b f d)
    (hi : Projected b f P q) (u y) (hz : π.Read f u y)
    (X : Spec.Algebra T) (a : Org.Grill C f) (L : Spec.Locals X R0.kernel.spin) :
    ∃ Z : OS.Selection T, Spec.Materializes (C:=C) X Z R0.kernel.spin ∧
      ∀ i d, (Z.ensemble i).null d=T.null d := by
  let s := R0.seed (π.uses R0 hG H _ _ hz hi hp)
  obtain ⟨Z,hz⟩ := Next.Phase.material s X a L
  exact ⟨Z,hz,hz.phase.retains⟩
end YM.Push.Corrected
