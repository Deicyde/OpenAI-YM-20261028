import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.FiniteRange

/-!
# On-support evaluation of the windows

A consumer for the tables needed by subsequent integrals. Here an output
V with flags *only locally* matched to A at the queried points still affords
marginal covariance precision & jet tests. Stay on the fixed label inputs
for every differentiation at such a V, not in a neighborhood where *A* is
reclaimed valid for that V. Epoch hypotheses purchased before all works;
see `Full.full_windows`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Placement
open Function Filter Lattice RG Pressure Pressure.Stores Precision Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps Next.Fluctuations
open Next.SectorChange.Completion Next.SectorChange.Rows Full Matching Push.SectorMeasure
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x C γ t η r : ℝ} {P : Patch}
    {U : Teller G} {T : Tube G S} {n : ℕ}

/-- Keep all OTHER inputs fixed, change remote record flags only. -/
def amended (x : ℝ) (A : Stores S) (V : Config G c) : Stores S :=
  { A with flags:=RG.flags (temp x) V }

-- local agreement of flag reads at V, only use through these locations.
-- Does not assert that A is used at V in the global integral (need D.bill).
def Printed (x : ℝ) (A : Stores S) (V : Config G c) (i : Site c) (R : ℕ) :=
  ∀ j, separation i j ≤ R → (j∈A.flags ↔ j∈RG.flags (temp x) V)

variable {A : Stores S} {V : Config G c} {F : Forest S.ratio}
    {k : S.Choices}

lemma Printed.repair {o : Site c} {R : ℕ} (h : Printed x A V o R) (k : S.Choices)
    (F : Forest S.ratio) (z : Coord G c) :
    ReadsWithin o R A (amended x A V) F F (coarse V z) (coarse V z) k k :=
  ⟨fun _ _ => rfl,h,fun _ _ => Iff.rfl,fun _ _ => Iff.rfl,fun _ _ => rfl,
    fun _ _ => rfl,fun _ _ => rfl⟩

/-- Local validity test includes actual V links. Use all endpoints; the
radius here is an initial-site price. -/
lemma Printed.test {R : ℕ} {o : Site c} {W : Config G c} (h : AgreeNear id o (R+7) V W) :
    Printed x A V o R ↔ Printed x A W o R := by
  have he (i) (hi : separation o i ≤ R) : i∈RG.flags (temp x) V ↔ i∈RG.flags (temp x) W := by
    rw [flags_spec,flags_spec]; apply exists_congr; intro p
    apply and_congr_right; intro hp
    have hz := Work.E01.sep_touched p i hp
    have HH : faceValue V p=faceValue W p := Next.Fluctuations.travel_near id
      (fun j k => Work.E03.sep_step j k) V W p.1 (square p.2.val.1 p.2.val.2) 4 le_rfl (h.shrink
        (show separation o p.1+4 ≤ R+7 by have hl := separation_triangle o i p.1; rw [separation_comm] at hz; omega))
    rw [HH]
  exact ⟨fun hb i hi => (hb i hi).trans (he i hi), fun hb i hi => (hb i hi).trans (he i hi).symm⟩

section audits
variable (A F V k) {ι : Type} [Fintype ι]
variable (e : ι → Index G f)

omit [Fintype ι] in
lemma on_deck {R : ℕ} {E : Reading S G} {L : ℕ} (hR : Local E L R)
    (h : ∀ i, Printed x A V (point S (e i)) R) :
    limitTo (fun z => E A F (coarse V z) k) e =
    limitTo (fun z => E (amended x A V) F (coarse V z) k) e := by
  funext z; ext i j
  exact (hR.both ((h i).repair k F z) (e i) (by simp) _).1






end audits
end YM.AnalyticBridge.NonflatCovarianceLocality.Placement
