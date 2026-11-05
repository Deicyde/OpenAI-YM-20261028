import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.WardDisk
import YM.Next.WARD_BIN.Sidebar

/-!
# A single equation shelf and Page.Flow fuel producing the actual
 Family & paying both erased/rank bills. Engineering needs still
 missing: at least `.Earned.flows` (and Spins & Ink convention),
 Array.Volley, plus the other Billing/Post obligations from here to
 R.Phase (no claim they are feasible simultaneously even at these
 calendars). Note no graded ν_W on raw table presumed. WARD portfolio
 can itself serve as the equation campaign, addressing E actual
 equations and rank without separately fitting yet another presentation
 or Compares. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Sideshow
open Function Set Filter Topology Matrix MeasureTheory Wilson Lattice RG Source Labels Bid Precision
    Supply Pressure WardBin Next.Foundations Extra.Histories Work.G08 Bay Disk
    Extraction Lease Next.Extract Push.Common Push.Corrected Push.CutoffProjectors Dash
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {C : Family G} {W : Worth} {d N p : ℕ} {r : ℕ→ℕ} (H : History G) (Q : Bay.Roads G)

abbrev Ports (r : ℕ→ℕ) := ∀ d (N p : ℕ), r d ≤ N → Quay H d N p

def Fits (X : Ports H r) (W : Worth) : Prop := ∀ d N p hr, Tested Q (X d N p hr) (r d) W

def tint (C : Bay.slots H) (X : Ports H r) (d : ℕ) : WardBin.Shelf (Bay.chart Q H r C d) := by
  refine ⟨r d,fun N p h=> ⟨(X d N p h).pad,(X d N p h).flight,(X d N p h).ink⟩⟩

/-- Books kept *including definition provenance* for later phase-compatible use:
Used the very same rod sets & canonical entries on which `wardmark`, `Press` and `Tier` operate.
No hypothesis of Factory or Calibrated. -/
structure Wage (T : Bay.slots H) (X : Ports H r) (W : Worth) : Prop where
  valid : H.Selected
  gallery : Fits H Q X W
  made : (Bay.book H r T).Makes
  shelf (d : ℕ) : WardBin.Shelf.Assured (tint H Q T X d) W
  matched d N p (hr : r d ≤ N) : (T d N p).entries = fun i v =>
    let Z := X d N p hr; Z.flight.signal N (WardBin.pennies (localSection G d) Z.pad (Q.art d).cover 0 Z.ink v) i

variable {h : ℕ→ℝ}




variable {H Q}
def reefs (Z : ∀ d,WardBin.Chart C d) (P : ∀ d,WardBin.Shelf (Z d)) : Presentation C :=
    ⟨fun i => (P i).spar,fun d i v=> (P d).step_power i v⟩



lemma manifest (E : ∀ d,WardBin.Chart C d) (P : ∀ d,WardBin.Shelf (E d)) (Y : ∀ d,(P d).Assured W)
    (hC : C.Makes) (hp : Bank W C.path.levels) (hw : roomCost C.path.levels W) (hG : G.Simple) (f : Extraction.Order) (d : ℕ) :
    f.late fun N p=> Module.finrank ℂ (LinearMap.range ((reefs E P).step d (N,p)).toLinearMap)= Module.finrank ℂ ((Cells.standard C).Field d) := by
  -- every sufficiently fine cutoff, BEFORE dominant extraction; exact free quotient, no IR watch
  have hx := (P d).panel_event (Y d) hC hG hw hp
  refine Eventually.of_forall fun i=> f.mesh.cofinal.eventually (hx.mono (q:=fun x=> Module.finrank ℂ (LinearMap.range ((reefs E P).step d (x,f.per i)).toLinearMap)= Module.finrank ℂ ((Cells.standard C).Field d)) fun x h=>?_)
  let P₀ := (P d).spar (x,f.per i)
  have ht := LinearMap.finrank_range_add_finrank_ker P₀.toLinearMap
  let S := Cells.standard C
  have hy := Submodule.finrank_quotient_add_finrank (S.null d)
  rw [show LinearMap.ker P₀.toLinearMap = LinearMap.range ((P d).panel (x,f.per i)) from (P d).spans_out _, LinearMap.finrank_range_of_inj (h (f.per i)), show Module.finrank ℂ (WardBin.PureBasis.Grid G d)=Module.finrank ℂ (Maxwell.equationIdeal G d) by simp [WardBin.PureBasis.Grid,WardBin.Count]] at ht
  have he : Module.finrank ℂ (S.null d) = Module.finrank ℂ (Maxwell.equationIdeal G d) := by
    change Module.finrank ℂ ((Maxwell.freeTable C.book.grid).null d)=_
    rw [← Push.CutoffProjectors.free_null d (Push.FiniteDetection.residual_trivial ..)]; exact equation_dim _
  rw [he] at hy; exact Nat.add_right_cancel (ht.trans hy.symm)


end YM.Further.PhysicalPeriodLimitF933.Sideshow
