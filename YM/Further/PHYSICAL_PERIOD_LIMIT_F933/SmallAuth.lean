import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Trades
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.WardDisk
import YM.Next.WARD_BIN.Sidebar


/-!
# Low weight Campaign in full, no stems or Poisson coupling hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Small
open Function Matrix Set Filter Wilson Lattice MeasureTheory RG Source Labels Supply Bid Stock Precision
  Extraction Lease Next.Extract Push.Common Push.Corrected
open Extra.Histories Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {a : Levels G} {C : Family G} {R : Hol G} {H : History G} {l m i N p d : ℕ} {F : Labels.Frame G d}



variable (S : SectionData F) (hS : S.Sound R)
include S hS


-- all cutoff Transfers (true scalar factor) without Program.Console
variable (hG : G.Simple) (hd : d <4) (H)

omit S hS



include S hS hG hd


omit S hS hG hd




include hG hd




omit hd
open Bay Disk

variable (Q : Bay.Roads G)
abbrev High (r : ℕ→ℕ) := ∀ d (N p : ℕ), r d ≤ N → 4 ≤ d → Disk.Quay H d N p

variable {r : ℕ→ℕ}
def Fit (X : High H r) (W : Worth) : Prop := ∀ d N p hr hd, Disk.Tested Q (X d N p hr hd) (r d) W

def tint (T : Bay.slots H) (X : High H r) (d : ℕ) (h : 4 ≤ d) : WardBin.Shelf (Bay.chart Q H r T d) := by
  refine ⟨r d,fun N p hv=> ⟨(X d N p hv h).pad,(X d N p hv h).flight,(X d N p hv h).ink⟩⟩

variable {r : ℕ→ℕ} {W : Worth}
structure WagesHigh (T : Bay.slots H) (X : High H r) (W : Worth) : Prop where
  valid : H.Selected
  gallery : Fit H Q X W
  made : (Bay.book H r T).Makes
  shelf (d : ℕ) (ht : 4 ≤ d) : WardBin.Shelf.Assured (tint H Q T X d ht) W
  matched d N p (hr : r d ≤ N) (ht : 4 ≤ d) : (T d N p).entries = fun i v =>
    let Z := X d N p hr ht; Z.flight.signal N (WardBin.pennies (Next.Foundations.localSection G d) Z.pad (Q.art d).cover 0 Z.ink v) i

-- r implicit defined after abbrev? autoimplicit false
open Next.Foundations
variable {t : ℕ→ℝ}


def inventory {E : ∀ d,WardBin.Chart C d} (Z : ∀ d ≥ 4,WardBin.Shelf (E d)) : Presentation C where
  step d i := if h : 4 ≤ d then (Z d h).spar i else ContinuousLinearMap.id ℂ _
  projected d i v := by split_ifs with ht; exact (Z d ht).step_power i v; rfl

omit hG in
lemma portable {E : ∀ d,WardBin.Chart C d} (Z : ∀ d ≥ 4,WardBin.Shelf (E d)) (f : Extraction.Order) : Affordable (inventory Z) f := by
  have h d : ∃ B : ℝ, 0 ≤ B ∧ ∀ i : ℕ × ℕ, ‖(inventory Z).step d i‖ ≤ B := by
    rcases lt_or_ge d 4 with h|h
    · exact ⟨‖(ContinuousLinearMap.id ℂ (C.label d))‖,norm_nonneg _,fun i => by simp [inventory, dif_neg h.not_ge]⟩
    obtain ⟨A,ha⟩:=(Z d h).bounded
    exact ⟨_,(norm_nonneg _).trans (ha (0,0)),fun i=> by simpa [inventory,h] using! ha i⟩
  choose b hp hZ using h
  exact ⟨fun d k=>⟨b d,hp d,Eventually.of_forall fun i=> hZ d (f.mesh i,k)⟩,fun d=>⟨b d,hp d,Eventually.of_forall fun k=>Eventually.of_forall fun i=> hZ d (f.mesh i,f.per k)⟩⟩


end YM.Further.PhysicalPeriodLimitF933.Small
