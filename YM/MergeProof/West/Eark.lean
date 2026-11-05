import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Gates
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision RG Filter
open Further.FreeCovariance.KP
open Next.Rank Next.Rank.Atlas Next.Rank.Radian Next.Rank.Perch Next.Rank.CellsInt Next.Rank.Station
open scoped Topology BigOperators

section pre
variable {K : KernelChoices} (P : Prisms K)

def reserveX (u J D : ℕ) (b L : ℝ) := ∀ n : ℕ, n≤u →
    Radian.Weight L (P.wheels J) b (Glimmer.fuel D n/4)

/-- Conditions only on costs on the planned plateau, ALL pre-C.
Only these numerical conditions are needed at the analytics call below.
Sufficient test `reserve` can actually be charged before L (proof
`reserving`), then anchors at weak stretch (`clearing`). -/
structure Eark (P : Prisms K)(u:ℕ) (J d D : ℕ) (b L s : ℝ) : Prop where
  optics n (h : n≤u) : P.wheels J ^ bump L b s * (2:ℝ)^d ≤ fraction n D s
  front : P.glass J d ≤ Perch.bill (1/4) s
  hinge n (h : n≤u) : P.centers J ≤ fraction n D s

variable {u:ℕ}
lemma reservingX (J D : ℕ) {b : ℝ} (hb : 0≤b) : ∀ᶠ L in atTop, reserveX P u J D b L := by
  have he:= (eventually_all_finset (Finset.range (u+1))).2 fun n _=> Radian.enough_room (n:=D) (m:=n) _ (P.net J) hb
  exact he.mono fun L hl n H=> hl n (Finset.mem_range.mpr (by omega))
lemma clearingX {J D b L} (h : reserveX P u J D b L) (d : ℕ) : ∀ᶠ s in atTop, Eark P u J d D b L s := by
  have he:= (eventually_all_finset (Finset.range (u+1))).2 fun n hn=> (gloss (h n (by have hh:= Finset.mem_range.mp hn;omega)) d).and
    ((Perch.bill_lo (show 0<Glimmer.fuel D n/4 from div_pos (Glimmer.fuel_real ..) (by norm_num))).eventually_ge_atTop (P.centers J))
  filter_upwards [he,(Perch.bill_lo (by norm_num : 0<(1/4:ℝ))).eventually_ge_atTop (P.glass J d)] with s he hf
  have ht n (hn : n ≤ u) := he n (Finset.mem_range.mpr (by omega)); exact ⟨fun n hn=> (ht _ hn).1,hf,fun n hn=> (ht _ hn).2⟩

variable {G : Gauge} {b : ℝ} (A : Levels G) (hA : A.clock.kernel=K)
variable {d D k : ℕ}
include hA

/-- Supply both Rank invoices, preserving SAME atlas all conjuncts. Does
not obtain a clearance merely from the width station/datums preexisting. -/
theorem y_supply (h : Allowed A b k) (ht : d-1 ≤ A.clock.J k-2) (he : Eark P u (A.clock.J k) d D b (wheel A k) (clim A k)) (N p : ℕ):
    Seal A k p d 2 (stamp A N p) chartHeat ∧ ∀ n : ℕ, n ≤ u → Worker.Folded k (middle A b k) p D A (stamp A N p) d n := by
  let J := A.clock.J k; have hJ:4≤J:= A.clock.adm k; let l:=middle A b k
  have hl : A.clock.J l=J := h.plateau l (wider ..) (before ..)
  refine ⟨P.locks J d hJ _ hA N k p rfl he.front,fun n hn=> ?_⟩
  refine ⟨stamp_real A N k p,stamp_real A N l p, fun i=>rows_close A N p l i, fun i j=> (P.earns _ hJ A hA N l p hl i j).trans (he.hinge n hn),
    P.wheels J,P.net J,?_,fun i hi hp=> P.tracks J hJ _ hA _ _ _ d ?_ ?_ ht⟩
  · rw [h.full]; exact he.optics n hn
  · apply h.plateau _ (((wider A b k).trans hi).trans (Nat.le_succ _)) hp
  exact h.plateau i ((wider ..).trans hi) hp.le
end pre
end YM.PhysicalNext.RankCovariance
