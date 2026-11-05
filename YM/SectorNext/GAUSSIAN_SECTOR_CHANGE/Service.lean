import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Free/Schedule compatibility and an actual committed consumer

No rerolling any of the horizon data. Same V, same F.label/kin and
frame in the RG cutEntry as in the numerical Beam and sector Grants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Client
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Wisps Tier Schur LocalJet
open Input RG.Supply RG.Shoot Scheduling YM.Pressure.Testing
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {B : Beam K D} {F' : ℕ → ℕ → Postage}



variable {C : Sheet G} {D₀ : Rolls C} {T : Protection D₀} {W₀ : Delays T} {Y₀ : Bar W₀} {I₀ : Wait Y₀}
    {Q : PostCost D₀} {Z : ChartRatio G} {K₀ : MapPrices} {w t E : ℕ → ℕ → ℝ}

lemma funded (F : Directed G I₀ Z K₀ Q) (hW : Ringing K₀ w W₀) (bill : Cosmos Z K₀ W₀ w t E)
    (N m p : ℕ) (hn : m<N) : Larger (G:=G) (F.a.clock.op m p) := by
  let S:=F.a.clock.op m p; let j := F.a.clock.J (m+1); let i:=F.a.clock.J m
  have ha : Adj j i:=Deployment.adj F.a _
  have hh := bill j i ha (show C.first ≤ i by rw [← F.valid.firstZero]; exact F.a.fits.mono (Nat.zero_le _))
  have he := hh.stars _ (F.valid.pays m)
  have hL : S.patch.L = D₀.L j := (F.a.fits.sameFactor _).symm.trans (congr_fun F.valid.lengths _)
  have hc : 100*(1+radiusB (F.a.clock.hatBeta m)) ≤ (F.a.S.side m p).val := by rw [add_comm]; exact F.a.fits.sizeT m p
  have hp := Pressure.Testing.proceeds F N m p hn
  obtain ⟨hi,hl,H⟩ := he.2.2.2.2 _ _ _ rfl hL hc (ships F N m p) hp
  exact ⟨funds_branch hp,hi,hl⟩


end YM.Next.SectorChange.Client
