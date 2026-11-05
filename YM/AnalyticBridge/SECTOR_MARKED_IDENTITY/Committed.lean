import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Generate
import YM.Push.LOCAL_SPLITTING.Initial
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff


set_option warningAsError false

/-!
# The marked transition at a supplied Directed height

Purchase from exactly the unmarked SectorChange commitment. Keeps the β
within-band hypothesis there as well as all schedule choices (does not boost
any W here). The allocation, forest, and χ can be chosen before any probe. No
new income or choice of post-L constants purchased from estimates on marker
families. This doesn't construct Directed, input activities at a step, or
ensure every schedule affords even Cosmos!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Gaussian Rows YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Presented Input RG.Supply RG.Shoot
open YM.Pressure.Testing Overlay Marker
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {s : Supply.Sheet G} {D : Rolls s} {Θ : Protection D}
    {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y} {P : PostCost D}
    {Z : ChartRatio G} {K : MapPrices} (F : Directed G I Z K P) {g a E : ℕ → ℕ → ℝ}

private lemma fiery_clock (m p : ℕ) : fiery G (F.a.clock.hatBeta m) ((F.a.clock.op m p).patch.L) = F.a.clock.threshold (m+1) := by
  have hl : F.a.clock.hatBeta (m+1)=betaF G (F.a.clock.hatBeta m) ((F.a.clock.op m p).patch.L) := by
    unfold Calendar.hatBeta betaF
    rw [Schedule.scale_succ]; change _ = _ + _ * Real.log (F.a.S.block m).val; unfold Levels.S; ring
  change temp _ = temp _; rw [hl]

/-- Common sector-price premises from the committed step. Thus unmarked and
marked licenses can be used together for *every* R in that scope. Includes
PointCharge again (only to spend at the same intact integrals). -/
theorem honored (hW : Ringing K g W) (bill : Cosmos Z K W g a E) (N m p : ℕ) (hn : m<N)
    (R : Rep G (F.a.S.side (m+1) p)) (hR : Lives F.bake N (m+1) p R) (hb : R.beta∈band F.a (m+1)) :
    let j := F.a.clock.J (m+1); let i:=F.a.clock.J m
    let S := F.a.clock.op m p; let U := ships F N m p; let x := F.a.clock.hatBeta m
    let w := g j i; let d := a j i * F.a.clock.threshold (m+1)
    0 < w ∧ (∃ κ, 0 < κ ∧ PointCharge U x w κ) ∧ ∀ (Q : Allocation G S x w) (H : Forest S.ratio) (q : Chi),
      Bought U x R H Q q Z d := by
  -- `SectorChange.committed` states Licenses and some consequences of
  -- Permitted; recover full Permitted from the SAME price paid there.
  intro j i S U x w d
  have hadj : Scheduling.Adj j i := Scheduling.Deployment.adj F.a _
  have hg : s.first ≤ i := by rw [← F.valid.firstZero]; exact F.a.fits.mono (Nat.zero_le m)
  obtain ⟨hw,κ,hκ,hPay⟩ := Consumer.bought F g hW j i hg hadj.1 hadj.2
  obtain ⟨_,_,hGate⟩ := bill j i hadj hg
  obtain ⟨_,_,_,_,hB⟩ := hGate x (F.valid.pays m)
  have hL : S.patch.L = D.L j := (F.a.fits.sameFactor _).symm.trans (congr_fun F.valid.lengths _)
  have hsize : 100 * (1+radiusB x) ≤ (F.a.S.side m p).val := by rw [add_comm]; exact F.a.fits.sizeT m p
  have hx := proceeds F N m p hn
  obtain ⟨_,_,hG⟩ := hB _ _ S rfl hL hsize U hx
  have hd : fiery G x (D.L j)=F.a.clock.threshold (m+1) := by rw [← hL]; exact fiery_clock F ..
  rw [hd] at hG
  have hβ' : 0 < R.beta := by
    have hi := F.a.fits.delayed (m+1)
    have ht := hb.1; linarith
  refine ⟨hw,⟨κ,hκ,(hPay N m p hn rfl rfl).2.2.1⟩,fun Q H q => ⟨⟨_,_,_,_,_,hR.valid⟩,
    ⟨_,hx⟩,hβ',?_,fun A k V h => ((hG A H Q k V q).2 h _ hβ').1⟩⟩
  refine ⟨?_,hR.clip,?_⟩
  · rw [hR.path,F.bases]; rfl
  rw [hR.point]; change F.a.clock.threshold (m+1) = _; exact (fiery_clock F m p).symm

/-- Mixed marker derivative of the input E representation through the true
Gaussian transition, at such a height. No output trajectory assumption. Empty
selection permitted. Specifying all V as functions, not a.e. here. -/
theorem paid (hW : Ringing K g W) (bill : Cosmos Z K W g a E) (N m p : ℕ) (hn : m<N)
    (R : Rep G (F.a.S.side (m+1) p)) (hR : Lives F.bake N (m+1) p R) (hb : R.beta∈band F.a (m+1)) :
    let j := F.a.clock.J (m+1); let i:=F.a.clock.J m
    let S := F.a.clock.op m p; let U := ships F N m p; let x := F.a.clock.hatBeta m
    let w := g j i; let d := a j i * F.a.clock.threshold (m+1)
    ∀ (Q : Allocation G S x w) (H : Forest S.ratio) (q : Chi),
    ∀ {M : Type*} [DecidableEq M] [Fintype M] {B : Census M}, ∀ (L : Bands B R), L.Active →
      ∀ {r u c D b}, L.Radial r u c D b → ∀ (l : List M) (s : B.Mode), l.toFinset=s.val → l.Nodup →
      S.push R.beta (mark L s) = paidSum U x R H Q q Z d (mark L s) ∧
      ∀ V, SourceJet.mixed (fun t => S.push R.beta (SourceJet.combine (mark L) [] t) V) l 0 =
        paidSum U x R H Q q Z d (mark L s) V ∧
        ∀ (A : Stores S) (k : S.Choices), Permission U x V k A R (shots S x) H Q q Z d
          (fog A H U x V k) (meanLog A H U x V k q d) (mark L s) := by
  intro j i S U x w d Q H q M _ _ B L hL r u c D b h l s hs hl
  have he := (honored F hW bill N m p hn R hR hb).2.2 Q H q
  obtain ⟨_,hp,hg⟩ := he.coefficients hL h s
  exact ⟨hp,fun V => ⟨SourceJet.decides he hL h s l hl hs V,fun A k => (hg A k).1 V⟩⟩
end YM.Next.SectorChange.Marked
