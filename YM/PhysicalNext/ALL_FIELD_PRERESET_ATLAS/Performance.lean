import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Reconnect
import YM.Next.BOUNDARY.Coordinates
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Volume



/-!
# Enacting BOTH versions of the pre-reset performance

One bank, two readers. Only difference is the value of some (forced) correction
terms. The compensated second reading is for the actual `BeforeReset.give`; the
first is for `Return.atlas`. See `TwoMasks` for why identical payments to all
addresses in both would in general be an error. Before calling these with the
Gaussian step must **prove** the exact first-gas density with this banker & same
component Pane and their analytic footprints. `Exposure` for that supplier path,
`Frontpage` for applying the whole route.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas.Hangar
open RG Lattice Wilson Function Filter Finset SectorNext.Reconnect
open AnalyticBridge.CouplingShape AnalyticBridge.VerifiedReset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {ι κ : Type} [Countable ι] [Countable κ]
    (p : BudgetPoint) (R : PathData G) (c : Clip)
    (F : Palette G n ι κ)
variable {p R} {M : Pane G n ι κ} {Q : Plate n}
    (T : Tape G p (atrium p M R) Q) (q : Courier Q (printed T))

def driver (s : Reading) (β α : ℝ) : Collection.Source G n :=
    q.fluid (pooled c F T β α) (marked c F T s β α)

/-- A denotational enactment **at this Courier**. -/
def viewResult (s : Reading) (R : PathData G) (c : Clip) (p : BudgetPoint) (X : Collection.Listing G n)
    (v : Collection.Source G n) (β α z : ℝ) : Config G n → ℝ := match s with
  | .returnMask => Collection.earlyValue X R c p v β z α
  | .shapeMask => received R c p (X.read v) z β α

lemma score (s : Reading) (V : Config G n) (β α z : ℝ) :
    viewResult s R c p q.grid (driver c F T q s β α) β α z V =
      Real.exp (fair c F T s β α z V) * ∑' i,(printed T).sell p (marked c F T s β α) V i := by
  let U s := q.grid.read (driver c F T q s β α)
  have he s : (U s).gas p V = _ := q.outgas p (pooled c F T β α) (marked c F T s β α) V
  have ht s : (U s).additive p V = _ := q.outlog p (pooled c F T β α) (marked c F T s β α) V
  cases s
  · unfold viewResult Collection.earlyValue Collection.frozen Rep.eval Rep.exponent
    change Real.exp (_-_ - (U .returnMask).additive p V)*(U .returnMask).gas p V * _ = _
    rw [ht, he,mul_right_comm,← Real.exp_add]; congr 2
    unfold fair; change ((_*_ - R.inChannels c p β V-_)+(-α)*_) = _*_-_-α*Collection.receipt R c p V-_
    ring
  unfold viewResult received foreword; change Real.exp (_-_-_-(U .shapeMask).additive p V)*(U .shapeMask).gas p V = _
  rw [he,ht]; rfl

variable {c F} {σ C Λ : ℝ} (h : R.Bounds c σ C Λ)
    (hs : OriginalLight p M F) {b : BidLog ι κ} (hb : b.Negative p M F)
include h hs hb


end YM.PhysicalNext.PreAtlas.Hangar
