import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Shutter
import YM.Push.GRID_APPROXIMATION.Cone


/-!
# Pinned stencils, including all fallback tags

Exact componentwise read criteria even for noisy V. The no-hole
projection is **not** needed. Again at fixed θ and field; see other
ports for comparing tags. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Curtain Spot.Programme Spot Notice
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
    {H R K : Type} {X : Support c} {l : Viewport u X H R K} {a : Notice l}

namespace Viewport
private lemma free_edge (e : u.F.Free) : e.val∉u.F.trunks := e.property
lemma edges_free (l : Viewport u X H R K) (e : H⊕R) : l.edges e ∉ u.F.trunks := free_edge _
lemma bars_free (l : Viewport u X H R K) (e : K) : l.bars e ∉ u.F.trunks := free_edge _
lemma not_bar (l : Viewport u X H R K) (i : H⊕R) (j : K) : l.edges i ≠ l.bars j := by
  intro h; have ht : (l.read i).val=(l.held j).val := Subtype.ext h
  exact (l.read i).property (ht.symm ▸ (l.held j).property)

def Latches (l : Viewport u X H R K) (Y : Set (Site f)) :=
    ∀ i : Bond f,i.1∈Y → i.1+Lattice.step i.2∈Y →
      i∈u.F.trunks ∨ ∃ j : H⊕K, i=Sum.elim (fun h => l.edges (.inl h)) l.bars j

lemma full (l : Viewport u X H R K) (p : Display G H R K) : ∃ q : Visual u,l.info q=p := by
  let C := extend l.held p.1 (fun _ => 1)
  let R := extend l.slot p.2 (fun _ => 0)
  exact ⟨(C,R),Prod.ext (funext (fun i => l.held.injective.extend_apply p.1 (fun _ => 1) i)) (funext (fun i => l.slot_inj.extend_apply p.2 (fun _ => 0) i))⟩
end Viewport

namespace Notice
variable [Fintype H] [Fintype R] (a : Notice l)

/-- Pad unread U, still fixing real tree links. This is for checking
local read agreements and ordering all derivative hypotheses, *not* for
testing global likelihoods or replacing K's on a nonguarded expansion. -/
def pad (V : Config G c) (p : Display G H R K) : Config G f := extend l.edges
    (a.givenU V p) (extend l.bars p.1 1)

lemma at_bones (V : Config G c) (p : Display G H R K) (i : H⊕R) : a.pad V p (l.edges i) = a.givenU V p i :=
    (show Injective l.edges from fun _ _ e => l.read.injective (Subtype.ext (Subtype.ext e))).extend_apply ..
lemma at_bars (V : Config G c) (p : Display G H R K) (i : K) : a.pad V p (l.bars i) = p.1 i := by
  unfold pad; rw [Function.extend_apply' (f:=l.edges) _ _ (l.bars i) (not_exists.mpr (fun j => l.not_bar j i))]
  exact (show Injective l.bars from fun _ _ e => l.held.injective (Subtype.ext (Subtype.ext e))).extend_apply ..
lemma at_tree (V : Config G c) (p : Display G H R K) : SliceSet S u.F (a.pad V p) := by
  intro i hi; unfold pad; rw [Function.extend_apply' (f:=l.edges) _ _ _ (not_exists.mpr (fun j he => l.edges_free j (he.symm ▸ hi))),Function.extend_apply' (f:=l.bars) _ _ _ (not_exists.mpr (fun j he => l.bars_free j (he.symm ▸ hi)))]
  rfl


lemma enables (V : Config G c) (p : Visual u) (Y : Set (Site f)) (he : u.Clearing V) (hy : l.Latches Y) :
    Agrees Y (a.pad V (l.info p)) (u.hard V p) := by
  intro i hi hh
  rcases hy i hi hh with ht|⟨j,hj⟩
  · exact (a.at_tree _ _ _ ht).trans ((u.F.on_tree _ ⟨_,ht⟩).symm)
  rw [hj]; cases j
  · exact (a.at_bones ..).trans (a.givenU_here V he ..)
  exact (a.at_bars ..).trans (Notice.hold_here ..)

lemma holds {r : ℝ} (hr : Ready d.chart d.g r) (V W : Config G c) (p : Reel G H R K) (h : Had (l:=l) r V p)
    (h' : Had (l:=l) r W p) {Y : Set (Site f)} (hy : l.Latches Y) :
    Agrees Y (a.pad V (p.1,a.imprint V p)) (a.pad W (p.1,a.imprint W p)) := by
  intro i hi hh
  rcases hy i hi hh with ht|⟨j,hj⟩
  · exact (a.at_tree _ _ i ht).trans ((a.at_tree _ _ i ht).symm)
  rw [hj]; cases j
  · rename_i j; change a.pad V _ (l.edges (.inl j))=a.pad W _ (l.edges (.inl j))
    exact ((a.at_bones V _ (.inl j)).trans (a.stalls hr V p h _)).trans (((a.at_bones ..).trans (a.stalls hr W p h' _)).symm)
  rename_i j; change a.pad V _ (l.bars j)=a.pad W _ (l.bars j)
  rw [a.at_bars V _ j,a.at_bars W _ j]


end Notice
open YM.Push.GridApprox

def frameUses (S : StepData c f) (i : Site c) := YM.Push.GridApprox.window (S.ratio.embed i) (reach S.patch)
def predictorUses (S : StepData c f) (i : Edge (Site c)) := frameUses S i.1 ∪ frameUses S (i.1+step i.2)

lemma knows_site (u : Spot d) (i : Site c) (h : S.patch.Branches S.kernel G) : LocalOn (frameUses S i) (u.frameBit i) := by
  intro V W he; unfold Spot.frameBit; rw [(site_dep S h i he _).2]
lemma knows_bond (u : Spot d) (i : Edge (Site c)) (h : S.patch.Branches S.kernel G) : LocalOn (predictorUses S i)
    (fun V => S.prediction (G:=G) V u.k i) := by
  intro V W he; unfold StepData.prediction
  refine congr_arg (fun f => S.patch.predict S.kernel f (u.k.2 i)) (connector_dep S h i _ _ rfl rfl
    (fun e hi hh => he e (Or.inl hi) (Or.inl hh)) (fun e hi hh => he e (Or.inr hi) (Or.inr hh)))
end YM.AnalyticBridge.LocalGaussian
