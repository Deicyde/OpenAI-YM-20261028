import YM.PhysicalNext.ORDERED_AFFINE_2B.Arrivals
import YM.PhysicalNext.ORDERED_AFFINE_2B.Reaches


/-!
# Complete supports for the ordered binder

Queries on the root's and EVERY intermediate and endpoint's usable
record, not just at nonzero occurrence/vetted data; include both endpoints
(even if coincident) in the stencil expansions. Only comparing the resulting
AFFINE/mean/determinant ledger, not U-integrands or hard tests depending
on global realizability. Keep also the V edges for every plaquette in any
queried flag predicate (including negative answer). Allow `readH + 12`
or any larger paid support to include endpoint meeting partners of all
these answers; effect on cover/cost issued in Currency. `Archive.queryV`
spelled at +10, with height sharing etc even before perturbations for all
answers besides numerical/sector supports. Fixed Tube charged at each use
(not varying between sectors). .
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Shelter
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree AnalyticBridge AnalyticBridge.Covariance Terrain
open AnalyticBridge.ResetIncome SectorTools.ActualScalar Whole Footprint
open Next Next.Fluctuations Next.SectorChange
open Further Further.CurvedGaussianJets Jets ChangeV Tracks
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

-- for effects of numerical calculations. Keep + allowances at ends.
def readN (P : Patch) (x : ℝ) := max (Padded.allN P x) (chargeR P x)
def readH (P : Patch) (x : ℝ) := max (Padded.signalH (Padded.allN P x) x) (chargeD P x)


variable {c f : Side} {G : Gauge} {S : StepData c f}
    {F F' : Forest S.ratio} {A A' : Stores S} {k k' : S.Choices} {x : ℝ} {T : Tube G S} {V V' : Config G c}
    {i j : Thing G f}
abbrev Bound (p : Site c) (x : ℝ) (A A' : Stores S) (F F' : Forest S.ratio) (k k' : S.Choices) (V V' : Config G c) := Teams S p
    (readN S.patch x) (readH S.patch x) F F' A A' k k' V V'

def Regard (W : CurvedGaussianJets.Windows (Thing G f)) (C C' : CurvedGaussianJets.Table (Thing G f)) (i j : Thing G f) :=
    C i j=C' i j ∧ (C*W.blend C-1) i j=(C'*W.blend C'-1) i j ∧
    W.localGram (C) i = W.localGram (C') i ∧
    ∀ u : ℝ, W.column (C) u j i = W.column (C') u j i ∧
      W.defect (C) u i j = W.defect (C') u i j

private lemma prim (h : Bound (home S i) x A A' F F' k k' V V') (hS : S.patch.Branches S.kernel G) (hx : 120≤radiusB x) (j : Thing G f) :
    let W := windows S G x hx; let C := charter T x A F k; let C' := charter T x A' F' k'; Regard W (C V) (C' V') i j := by
  intro W C C'
  have hp := h.zone (p:=home S i) (k:=chargeR S.patch x) (s:=chargeD S.patch x)
    (by rw [separation_self]; unfold readN; omega) (by rw [separation_self]; unfold readH; omega)
  have he := product_scan T i j hS hp
  have h₁ := hp.zone (p:=home S i) (k:=peekR S.patch x) (s:=peekD S.patch x)
    (by rw [separation_self]; unfold chargeR careR; omega) (by rw [separation_self]; unfold chargeD careD; omega)
  refine ⟨Terrain.seenA T i j hS (h₁.zone (by rw [separation_self]; unfold peekR; omega)
    (by rw [separation_self]; unfold peekD; omega)), ?_, ?_, ?_⟩
  · unfold W C C'; rw [blend,blend]; exact he.1
  · ext l m
    have hi : l.val ∈ unitWin S x i := (wind ..).1 l.property
    have hv := aboutWin hi
    exact Terrain.seenA T l.val m.val hS (h₁.zone (by unfold peekR; omega) (by unfold peekD; omega))
  intro u; unfold W C C' CurvedGaussianJets.Windows.defect; rw [column,column]; exact ⟨coveredWin T _ _ hS u h₁, he.2 u⟩

private lemma ready (h : Bound (home S i) x A A' F F' k k' V V') (hS : S.patch.Branches S.kernel G) (hx : 120≤radiusB x) (y : Bool) :
    Regard (windows S G x hx) (stack T x A F k y V) (stack T x A' F' k' y V') i j := by
  have hg {i : Thing G f} (hd : Bound (home S i) x A A' F F' k k' V V') : Bound (home S i) x noHole noHole F F' k k' (1:Config G c) 1 :=
      ⟨fun _ _=> rfl,hd.tree,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,hd.branch,hd.point⟩
  cases y; exact prim (T:=T) (hg h) hS hx j; exact prim (T:=T) h hS hx j

variable {m : ℕ} {l l' : List (Directions G c)}
abbrev Deck (p : Run (Thing G f) m) (x : ℝ) (A A' : Stores S) (F F' : Forest S.ratio) (k k' : S.Choices) (V V' : Config G c) := ∀ i, Bound (home S (p i)) x A A' F F' k k' V V'




variable (hx : 120≤radiusB x) (hS : S.patch.Branches S.kernel G) (y : Bool)
include hx hS





-- ASSIGN supports: all occurrences of these entries and in b/mean/etc
-- can be charged before asking sectors. Not allowed to shrink them to
-- numerical range. `o` one parent home or a Wisps.down on coarse
-- orientation. Retain ALL coordinates in these balls inc even flag
-- plaquette and their endpoints.
omit hS in
lemma aboard (p : Run (Thing G f) m) (hv : readH S.patch x+12 ≤ 12*radiusB x) (hn : readN S.patch x+12 ≤ 2*radiusB x) :
    ∀ (i : Fin (m+1)) (o : Site c), separation (home S (p i)) o ≤ max (readH S.patch x+12) (readN S.patch x+12) →
    o ∈ dots (home S) (watch*rail x) p := by
  intro i o hi; refine dots_mem.mpr ⟨i,?_⟩; unfold watch Whole.rail; omega
end YM.PhysicalNext.OrderedAffine2B.Shelter
