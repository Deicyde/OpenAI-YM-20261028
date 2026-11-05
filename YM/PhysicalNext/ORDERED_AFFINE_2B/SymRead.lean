import YM.PhysicalNext.ORDERED_AFFINE_2B.CompactResolvent
import YM.PhysicalNext.ORDERED_AFFINE_2B.Streams
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymScope
import YM.PhysicalNext.ORDERED_AFFINE_2B.Tour

/-!
# Read full symmetric halos for scalar RUNs and short charges

Metadata compare on incidences entirely in X -- enables the enlarged,
symmetric footprint assignments instead of mid-edge conventions. Hards,
paths V,Y and direction arguments for all ordered slots actually read.
No claim to depend locally on histories generating these arrays;
they're fixed in statement, not Hilbert sequences. Charges including when
partial calm decision changes a far writer, don’t keep smaller supports
in those cases. `Table` compiled field dependence then if looked at from
Z consumers, include both actual Z incidences also in X (and their
location usage windows); don't count integrating anchors alone.  in these norms; still need fuller compulsory packets etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymRead
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores
open Next Next.SectorChange AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor Whole Matrix
open Further Further.CurvedGaussianJets Jets Tracks Completion SymRows SymWhole  
open AnalyticBridge AnalyticBridge.Covariance Terrain Shelter Scope  Trip Tour Footprint
open MeasureTheory SectorNext.Vacuum Push.SectorMeasure
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {d j m n : ℕ} {x : ℝ}
local notation "Coords" => Next.SectorChange.Prices

def old (X : Support c) (i : Bond c) := i.1∈X ∧ i.1+step i.2∈X
def wall (S : StepData c f) (X : Support c) (i : Bond f) := ∀ y∈Next.SectorChange.points S i,y∈X

structure Samples (X : Support c) {S : StepData c f} {F F' : Forest S.ratio} {A A' : Stores S}
    (k k' : S.Choices) (V V' : Config G c) (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F'))
    (z z' : Coords G (Bond f)) : Prop where
  core : ∀ i, old X i → V i=V' i
  front : ∀ i j, i.val.val=j.val.val → wall S X i.val.val → Y i=Y' j
  t1 : ∀ i, S.ratio.parent i ∈ X → F.up i=F'.up i
  t2 : ∀ i, S.ratio.parent i ∈ X → F.height i=F'.height i
  flags : ∀ i, i∈X → (i∈A.flags ↔ i∈A'.flags)
  costs : ∀ i, (∀ j ∈ touched i,S.ratio.parent j∈X) → (i∈A.costs ↔ i∈A'.costs)
  aisles : ∀ i, old X i → (i∈A.aisles ↔ i∈A'.aisles)
  k1 : ∀ i, i∈X → k.1 i=k'.1 i
  k2 : ∀ i, old X i → k.2 i=k'.2 i
  allZ : ∀ i : Thing G f, wall S X i.1 → z i=z' i


abbrev Covers (X : Support c) (o : Site c) (x : ℝ) := ∀ i, separation o i≤12*radiusB x → i∈X

variable {A A' : Stores S} {F F' : Forest S.ratio} {k k' : S.Choices} {T : Tube G S} {V V' : Config G c}
    {J : Tab} {σ : ℝ} {l l' : Word G c} {X : Support c} {o : Site c} {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')} {z z' : Coords G (Bond f)}
    (h : Samples X k k' V V' Y Y' z z') (he : readN S.patch x + 12 ≤ 2*radiusB x) (ht : readH S.patch x + 12 ≤ 12*radiusB x)

lemma asks {i : Bond c} (hx : Covers X o x) (hi : separation o i.1+1≤12*radiusB x) : old X i := by
  refine ⟨hx _ (by omega),hx _ ?_⟩; have he := Work.E03.sep_step i.1 i.2; have hh := separation_triangle o i.1 (i.1+step i.2); omega
lemma asks_edge {i : Bond f} (hx : Covers X o x) (hi : separation o (nearStart S i)+1≤12*radiusB x) : wall S X i := fun j hj=>hx _ (le_trans (separation_triangle o (nearStart S i) j) ((Nat.add_le_add_left (show separation (nearStart S i) j ≤ 1 from meetings _ hj) _).trans hi))

include h



include he ht
lemma compiles (hp : Covers X o x) : Archive S o (readN S.patch x) (readH S.patch x) k k' V V' Y Y' := by
  have ht' i (hx : separation o i≤readH S.patch x) : i∈X := hp _ (by omega)
  have he' {i} (hx : separation o (i : Bond c).1≤readH S.patch x) : old X i := asks hp (by omega)
  refine ⟨⟨⟨fun i hi=> h.core _ (asks hp (by omega)),fun i hi=> h.t1 _ (ht' _ hi),fun i hi=>h.flags _ (ht' _ hi),fun i hi=>h.aisles i (he' hi),?_ ,fun i hi=> h.k1 _ (ht' _ hi),fun i hi=>h.k2 _ (he' hi)⟩,
    fun i j hk hl=>h.front i j hk (asks_edge hp (by unfold nearStart; omega))⟩,
    fun i hi=> h.core i (asks hp (by simp only [id_eq] at hi; omega)),fun i hi=>h.t2 _ (ht' _ hi)⟩
  intro i hi; apply h.costs; intro j hj
  have hh := (Work.E04.parent_separation S.ratio i.1 j).trans (Nat.add_le_add_right (Work.E01.sep_touched i j hj) _)
  have hv := separation_triangle o (S.ratio.parent i.1) (S.ratio.parent j); exact hp _ (by omega)
omit he ht h


lemma covers_pair (p : Bond f) : Covers (both S p x) (nearStart S p) x := fun _ hi=>both_halo _ (by omega)

variable {hb : 120 ≤ radiusB x} (hS : S.patch.Branches S.kernel G) (a : Bool)
include hb hS he ht

-- l empty proofs restore all nonzero denominators; this is NOT
-- dropping any mask test, even for two linked labels of a singlet.




variable (hc : Ticketed T.low x) (q : Chi) (d' g : ℝ)
include hc

omit he ht hb hS hc in
lemma contracts (h : Archive S o (readN S.patch x) (readH S.patch x) k k' V V' Y Y') : Shared S o (Padded.allN S.patch x) (Padded.signalH (Padded.allN S.patch x) x) k k' V V' Y Y' := by
  apply h.numerical.zone
  · rw [separation_self]; unfold readN; omega
  · rw [separation_self]; unfold readH; omega



omit hb hS hc in
lemma watchIce (i : Bond f) (g : ℝ) (hX : Samples (both S i x) k k' V V' Y Y' z z') : iced x A F g i=iced x A' F' g i := ice_home (compiles hX he ht (covers_pair _)).numerical.team g
end YM.PhysicalNext.OrderedAffine2B.SymRead
