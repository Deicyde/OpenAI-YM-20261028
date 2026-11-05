import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.TwoWindows
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Watches
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Reading
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Projection
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Tags
import YM.Extra.ITERATION_NO_LOSS.Mechanism
import YM.Further.FREE_COVARIANCE_KP.KP.Gem
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Images
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Orchards
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds





/-!
# Point stencil for Rank marks in the native sector chart

Real microsupport criteria: uses Neighborhood data buffered in the
mask. Keep both V data including flags wherever read by any
calls, and tag/root selectors; prove even A,B with different trunks
but drawing the same roots in X give the same comparison there. Don't
assume local independence as a combinatorial axiom. Obtain probes on
the actual `viewer` laws.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Marker Value
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
    AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.RelativeLogdet AnalyticBridge.Sharp.Tags
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {X X' : Support c} {x : ℝ} {U V : Config G c} {A B : Stores S}
    {F : Forest S.ratio} {T : Tube G S} {O : Orchard S} {k k' : Streak O}

structure Nearby (X : Support c) (U V : Config G c) (A B : Stores S)
    (k k' : Streak O) : Prop where
  branch : Agrees X U V
  freezes (p : Site c) : Shields X p 8 → (p∈A.place ↔ p∈B.place)
  keys : Synchronized X k.tag k'.tag
  stones : Set.EqOn k.roots k'.roots ↑X
  aisles (p : Bond c) : ¬ Disjoint (pinPos p) X → (p ∈ A.aisles ↔ p ∈ B.aisles)
  costs (p : Cell f) : ¬ Disjoint (startPos S p) X → (p∈A.costs ↔ p∈B.costs)

namespace Nearby
lemma mono (h : Nearby X U V A B k k') (H : X' ⊆ X) : Nearby X' U V A B k k' :=
  ⟨agrees_mono h.branch (by exact_mod_cast H),fun p e => h.freezes p (fun s g=> H (e s g)), ⟨fun i hv => h.keys.1 i (H hv),fun i hv hu=>h.keys.2 i (H hv) (H hu)⟩, h.stones.mono (by simpa only [Finset.coe_subset]),
    fun i hi=> h.aisles i (fun he=>hi (Disjoint.mono_right H he)),fun p hp=>h.costs p (fun he=>hp (Disjoint.mono_right H he))⟩
lemma back (h : Nearby X U V A B k k') : Nearby X V U B A k' k :=
  ⟨fun i hi hs=> (h.branch i hi hs).symm, fun p hp=>(h.freezes p hp).symm,
    ⟨fun i hv=>(h.keys.1 i hv).symm,fun i h1 h2=> (h.keys.2 i h1 h2).symm⟩,h.stones.symm,
    fun i hi=>(h.aisles i hi).symm,fun i hi=>(h.costs i hi).symm⟩
lemma tickets (h : Synchronized X k.tag k'.tag) (H : Set.EqOn k.roots k'.roots ↑X) : Nearby X U U A A k k' := ⟨fun _ _ _=>rfl,fun _ _=>Iff.rfl,h,H,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩
lemma same (X : Support c) (U : Config G c) (A : Stores S) (k : Streak O) : Nearby X U U A A k k := Nearby.tickets ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩ (Set.eqOn_refl ..)
lemma shutter (h : Nearby X U V A B k k') {Y : LinkArray G (Frozen A x k.wood)} {Y' : LinkArray G (Frozen B x k'.wood)}
    {o : Site c} {s : ℕ} (H : Shields X o (s+1+10*radiusB x+8))
    (hY : ∀ i j,separation o (S.ratio.parent i.val.val.1) ≤ s → i.val.val=j.val.val → Y i=Y' j) :
    PatchReads.Scan S x o s A B k.wood k'.wood k.tag k'.tag U V Y Y' := by
  let d := s+1+10*radiusB x+8
  have hp (e : Edge (Site c)) (hv : separation o e.1 ≤ s) : e.1∈X ∧ e.1+step e.2∈ X:= by
    have hx := (separation_triangle o e.1 (e.1+step e.2)).trans (Nat.add_le_add hv (Work.E03.sep_step ..))
    exact ⟨H _ (by omega), H _ (by omega)⟩
  exact ⟨fun p he=> h.freezes p (H.shift (by omega)),fun i hi=>h.keys.1 i (H i (by omega)),fun i hi=>h.keys.2 i (hp i hi).1 (hp i hi).2,
    fun i hi => O.crowns i (h.stones (H _ (by omega))),fun i hi=> h.branch i (hp i hi).1 (hp i hi).2, fun i j he hf=>hY i j he hf ⟩
end Nearby

def lumen (S : StepData c f) (x : ℝ) (X : Support c) (i : Bond f) := Shields X (S.ratio.parent i.1) (20*radiusB x+16)

-- conservative halo for these readings
abbrev Unveiled (X : Support c) (A : Stores S) (x : ℝ) (F : Forest S.ratio) := {i : Frozen A x F // lumen S x X i.val.val}
abbrev Chargeable (G : Gauge) (X : Support c) (A : Stores S) (x : ℝ) (F : Forest S.ratio) := {i : In (G:=G) x A F // lumen S x X i.1.val.val}
namespace Nearby
variable (h : Nearby X U V A B k k')
include h in
lemma lumen_scan {i : Bond f} {x : ℝ} (hb : lumen S x X i) :
    PatchReads.Scan S x (S.ratio.parent i.1) (radiusB x) A B k.wood k'.wood k.tag k'.tag U V 1 1 := h.shutter (hb.shrink (by omega)) (fun _ _ _ _=>rfl)
include h in
lemma trunk_iff (i : Bond f) (H : S.ratio.parent i.1 ∈ X) : i∈k.wood.trunks ↔ i∈k'.wood.trunks:= O.crowns _ (h.stones H)
include h in
lemma frozen {i : k.wood.Free} (hb : lumen S x X i.val) {j : k'.wood.Free} (he : i.val=j.val): chill A x k.wood i ↔ chill B x k'.wood j := (h.lumen_scan hb).freeze_same (by simp) he
include h in
private def glows' (i : Unveiled X A x k.wood) : Unveiled X B x k'.wood := ⟨⟨⟨i.val.val.val,mt (h.trunk_iff _ i.property.center).mpr i.val.val.property⟩,(h.frozen i.property rfl).1 i.val.property⟩,i.property⟩
include h in
private def charges' (i : Chargeable G X A x k.wood) : Chargeable G X B x k'.wood :=
    ⟨(⟨⟨i.val.1.val.val,mt (h.trunk_iff _ i.property.center).mpr i.val.1.val.property⟩, fun he=>i.val.1.property ((h.frozen i.property rfl).2 he)⟩,i.val.2),i.property⟩

def glows : Unveiled X A x k.wood ≃ Unveiled X B x k'.wood := ⟨glows' h,glows' h.back,fun _=>rfl,fun _=> rfl⟩
def charges : Chargeable G X A x k.wood ≃ Chargeable G X B x k'.wood := ⟨charges' h,charges' h.back,fun _=>rfl,fun _=>rfl⟩

lemma paid_here (ht : PatchReads.Ready T x) (i : Chargeable G X A x k.wood) (j : Chargeable G X A x k.wood) :
    palette T A k.wood k.tag x U .endpoint i.val j.val = palette T B k'.wood k'.tag x V .endpoint (h.charges i).val (h.charges j).val := by
  simp_rw [← Q_endpoint]; exact PatchReads.fog_eq ht ((h.lumen_scan i.property).lower (by omega)) rfl rfl
end Nearby
private lemma emptied (Z : Tube G S) (h : Disjoint X X') (i : Chargeable G X A x F) (j : Chargeable G X' A x F) (k : S.Choices) (V : Config G c) :
    palette Z A F k x V .endpoint i.val j.val=0:= by
  rw [← Q_endpoint]; apply fog_zero; intro hp
  have hi := PatchReads.ball_member hp
  let v := front A F j.val
  exact Finset.disjoint_left.mp h ((show lumen S x X _ from i.property) v (le_trans hi (by omega))) j.property.center

abbrev Cupful (G : Gauge) (X : Support c) (A : Stores S) (x : ℝ) (F : Forest S.ratio) := LinkArray G (Unveiled X A x F) × Gaussian.Vec (Chargeable G X A x F)

def closeup (T : Tube G S) (X : Support c) (A : Stores S) (x : ℝ) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) : Measure (Cupful G X A x F) :=
    (piHaar G (Unveiled X A x F)).prod (Gaussian.cloud ((palette T A F k x V .endpoint).submatrix (fun i: Chargeable G X A x F => i.val) (fun i : Chargeable G X A x F => i.val)))
instance (V : Config G c) (k : S.Choices) : IsProbabilityMeasure (closeup T X A x F k V):=by unfold closeup; infer_instance

def amplify (h : Nearby X U V A B k k') (b : RoomView B x k'.wood G) : Cupful G X A x k.wood :=
    (fun i => b.1 (h.glows i).val, fun i => b.2 (h.charges i).val)

def nearby (X : Support c) (b : RoomView A x F G) : Cupful G X A x F := (fun i=> b.1 i.val, fun j=> b.2 j.val)

lemma beam (ht : PatchReads.Ready T x) (h : Nearby X U V A B k k')
    (hc : (palette T B k'.wood k'.tag x V .endpoint).PosDef) : MeasurePreserving (amplify h) (viewer T B x k'.wood k'.tag V) (closeup T X A x k.wood k.tag U) := by
  have hg : MeasurePreserving (fun u : LinkArray G (Frozen B x k'.wood)=> fun i:Unveiled X A x k.wood => u (h.glows i).val) _ _:=
    AnalyticBridge.Sharp.Projection.pi_projection G.probHaar (⟨_,Subtype.val_injective.comp (Nearby.glows h).injective⟩ : _ ↪ _)
  let C := palette T A k.wood k.tag x U .endpoint; let D := palette T B k'.wood k'.tag x V .endpoint
  have he : C.submatrix (fun i:Chargeable G X A x k.wood=>i.val) (fun j:Chargeable G X A x k.wood=>j.val)=
      D.submatrix (fun i:Chargeable G X A x k.wood=>(h.charges i).val) (fun j:Chargeable G X A x k.wood=>(h.charges j).val):=Matrix.ext (Nearby.paid_here h ht)
  have hs:= AnalyticBridge.Sharp.Projection.cloud_projection hc (fun i:Chargeable G X A x k.wood => (h.charges i).val)
  unfold closeup; rw [he]; exact hg.prod hs
lemma beam_family {ι : Type} [Fintype ι] (X : ι→ Support c) (h : Pairwise (fun i j => Disjoint (X i) (X j)))
    {k : S.Choices} (hp : (palette T A F k x U .endpoint).PosDef) : MeasurePreserving (fun a : RoomView A x F G => fun i => nearby (X i) a) (viewer T A x F k U) (Measure.pi (fun i=>closeup T (X i) A x F k U)) := by
  let e (i:ι) : Unveiled (X i) A x F ↪ Frozen A x F:=⟨Subtype.val,Subtype.val_injective⟩
  have hh i j (he : i ≠ j) (a b) : e i a ≠ e j b := by
    intro hx
    have hA := a.property.center;have hB := b.property.center
    change a.val=b.val at hx
    rw [hx] at hA
    exact Finset.disjoint_left.mp (h he) hA hB
  exact AnalyticBridge.Sharp.Projection.localizes G.probHaar hp e hh (fun i (u:Chargeable G (X i) A x F)=>u.val)
    (fun i j hi a b=> emptied T (h hi) a b k U) _ (fun _=>rfl)
end YM.PhysicalNext.InteractingRank
