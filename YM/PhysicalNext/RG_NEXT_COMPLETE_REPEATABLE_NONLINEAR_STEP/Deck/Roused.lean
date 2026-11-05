import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
/-! # A widened grouping of untreated kinetic contribution from paid Masks.
 Member bounds sufficient to monogram ANY restrictions integrated budget.
 Keep ALL such terms (even when entitled to other payment).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Mint
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D B:ℕ} {K : Teller G} {j : ℕ}

section life
abbrev Music (c f:Side) := Raw.Trans f ⊕ Raw.Trans f ⊕ Raw.Trans f ⊕ Miniature c f
def note (i:Music c f):Coat.LogIndex c f:= Sum.elim (.inl ∘ .inr ∘ .inl) (Sum.elim (.inl ∘ .inr ∘ .inr ∘ .inl) (Sum.elim (.inl ∘ .inr ∘ .inr ∘ .inr ∘ .inl) (.inr ∘ .inl))) i
abbrev album (S:StepData c f) (x:Music c f): Head S:= .inr (.inr (.inl (note x)))
lemma record : Injective (note (c:=c) (f:=f)):= by rintro (x|x|x|x) (y|y|y|y) <;>simp [note]
def disc (S:StepData c f): Music c f ↪ Head S:= ⟨album S, fun _ _ h=> record (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))⟩
lemma penned (S:StepData c f) (p:Head S): Beam.Pennies S p ↔ p ∈ Set.range (disc S):= by
  refine ⟨?_,?_⟩
  · rintro ⟨i,rfl,hi⟩; rcases i with i|i|i
    · rcases i with i|i|i|i|i
      · exact False.elim hi
      · exact ⟨.inl i,rfl⟩
      · exact ⟨.inr (.inl i),rfl⟩
      · exact ⟨.inr (.inr (.inl i)),rfl⟩
      rcases i with i|i <;> exact False.elim hi
    · exact ⟨.inr (.inr (.inr i)),rfl⟩
    exact False.elim hi
  rintro ⟨z,rfl⟩; refine ⟨note z,rfl,?_⟩; rcases z with z|z|z|z <;> trivial

def verse (T : PathData G) (z : Music c f): ℕ:= z.elim (atomCharge T.cubic) (Sum.elim (atomCharge T.quartic) (Sum.elim (atomCharge T.loop) (fun _=>0)))
lemma balance {S:StepData c f} (T:Tube G S) (R:RG.Rep G f) (z : Music c f): verse R.path z= exCharge T R (note z):= by rcases z with z|z|z|z<;> rfl
-- anchor tie field orientation BEFORE
abbrev soul (S : StepData c f) (i : Raw.Trans f) : Site c:= i.1.act (S.ratio.parent i.2.1)
def pace (S : StepData c f) (i : Music c f): Site c:=i.elim (soul S) (Sum.elim (soul S) (Sum.elim (soul S) (caption S)))
-- Radius uniform (K=650 etc eventually)
def width (m B n:ℕ):= (m*B+(6*B+3))+n
lemma batch_span (S : StepData c f) (A: ℕ→Atom G j) (m b n : ℕ) (hb:0<b) (g:Raw.Trans f) (hg:atomCharge A g ≤ n):
      soul S g ∈ atomFoot S.ratio m b A g ∧ atomFoot S.ratio m b A g ⊆ neighbors (Mint.width m b n) (soul S g):= by
  let x:= g.2.1; let y:= S.ratio.parent x; let p:= A g.2.2; let v:=p.footprint x
  have hp:x∈v:= mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩
  constructor
  · have he : y∈ enlargement S.ratio m b (inspected v):= halo_subset _ _ (mem_image_of_mem _ (show x∈RG.inspected v from (mem_union_left _ hp)))
    change soul S g∈ (enlargement _ _ _ (RG.inspected v)).image _; exact mem_image.mpr ⟨y,he,affine0 g.1 y⟩
  intro i hi; obtain ⟨z,hz,rfl⟩:= mem_image.mp hi; obtain ⟨w,hw,hz⟩:= halo_spec.mp (inspected_price S.ratio m b v hb hz); obtain ⟨w,h',rfl⟩:=mem_image.mp hw; apply (neighbors_mem ..).2
  have he : separation (S.ratio.parent x) (S.ratio.parent w)≤ n+1:= (Work.E04.parent_separation ..).trans (Nat.add_le_add_right ((Paths.where_slot x p.leg w ((Paths.atom_foot ..) ▸ (show w∈p.footprint x from h'))).trans hg) _)
  rw [affine0]; unfold soul; rw [separation_signed]; -- order see
  apply (separation_triangle y (S.ratio.parent w) z).trans; unfold Mint.width; nlinarith only [hb,he,hz]
lemma centered (m b n:ℕ) (hb:0<b) (x : Music c f) (S:StepData c f) (T:Tube G S) (R:RG.Rep G f) (he:verse R.path x ≤ n) : pace S x∈ areas R T m b (disc S x) ∧ areas R T m b (disc S x) ⊆ neighbors (Mint.width m b n) (pace S x):= by
  rcases x with x|x|x|x
  · exact batch_span S R.path.cubic m b n hb x he
  · exact batch_span S R.path.quartic m b n hb x he
  · exact batch_span S R.path.loop m b n hb x he
  refine ⟨?_, (packed S hb x).trans (show neighbors ((m+1)*b) (caption S x)⊆neighbors _ (caption S x) from fun i hi=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp hi).trans (by unfold Mint.width; nlinarith)))⟩
  rcases x with x|x|x
  · exact (neighbors_mem ..).mpr (separation_self _ ▸ Nat.zero_le _)
  · exact Itinerary.city S ..
  exact Itinerary.city S ..
end life
end YM.PhysicalNext.Repeat.Deck.Mint
