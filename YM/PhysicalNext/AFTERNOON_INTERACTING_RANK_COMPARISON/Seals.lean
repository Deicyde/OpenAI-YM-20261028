import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pictures
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Tableau

/-!
# Keep all integrity envelopes under THIS chosen chart

Allocate *one* extra inflation of tolerance gain per club, even with multiple
compulsories/ W partners. Crucial that p inputs before the clustering. See
Conditions. Here applies them after enlisting every possible probe. Never assumes
Stencil from a neighbor test once packets intersect. No K via linked cost to W norm or
two normalized densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Filter
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ σ w : ℝ} {L : Lantern G S} {F : Orchard S} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι κ α : Type} [Fintype W] [DecidableEq W] {θ : W → Site f} {u : W → Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (K : κ→ Lifted G θ R.p.threshold) (H : α → Flake S G x L.park u R'.p.threshold)
    (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ)
    {r : W → ℝ} {l m : ℝ}
local notation "Q" => picture R R' p K H ht hs hv
lemma stationed (s : Club Q) (i) (hi:i∈s.val.toLeft.toLeft) (V) (he : validArea Q s V) :
    (p i).zone ∩ flags R'.p.threshold V=(p i).down ∧
    ∀ k:Streak L.park,Nearby (p i).zone V V (stapled x (p i).data V) (stapled x (glow Q s.val) V) k k := by
  obtain ⟨hz,hf,hg⟩:= on_film R R' p K H ht hs hv s.val; let B:= s.val.toLeft.toLeft
  have Hp : (p i).zone ⊆ zone Q s := fun j hp=> Finset.mem_biUnion.mpr ⟨.inl (.inl i),mem_toLeft.mp (mem_toLeft.mp hi),hp⟩
  have ha: (B:Set _).PairwiseDisjoint (fun i=>(p i).zone):= (hg.1 s.property.2.1).1
  have hB:zone Q s∩flags R'.p.threshold V=B.biUnion fun i=>(p i).down:= he.trans hz
  constructor
  · ext k; constructor
    · intro he; obtain ⟨hr,hv⟩:= Finset.mem_inter.mp he; obtain ⟨j,hj,hs⟩:=mem_biUnion.mp (hB ▸ (mem_inter.mpr ⟨Hp hr,hv⟩ : k∈zone Q s∩flags R'.p.threshold V))
      rcases eq_or_ne j i with g|g; exact g ▸ hs
      exact (Finset.disjoint_left.mp (ha hj hi g) ((p j).sent hs) hr).elim
    intro he; exact mem_inter.mpr ⟨(p i).sent he,(mem_inter.mp (hB.symm ▸ (mem_biUnion.mpr ⟨_,hi,he⟩:k∈ B.biUnion fun i=>(p i).down))).2⟩
  intro k; let D:= (B.erase i).sup fun i=>(p i).data
  rw [show glow Q s.val=(p i).data⊔D by rw [hf]; symm; unfold D; rw [← Finset.sup_insert (f:=fun i=>(p i).data)]; rw [insert_erase hi]]
  apply towards
  have hl (g : ι→vouchers S) (s : Finset ι) : wards (s.sup g)= s.biUnion fun j=> wards (g j):= by
    induction s using Finset.induction_on with
    | empty=>ext; simp [wards]
    | insert i s h ih=>
      rw [biUnion_insert,← ih,sup_insert]
      generalize (g i)=u;generalize s.sup g=v
      unfold wards; change (u.1∪v.1).biUnion (startPos S) ∪ (u.2∪v.2).biUnion pinPos=_
      rw [Finset.union_biUnion, Finset.union_biUnion]; ac_rfl
  unfold D; rw [hl]; refine disjoint_left.mpr fun j hj hh=> ?_
  obtain ⟨z,hz,h⟩:= mem_biUnion.mp hh; exact Finset.disjoint_left.mp (ha hi (mem_erase.mp hz).2 (mem_erase.mp hz).1.symm) hj ((p z).contains h)
-- Weighted stage amplitude (untouched diagnostics). Works for Empty.
def stroke (p : PaintCan S G x F u τ) (r : W→ℝ) : Shader G S x F ℝ := fun A k U z=> Poly.toll r p.hues*‖p.lamp A k U z‖
lemma stroke_nonneg (hp : ∀ i,0<r i) (p : PaintCan S G x F u τ) A k U z : 0 ≤ stroke p r A k U z := mul_nonneg (Poly.worth hp p.hues).le (norm_nonneg _)
lemma earmark {X : ι→ PaintCan S G x F u τ} (b : Finset ι) (h : enlist X b) (V : Config G c) A k z : Poly.toll r (fires X b)*‖stage X b A k V z‖=
    ∏ i∈b, stroke (X i) r A k V z := by
  unfold stroke; rw [billed_flux X b h r,stage,norm_prod, Finset.prod_mul_distrib]
lemma lowstroke {y : ℝ} (x : W → Site c) (A : Stores S) (p : Zest G S y F τ) k V z : stroke (lowTone x p) r A k V z=‖p.weight A k V z‖:=by simp [stroke, Poly.toll, lowTone,Glyph.quiet,Census.quiet]

abbrev Gathered (cool : α→Prop) (s : Club Q) := s.val.toLeft=∅ ∧ ∀ i ∈ s.val.toRight,cool i
def bid (f : ι → ℝ) (g : κ → ℝ) (j : α → ℝ) : Spectrum ι κ α→ℝ := Sum.elim (Sum.elim f g) j

lemma earning_base (s : Club Q) (V : Config G c) (A : Stores S) (k : Streak L.park) (he : A=stapled x (glow Q s.val) V) (hp : validArea Q s V)
    (z : ι →ℝ) (hg : ∀ i, (p i).Wares T m l (z i)) (hm : 1 ≤ m) (hl : 1 ≤ l):
    let X:=s.val.toLeft.toLeft; let v(y : RoomView A x k.wood G):=∏ i∈X,stroke (lowTone u (p i)) r A k V y
    let q:=∏ i∈X, (p i).infl m l
    Integrable v (viewer T A x k.wood k.tag V) ∧ q * (∫ y,v y ∂viewer T A x k.wood k.tag V) ≤ ∏ i∈X,z i:= by
  subst A; intro B v q
  let a:= stapled x (glow Q s.val) V; let μ := viewer T a x k.wood k.tag V
  let Z (i:ι) : Shader G S x L.park ℝ:= fun A k V y=> ‖(p i).weight A k V y‖
  have hsx i:Sees (Z i) (p i).zone (p i).down.Nonempty R'.p.threshold:= (p i).follows.comp (‖·‖) measurable_norm
  let g i:= ∫ y, Z i a k V y ∂μ
  have hb i (hi:i∈B): Integrable (Z i a k V) μ ∧ (p i).infl m l*g i ≤ z i:= by
    obtain ⟨hP,hB⟩:= stationed R R' p K H ht hs hv s i hi V hp
    obtain ⟨hu,hE⟩:= Zest.Wares.arise _ (hg i) hm hl ht V (position ..) hP k (hB k)
    exact ⟨hu.norm,hE⟩
  have hX : (B:Set _).PairwiseDisjoint (fun i=>(p i).zone):= ((on_film R R' p K H ht hs hv s.val).2.2.mp s.property.2.1).1
  obtain ⟨hi,h2⟩:= peer_beams (fun i:↥B=>(p i).zone) (Z ∘ Subtype.val) (fun i=>hsx _) ht (fun i j hp=> hX i.property j.property (mt Subtype.ext hp)) (position ..) k (fun i=>(hb i i.property).1)
  have heV y:v y=∏ i:↥B, Z i a k V y:= by rw [show v y=∏ i∈B,Z i a k V y from Finset.prod_congr rfl fun i _ =>lowstroke ..,← Finset.prod_coe_sort B]
  refine ⟨hi.congr (Eventually.of_forall fun _=> (heV _).symm),?_⟩
  rw [show (∫ y,v y ∂_) =∏ i∈B,g i by rw [← Finset.prod_coe_sort B]; exact (integral_congr_ae (Eventually.of_forall heV)).trans h2, show q*(∏ i ∈B,g i)=∏ i∈B, (p i).infl m l*g i from (Finset.prod_mul_distrib ..).symm]
  apply Finset.prod_le_prod; intro i _; exact mul_nonneg (zero_le_one.trans ((p i).infl_one hm hl)) (integral_nonneg fun _=> norm_nonneg _)
  exact fun i hi=> (hb i hi).2
end YM.PhysicalNext.InteractingRank.Display
