import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Collar
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Nil
import YM.Primitives.SMALL_FIELD_EXTERIOR.Window
/-!
 # Mandatory effect of THREE charge. Labels not in Militia.
 use at promise Φ even for clusters projecting. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Reserves
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p

abbrev owned (H : Cash W p a L₀ X o U T R) (i:Poet H): H.fragrances:= vintage i.val i.property
def booths (H : Cash W p a L₀ X o U T R) : Poet H ↪ H.fragrances:= ⟨owned H,enrollment⟩
lemma entry (z: H.ThinP) (h : Height.Solo z) (hp : ∀ x∈z.val, Beam.Pennies S x) (hv: H.shapeW z.val≤ B):
    ∃ b: Park c f, ∃ X: Seed H b,z=Heir b X:= by
  let k := disc S; let b:= z.val.preimage k k.injective.injOn; have hf i:i∈b↔k i∈z.val:=Finset.mem_preimage
  have he: hatch S b=z.val:= by
    ext y; constructor
    · intro hy; obtain ⟨x,hx,rfl⟩:=mem_map.mp hy; exact (hf _).1 hx
    intro hy; obtain ⟨i,rfl⟩:= (penned ..).1 (hp y hy); exact mem_map_of_mem k ((hf _).2 hy)
  refine ⟨b,⟨he.symm ▸ h.connected,?_,?_⟩, Subtype.ext he.symm⟩
  · have hx:= h.shares.2; rw [← he,hatch,card_map] at hx; exact hx
  intro i hi; have hu:= (hf i).1 hi
  refine (Nat.cast_le (α:=ℝ)).mp ?_ -- change
  refine le_trans ?_ hv; change _≤ Finset.sum _ _; apply le_trans _ (Finset.single_le_sum (fun v hv=> ?_) hu)
  swap
  · obtain ⟨w,hw⟩: v∈Set.range (disc S):= (penned ..).1 (hp v hv); subst v; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · change (Mint.verse R.path i:ℝ)≤_ + (exCharge T R (note i):ℝ); rw [Mint.balance T R i]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
lemma remnants (u:H.fragrances) (ht : ¬ Beam.lit H u) (U : Config G c) (hx : Blaze.March.stream H χ U u ≠0):
    u∈ Set.range (booths H):= by
  obtain ⟨he,hh⟩:= Beam.kids χ u U hx ht; have ht i:=he.enter.2.2 i
  have hd i : H.shapeW (u.2 i).val≤B:= (single_le_sum (f:=fun i=>H.shapeW (u.2 i).val) (fun i _=> H.positive_volume _) (mem_univ i)).trans (he.length.le.trans (by exact_mod_cast show Pressure.Stores.till p≤ B from Nat.div_le_self ..))
  choose b Hk Hv using fun i=> entry (u.2 i) (ht i) (hh i) (hd i)
  have hg: Stir H ⟨u.fst,b⟩:= by
    refine ⟨he.enter.2.1,Hk,fun h=>hx ?_⟩; unfold stream Gas.term; rw [show coefficient H.seam u.snd=_ from ?_,zero_mul,zero_div]
    apply Eq.trans _ h; apply movement; intro i j; rw [Hv,Hv]; apply or_congr; · exact ⟨seed_height _ _,fun h=>Subtype.ext (congr_arg (Mint.hatch S) h)⟩
    exact Iff.rfl
  refine ⟨⟨⟨u.fst,b⟩,hg⟩,?_⟩; change Sigma.mk u.fst _=u; congr 1; exact funext fun i=> (Hv i).symm

section shape
variable (v: Match.Alliance H I 1 0) (hr : R.path=R'.path) (he:v.units= Equiv.refl _)
-- supportP may differ in reg otherwise, so assume canonical matches from controller
variable (hp : H.supportP=I.supportP)
include hr hp
lemma estate (z: Park c f): Seed H z ↔ Seed I z:= by
  constructor
  · intro h; refine ⟨hp ▸ h.hot,h.sizes,fun i hi=>?_⟩; rw [← hr]; exact h.earns i hi
  intro h; refine ⟨hp.symm ▸ h.hot,h.sizes,fun i hi=>?_⟩; rw [hr]; exact h.earns i hi
lemma universal (z: Vines c f): Stir H z ↔ Stir I z:= by
  have hx:Meadow.ground H=Meadow.ground I:= funext fun i=> by unfold Meadow.ground Cash.unionP; rw [hp]
  exact ⟨fun h=>⟨h.small,(fun i=> (estate hr hp _).1 (h.each i)),hx ▸ h.moves⟩,fun h=>⟨h.small,(fun i=>(estate hr hp _).2 (h.each i)),hx.symm ▸ h.moves⟩⟩
def firstBatch : Poet H≃Poet I:=Equiv.subtypeEquiv (Equiv.refl _) (universal hr hp)
include he
lemma identifies (z:Poet H): v.furrow (booths H z)=booths I (firstBatch hr hp z):= by
  obtain ⟨⟨i,k⟩,hz⟩:=z; change Sigma.mk i _=Sigma.mk i _; congr 1; funext j; apply Subtype.ext; change v.units (hatch S _)= _; rw [he]; rfl
lemma holdings (i:H.fragrances): i∈Set.range (booths H) ↔ v.furrow i∈Set.range (booths I):= by
  let V:= firstBatch hr hp; constructor
  · rintro ⟨u,rfl⟩; exact ⟨V u,(identifies v hr he hp u).symm⟩
  rintro ⟨u,hu⟩; obtain ⟨u,rfl⟩:= V.surjective u; exact ⟨u,v.furrow.injective ((identifies v hr he hp u).trans hu)⟩
end shape
end YM.PhysicalNext.Repeat.Meadow
