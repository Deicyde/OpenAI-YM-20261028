import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Sieve
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Quips
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Nil
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Tuft
import YM.Primitives.SMALL_FIELD_EXTERIOR.Shed
/-! # Young part charge per support position. Fits Tran. Need actual Receipt for *everyone*
    before using arc. No characteristic-bound equality guessed.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ}
variable {X : ConnectedActivityE6.Target G K} {o: Target.Order G W} {χ : Chi}
section coin
variable {S:StepData c f} {T:Tube G S} {R:RG.Rep G f} {H : Cash W p a L₀ X o U T R}
def vote (z:Poet H) := ((Meadow.pasture H z.val).card:ℝ)⁻¹
def offer (χ:Chi) (z:Poet H) (V:Config G c) := -(vote z) * stream H χ V (vintage z.val z.property)
def echoing (H:Cash W p a L₀ X o U T R) (χ:Chi) (k:ℕ) (x:Site c) (V:Config G c):= ∑ i∈(Meadow.calendar H k).filter (fun i=>x∈Meadow.pasture H i.val), Meadow.offer χ i V
end coin
section roll
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (Tq : T'=Deck.re T) (hp:R'.path=R.path) (ha:R'.p= R.p) (hz:R'.beta=R.beta) (x : Site C) (hX:4*roomSize X.halo (radiusB p)<c.val) {b ℓ : ℕ}
    {C' d z T'' A B r V' u s₁ a' b' c' d' e' D Z q' :ℝ} -- B conflicts
    (N : Captain I b C' d z T'' A B r V' u m χ) (N' : Captain I' j s₁ a' b' c' d' e' D Z q' ℓ χ) -- note args
    (f' : Config G c) (hV: RG.flags (Pressure.temp p) f'= ∅)
local notation "R₀" => radiusB p
local notation "D'" => roomSize X.halo R₀
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include hC he Tq hp ha hz hX N N' hV
lemma due (i : Poet I') (j:Poet I) (heq: j.val=forward (L) i.val) (hr:x∈Meadow.pasture I' i.val):
     offer χ i ((L).low.links f')=offer χ j f':= by
  let f:=f'; let F:=(L).low.links f; let z:=i.val; let w:= j.val
  have hc: RG.flags (Pressure.temp p) F=∅:= by ext i; rw [show i∈RG.flags (Pressure.temp p) F↔_ from Deck.flagged hC f' i (show c.val>4 from (by have hv:= I.laws.data.room.buys; omega)) (Pressure.temp p),hV]; simp -- adjust
  have hf:(Meadow.pasture I w).card= (Meadow.pasture I' z).card:= by
    have hy:=entered i.property x hr; unfold w; rw [heq, pitchRoll hC he (I:=I) (I':=I') hp]; exact card_image_of_injOn ((garden hC x (show 2* D' < c.val from (by omega))).mono (Finset.coe_subset.mpr hy))
  let C0:= vintage z i.property; let C1:= vintage w j.property; have ht : stream I χ f C1= I.trainedPool χ f C1:= Eq.symm ((congr_fun (N.permitAverage C1).2.2.2.1 f).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hV]; simp)))
  have hx : stream I' χ F C0= I'.trainedPool χ F C0 := Eq.symm ((congr_fun (N'.permitAverage C0).2.2.2.1 F).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hc]; simp)))
  have hh : 2*D' < c.val:=by omega
  suffices h : I'.trainedPool χ F C0= I.trainedPool χ f C1 by unfold offer; rw [ht,hx,h,show Meadow.vote j=Meadow.vote i from (by unfold Meadow.vote; rw [show (Meadow.pasture I j.val).card=_ from hf])]
  obtain ⟨j,Hj⟩:=j; dsimp only at heq; subst j
  unfold Cash.trainedPool Gas.term
  apply congr_arg₂ HDiv.hDiv _ rfl
  apply congr_arg₂ HMul.hMul
  · exact (mana i.property).symm.trans ((receipts hC he (I:=I) x hp z hh (entered i.property x hr) i.property.each).trans (mana Hj))
  apply prod_congr rfl; intro j _
  have hy' := rings (h:=h) hC he x i.val i.property hr hh j
  exact Mint.meetups hC he I' I Tq hp ha hz x D' (by omega) hy' (engirds x i.val i.property hr j) (i.property.each j).earns f χ hV (i.property.each j).hot (Hj.each j).hot

lemma arranges (k:ℕ) : Meadow.echoing I' χ k x ((L).low.links f')= Meadow.echoing I χ k x' f':= by
  let T x i:= x∈Meadow.pasture I' i
  let P:=L; let u:=(Meadow.calendar I' k).filter (fun i=> x∈Meadow.pasture I' i.val); let v:=(Meadow.calendar I k).filter (fun i=> x'∈Meadow.pasture I i.val)
  have hm : 2*(D')<c.val:= by omega
  have hh {i : Poet I'} (hi:i∈u) := stitches hC he (I:=I) (I':=I') x hp i.val i.property (mem_filter.mp hi).2 hm
  let f (i: Poet I') (hi:i∈u): Poet I:=⟨forward P i.val, (hh hi).1⟩
  have hv i: held (verse_down P i)= held i := by rcases i with i|i|i|i <;> rfl
  have ht (z:Vines C F): (∀ j,z.snd j⊆tuck k) ↔ (∀ j,(forward P z).snd j⊆ tuck k):= by
    constructor
    · intro h j i hi; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; rw [pocket,hv,← pocket]; exact h _ (by assumption)
    intro h j i hi; rw [pocket, ← hv,← pocket]; exact h _ (mem_image_of_mem (verse_down P) (show i∈z.snd j from hi))
  apply Finset.sum_bij f (fun i hi=> ?_) (fun i hi j hj heq=> ?_) (fun b hb=>?_) (fun i hi=>?_)
  · exact mem_filter.mpr ⟨(tunes _ k).mpr ((ht _).1 ((tunes i k).1 (mem_filter.mp hi).1)), (hh hi).2⟩
  · exact Subtype.ext (inquire hC he x j.val i.val j.property i.property (mem_filter.mp hj).2 (mem_filter.mp hi).2 hm (congr_arg Subtype.val heq))
  ·
    obtain ⟨y,hy,hY,h⟩ := Meadow.returns hC he x hp b.val (I:=I) (I':=I') b.property (mem_filter.mp hb).2 (show 2*(D'+Mint.width X.halo R₀ R₀)<c.val from by unfold roomSize at *; omega)
    have hk : (⟨y,hy⟩ : Poet I')∈u:= mem_filter.mpr ⟨(tunes _ _).2 ((ht _).2 (h.symm ▸ (tunes _ _|>.1 (mem_filter.mp hb).1))),hY⟩; exact ⟨_,hk,Subtype.ext h⟩
  exact due hC he Tq hp ha hz x hX N N' f' hV i (f i hi) rfl (mem_filter.mp hi).2
end roll
end YM.PhysicalNext.Repeat.Meadow
