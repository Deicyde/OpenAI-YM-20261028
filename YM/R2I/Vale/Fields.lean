import YM.R2I.Vale.Cap
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Coset
/- Widen verified Meadow Vista,Span,Tuft,Coset proof to arbitrary order Θ. Native radius remains, connectivity & symmetry BOTH. -/
noncomputable section

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' : ℕ} {K : Teller G}

variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
-- includes length/ground but not val bills
local notation "B" => radiusB p
variable (hp:R'.path=R.path)
include hC he hp I I'
lemma seed_orderR (p:Park C F) (heq:Set.InjOn (verse_down (L)) p) (hh:Set.InjOn ((L).low.cut) (Meadow.ground I' p)) : SeedR Θ₃ I' p ↔ SeedR Θ₃ I (wrappers (L) p):= by
  have he' := preheated (verse_down (L)) (I'.supportP ∘ disc (Y)) (I.supportP ∘ disc (S)) p (L).low.cut (fun i=> (contempt hC he (I:=I) (I':=I') hp i).2) heq (by rw [footland] at hh; exact hh)
  have ht := card_image_of_injOn heq
  have hf {c f'} {W₁:StepData c f'} (p: Finset (Music c f')) (g: Head W₁→Support c): Ac.Spark g (hatch W₁ p) ↔Ac.Spark (g ∘ disc W₁) p:= by
    unfold hatch; rw [Finset.map_eq_image]; exact (sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
  have ha : Ac.Spark I'.supportP (hatch _ p) ↔Ac.Spark I.supportP (hatch _ (wrappers (L) p)):= (hf p _).trans ((show Ac.Spark (I'.supportP ∘ disc (Y)) p ↔ Ac.Spark (I.supportP ∘ disc (S)) (wrappers (L) p) from (by convert! he' using 2; unfold wrappers; congr; exact Subsingleton.elim _ _)).trans (hf (wrappers (L) p) I.supportP).symm)
  constructor
  · intro h; refine ⟨ha.1 h.hot,ht ▸ h.sizes,fun i hi=>?_⟩; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; exact (contempt hC he hp (I:=I) (I':=I') i).1 ▸ h.earns _ (by assumption)
  intro h; refine ⟨ha.2 h.hot,ht ▸ h.sizes,fun i hi=> (contempt hC he hp (I:=I) (I':=I') i).1.trans_le (h.earns _ (mem_image_of_mem _ hi))⟩
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
local notation "B" => radiusB p
local notation "D" => roomSizeR Θ₃ X.halo B
local notation "t" => Mint.width X.halo B B
variable (x : Site C)
include hC he
omit hC he in
lemma engirdsR (v:Vines C F) (hv:StirR Θ₃ I' v) (hz:x∈Meadow.pasture I' v) (i): Meadow.ground I' (v.2 i)⊆neighbors D x:= (your (H:=I') (z:=v) i).trans (enteredR hv x hz)
lemma inquireR (v u: Vines C F) (hv:StirR Θ₃ I' v) (hu:StirR Θ₃ I' u) (hx:x∈Meadow.pasture I' v) (hk:x∈Meadow.pasture I' u) (hC':2 * D < c.val) (h:forward (L) u=forward (L) v): u=v:= by
  have he : u.fst=v.fst:= congr_arg (fun i : Vines c f=> i.fst) h; rcases v with ⟨n,v⟩; rcases u with ⟨m,u⟩; dsimp only at he; subst m
  unfold forward at h; injection h with h hh; congr 1; funext i; let V:=v
  apply genitive (Q:=Q) hC (by assumption) x hC' _ _ (congr_fun hh i)
  · intro j hk'; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,u⟩) i|>.trans (enteredR hu x hk)) (centersR (hu.each i) hk'))
  intro j hk; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,v⟩) i|>.trans (enteredR hv x hx)) (centersR (hv.each i) hk))
lemma ringsR (v:Vines C F) (hv:StirR Θ₃ I' v) (hx:x∈ Meadow.pasture I' v) (hp:2*D<c.val) (i) : Set.InjOn (verse_down (L)) (↑(v.2 i) : Set (Music C F)):= by
  have hI:= engirdsR x v hv hx i
  intro y hy z hz he; exact (nest_mint (Q:=Q) (hC:=hC) (he:=by assumption) (h:=h) (H:=H)).point hp x y z ((neighbors_mem ..).1 (hI (centersR (hv.each i) hy))) ((neighbors_mem ..).1 ((your (H:=I') (z:=v) i).trans (enteredR hv x hx) (centersR (hv.each i) hz))) he
variable (hp : R'.path=R.path)
include hp I I'
lemma receiptsR (z:Vines C F) (hZ:2*D'< c.val) (hz: Meadow.pasture I' z⊆ neighbors D' x) (hu: ∀ i,SeedR Θ₃ I' (z.2 i)) :
    coefficient (blocked (Meadow.ground I')) z.2=coefficient (blocked (Meadow.ground I)) (forward (L) z).2:= by
  apply movement; intro i j; let f:=Meadow.ground I'; have hf i: f (z.2 i)⊆neighbors D' x := (your (H:=I') (z:=z) _).trans hz
  have hm i s (hh:s∈z.2 i):separation x (pace Y s) ≤ D':= (neighbors_mem ..).1 (hf i (centersR (hu i) hh)); have hv i: ((Meadow.ground I ∘ (forward (L) z).2) i)=(f (z.2 i)).image (L).low.cut:= pitched hC he hp _
  have hy i : Meadow.ground I ((forward (L) z).2 i)= (f (z.2 i)).image (L).low.cut:= hv i
  apply or_congr; · exact ⟨fun hx=>congr_arg (wrappers (L)) hx,genitive hC he x hZ (hm i) (hm j)⟩
  unfold Ac.meets; rw [hy,hy]; constructor
  · rintro ⟨v,h,hx⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ hx⟩
  rintro ⟨v,h',hx⟩; obtain ⟨z,hv,hj⟩:=mem_image.mp h'; obtain ⟨y,hy,hr⟩:=mem_image.mp hx
  -- compare labels via hZ; priority
  exact ⟨z,hv, ((garden hC x hZ) (hf _ hy) (hf _ hv) (hr.trans hj.symm)) ▸ hy⟩
lemma stitchesR (z:Vines C F) (hv:StirR Θ₃ I' z) (hk:x∈Meadow.pasture I' z) (hH:2 * D< c.val) : StirR Θ₃ I (forward (L) z) ∧ (L).low.cut x∈Meadow.pasture I (forward (L) z):= by
  have hS:= enteredR hv x hk
  refine ⟨⟨hv.small,fun i=> ?_,((receiptsR (I':=I') hC he x (I:=I) hp z hH hS hv.each) ▸ hv.moves)⟩,?_⟩
  · apply (seed_orderR (I:=I) (I':=I') hC he hp _ (ringsR hC he x z hv hk hH i) ((garden hC x hH).mono _)).1 (hv.each i)
    exact coe_subset.mpr ((your (z:=z) i).trans hS)
  rw [pitchRoll (I:=I) (I':=I') hC he hp z]; exact mem_image_of_mem _ hk
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' m: ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (x:Site C) (hp:R'.path=R.path)
local notation "B" => radiusB p
local notation "D" => roomSizeR Θ₃ X.halo B
local notation "τ" => Mint.width X.halo B B
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include I I' hC he hp
lemma ramifyR (z: Park c f) (h: SeedR Θ₃ I z) (hk : Meadow.ground I z⊆ neighbors D' x') (ht : D'+τ≤ m) (hm: 2 * m < c.val) : ∃ v, SeedR Θ₃ I' v ∧ Meadow.ground I' v⊆neighbors m x ∧ wrappers (L) v=z := by
  let P:= L 
  let y := verse_down P
  choose Y' HY hp' using (nest_mint (h:=by assumption) (H:=H) (Q:=Q) (hC:=hC) (he:=he)).esc x -- maybe inference
  let v:=z.image Y'
  have hx' i (hi:i∈z) : separation x (pace Y (Y' i)) ≤ D':=(hp' i).trans_le ((neighbors_mem ..).1 (hk (centersR h hi)))
  have hr k (hk:k∈v): pace Y k ∈ Meadow.ground I' v ∧ I'.supportP (disc (Y) k) ⊆ neighbors m x:= by
    obtain ⟨p,hpK,rfl⟩:= mem_image.mp hk; let A':=Y' p; have hh:= contempt hC he hp (I:=I) (I':=I') A'; have ht' := hx' p hpK
    obtain ⟨hz,hV⟩:= centered X.halo B B (lt_of_lt_of_le (by norm_num) I'.laws.data.room.sight.1) A' Y T' R' (((hh.1.trans (congr_arg (verse R.path) (HY p))).trans_le (h.earns _ hpK)))
    refine ⟨mem_biUnion.mpr ⟨_,mem_map_of_mem (disc Y) (show A'∈ v from mem_image_of_mem _ hpK),hz⟩, fun i hi=> ?_⟩; apply (neighbors_mem ..).2; exact (separation_triangle _ (pace Y A') _).trans ((Nat.add_le_add ht' ((neighbors_mem ..).1 (hV hi))).trans ht)
  have hM:Meadow.ground I' v⊆neighbors m x:= by intro i hi; obtain ⟨k,hk,h⟩:= mem_biUnion.mp hi; obtain ⟨s,hs,rfl⟩:=mem_map.mp hk; exact (hr s hs).2 h
  have ht': Set.InjOn (verse_down P) v:= fun i hi j hj hh=> (nest_mint (hC:=hC) (he:=he) (h:=by assumption) (H:=H) (Q:=Q)).point hm x i j ((neighbors_mem ..).1 (hM (hr i hi).1)) ((neighbors_mem ..).1 (hM (hr j hj).1)) hh
  have hL:wrappers P v=z:= by unfold wrappers v; rw [Finset.image_image,show verse_down P ∘ Y'=id from funext HY,image_id]
  exact ⟨v,(seed_orderR hC he hp v (I:=I) (I':=I') ht' ((garden hC x hm).mono (coe_subset.mpr hM))).2 (hL.symm ▸ h),hM,hL⟩
lemma returnsR (s: Vines c f) (hs: StirR Θ₃ I s) (hx:x'∈Meadow.pasture I s) (hH:2*(D+τ) < c.val):
    ∃ u, StirR Θ₃ I' u∧ x∈Meadow.pasture I' u∧ forward (L) u=s:= by
  choose f hp' hZ hf using fun i=> ramifyR hC he x hp (I:=I) (I':=I') (s.2 i) (hs.each i) ((your (z:=s) i).trans (enteredR hs x' hx)) le_rfl hH
  let u:Vines C F:= ⟨s.1,f⟩
  have h : forward (L) u=s:= by unfold forward u; congr 1; exact funext hf
  have ht : Meadow.pasture I' u⊆ neighbors (D+τ) x:= by
    intro i hi; obtain ⟨j,-,hq⟩:=mem_biUnion.mp hi; exact hZ j hq
  have hy := receiptsR (I:=I) hC he x hp u hH ht hp'; rw [h] at hy
  refine ⟨u,⟨hs.small,hp',hy.symm ▸ hs.moves⟩,?_,h⟩
  obtain ⟨i,hk,hh⟩:=mem_image.mp (show (L).low.cut x∈ (Meadow.pasture I' u).image (L).low.cut from (by rw [← pitchRoll hC he hp (I:=I) (I':=I') u,h]; exact hx))
  exact ((garden hC x hH (ht hk) (show x ∈ neighbors _ x from (neighbors_mem ..).2 (by simp)) hh) : i=x) ▸ hk
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ}
variable {X : ConnectedActivityE6.Target G K} {o: Target.Order G W} {χ : Chi}
section coin
variable {S:StepData c f} {T:Tube G S} {R:RG.Rep G f} {H : Cash W p a L₀ X o U T R}
def voteR (z:PoetR Θ₃ H) := ((Meadow.pasture H z.val).card:ℝ)⁻¹
def offerR (χ:Chi) (z:PoetR Θ₃ H) (V:Config G c) := -(voteR z) * stream H χ V (vintageR z.val z.property)
variable (Θ₃) in
def echoingR (H:Cash W p a L₀ X o U T R) (χ:Chi) (k:ℕ) (x:Site c) (V:Config G c):= ∑ i∈(Meadow.calendarR Θ₃ H k).filter (fun i=>x∈Meadow.pasture H i.val), Meadow.offerR χ i V
end coin
section roll
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (Tq : T'=Deck.re T) (hp:R'.path=R.path) (ha:R'.p= R.p) (hz:R'.beta=R.beta) (x : Site C) (hX:4*roomSizeR Θ₃ X.halo (radiusB p)<c.val) {b ℓ : ℕ}
    {C' d z T'' A B r V' u s₁ a' b' c' d' e' D Z q' :ℝ} -- B conflicts
    (N : Captain I b C' d z T'' A B r V' u m χ) (N' : Captain I' j s₁ a' b' c' d' e' D Z q' ℓ χ) -- note args
    (f' : Config G c) (hV: RG.flags (Pressure.temp p) f'= ∅)
local notation "R₀" => radiusB p
local notation "D'" => roomSizeR Θ₃ X.halo R₀
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include hC he Tq hp ha hz hX N N' hV
lemma dueR (i : PoetR Θ₃ I') (j:PoetR Θ₃ I) (heq: j.val=forward (L) i.val) (hr:x∈Meadow.pasture I' i.val):
     offerR χ i ((L).low.links f')=offerR χ j f':= by
  let f:=f'; let F:=(L).low.links f; let z:=i.val; let w:= j.val
  have hc: RG.flags (Pressure.temp p) F=∅:= by ext i; rw [show i∈RG.flags (Pressure.temp p) F↔_ from Deck.flagged hC f' i (show c.val>4 from (by have hv:= I.laws.data.room.buys; omega)) (Pressure.temp p),hV]; simp -- adjust
  have hf:(Meadow.pasture I w).card= (Meadow.pasture I' z).card:= by
    have hy:=enteredR i.property x hr; unfold w; rw [heq, pitchRoll hC he (I:=I) (I':=I') hp]; exact card_image_of_injOn ((garden hC x (show 2* D' < c.val from (by omega))).mono (Finset.coe_subset.mpr hy))
  let C0:= vintageR z i.property; let C1:= vintageR w j.property; have ht : stream I χ f C1= I.trainedPool χ f C1:= Eq.symm ((congr_fun (N.permitAverage C1).2.2.2.1 f).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hV]; simp)))
  have hx : stream I' χ F C0= I'.trainedPool χ F C0 := Eq.symm ((congr_fun (N'.permitAverage C0).2.2.2.1 F).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hc]; simp)))
  have hh : 2*D' < c.val:=by omega
  suffices h : I'.trainedPool χ F C0= I.trainedPool χ f C1 by unfold offerR; rw [ht,hx,h,show Meadow.voteR j=Meadow.voteR i from (by unfold Meadow.voteR; rw [show (Meadow.pasture I j.val).card=_ from hf])]
  obtain ⟨j,Hj⟩:=j; dsimp only at heq; subst j
  unfold Cash.trainedPool Gas.term
  apply congr_arg₂ HDiv.hDiv _ rfl
  apply congr_arg₂ HMul.hMul
  · exact (manaR i.property).symm.trans ((receiptsR hC he (I:=I) x hp z hh (enteredR i.property x hr) i.property.each).trans (manaR Hj))
  apply prod_congr rfl; intro j _
  have hy' := ringsR (h:=h) hC he x i.val i.property hr hh j
  exact Mint.meetups hC he I' I Tq hp ha hz x D' (by omega) hy' (engirdsR x i.val i.property hr j) (i.property.each j).earns f χ hV (i.property.each j).hot (Hj.each j).hot

lemma arrangesR (k:ℕ) : Meadow.echoingR Θ₃ I' χ k x ((L).low.links f')= Meadow.echoingR Θ₃ I χ k x' f':= by
  let T x i:= x∈Meadow.pasture I' i
  let P:=L; let u:=(Meadow.calendarR Θ₃ I' k).filter (fun i=> x∈Meadow.pasture I' i.val); let v:=(Meadow.calendarR Θ₃ I k).filter (fun i=> x'∈Meadow.pasture I i.val)
  have hm : 2*(D')<c.val:= by omega
  have hh {i : PoetR Θ₃ I'} (hi:i∈u) := stitchesR hC he (I:=I) (I':=I') x hp i.val i.property (mem_filter.mp hi).2 hm
  let f (i: PoetR Θ₃ I') (hi:i∈u): PoetR Θ₃ I:=⟨forward P i.val, (hh hi).1⟩
  have hv i: held (verse_down P i)= held i := by rcases i with i|i|i|i <;> rfl
  have ht (z:Vines C F): (∀ j,z.snd j⊆tuck k) ↔ (∀ j,(forward P z).snd j⊆ tuck k):= by
    constructor
    · intro h j i hi; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; rw [pocket,hv,← pocket]; exact h _ (by assumption)
    intro h j i hi; rw [pocket, ← hv,← pocket]; exact h _ (mem_image_of_mem (verse_down P) (show i∈z.snd j from hi))
  apply Finset.sum_bij f (fun i hi=> ?_) (fun i hi j hj heq=> ?_) (fun b hb=>?_) (fun i hi=>?_)
  · exact mem_filter.mpr ⟨(tunesR _ k).mpr ((ht _).1 ((tunesR i k).1 (mem_filter.mp hi).1)), (hh hi).2⟩
  · exact Subtype.ext (inquireR hC he x j.val i.val j.property i.property (mem_filter.mp hj).2 (mem_filter.mp hi).2 hm (congr_arg Subtype.val heq))
  ·
    obtain ⟨y,hy,hY,h⟩ := Meadow.returnsR hC he x hp b.val (I:=I) (I':=I') b.property (mem_filter.mp hb).2 (show 2*(D'+Mint.width X.halo R₀ R₀)<c.val from by unfold roomSizeR at *; omega)
    have hk : (⟨y,hy⟩ : PoetR Θ₃ I')∈u:= mem_filter.mpr ⟨(tunesR _ _).2 ((ht _).2 (h.symm ▸ (tunesR _ _|>.1 (mem_filter.mp hb).1))),hY⟩; exact ⟨_,hk,Subtype.ext h⟩
  exact dueR hC he Tq hp ha hz x hX N N' f' hV i (f i hi) rfl (mem_filter.mp hi).2
end roll
end YM.PhysicalNext.Repeat.Meadow
