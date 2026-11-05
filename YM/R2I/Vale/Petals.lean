import YM.R2I.Vale.Fields
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet
/- Widen verified Meadow Tableau,Blox,Reframe,Fir,Duet proof to arbitrary order Θ. Native radius remains, connectivity & symmetry BOTH. -/
noncomputable section

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {χ:Chi} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}

section mint
variable {S:StepData c f} {T:Tube G S} {R : RG.Rep G f} (H : Cash W p a L₀ X o U T R)
local notation "B" => radiusB p

variable (Θ₃) in
def baronyR (χ:Chi) (k:ℕ) (γ:ℝ) := Meadow.atlas (echoingR Θ₃ H χ k + garner T.down T.low R.beta γ B k)
lemma rotatesR (χ:Chi) (k:ℕ) (γ:ℝ) (x:Site c) (V:Config G c) (s:Signed) (b:Site c): baronyR Θ₃ H χ k γ (Lattice.affine s b x) V= baronyR Θ₃ H χ k γ x (pull s b V):=(astrolabe _ x V (s,b)).symm
end mint

section roll
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (Tq : T'=Deck.re T) (hp:R'.path=R.path) (ha:R'.p= R.p) (hz:R'.beta=R.beta) (x : Site C) (hX:4*roomSizeR Θ₃ X.halo (radiusB p)<c.val) {b ℓ : ℕ}
    {C' d z T'' A B r V' u s₁ a' b' c' d' e' D Z q' :ℝ}
    (N : Captain I b C' d z T'' A B r V' u m χ) (N' : Captain I' j s₁ a' b' c' d' e' D Z q' ℓ χ)
    (f' : Config G c) (hV: RG.flags (Pressure.temp p) f'= ∅)
local notation "R₀" => radiusB p
local notation "D'" => roomSizeR Θ₃ X.halo R₀
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
include hC he Tq hp ha hz hX N N' hV
lemma replayR (γ' : ℝ) (k:ℕ) : baronyR Θ₃ I' χ k γ' x ((L).low.links f')=baronyR Θ₃ I χ k γ' x' f':= by
  let b (θ:Seat c):=echoingR Θ₃ I χ k ((spin θ).symm x') (θ.view f') + garner T.down T.low R.beta γ' R₀ k ((spin θ).symm x') (θ.view f')
  unfold baronyR atlas; change _=likely b
  rw [← revolving hC b]
  apply congr_arg likely; funext θ
  simp only [b,Pi.add_apply]
  rw [show θ.view ((L).low.links f')=(L).low.links ((pinch hC θ).view f') from estuary hC f' θ]
  apply congr_arg₂ HAdd.hAdd
  · rw [← inverts hC θ]; exact arrangesR hC he Tq hp ha hz _ hX N N' ((pinch hC θ).view f') (covers_field (pinch hC θ) f' hV) k
  rw [hz,← inverts hC θ]; subst T'; exact garner_pack hC ..
end roll
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p

variable (Θ₃) in
def keepR (I : Cash W p a L₀ X o U T R') (i: Magazine I): Prop:= i.elim (fun i=>i∉Set.range (boothsR Θ₃ I)) (fun i=> B< arc T.down i)
variable (Θ₃) in
def towerR (X' : Match.Alliance I H 1 0) (γ : ℝ) (i:Magazine I): Config G c→ℝ:= if Meadow.keepR Θ₃ I i then opus I X' χ γ i else 0

variable (Θ₃) in
def bouquetR (I:Cash W p a L₀ X o U T R') (k:ℕ): Finset (Magazine I):= disjSum ((Meadow.calendarR Θ₃ I k).map (boothsR Θ₃ I)) ((univ ×ˢ (ripened T.down B k)).map (rollers c).toEmbedding)
lemma notKeptR (z:Magazine I) (h:z ∈ bouquetR Θ₃ I m) : ¬keepR Θ₃ I z:= by
  unfold bouquetR at h; rcases z with z|z
  · obtain ⟨i,hi,hz⟩:= mem_map.mp (inl_mem_disjSum.mp h); exact fun he=> he ⟨i,hz⟩
  obtain ⟨⟨s,i⟩,hi,hz⟩:= mem_map.mp (inr_mem_disjSum.mp h); have ht : arc T.down z≤ B:= by rw [← (show legs s i=z from hz),arc_receipt]; exact (mem_filter.mp (mem_product.mp hi).2).2
  exact fun h=> not_lt.mpr ht h
lemma unfurlsR (z:Magazine I) (hp:¬keepR Θ₃ I z): ∀ᶠ m in atTop,z∈bouquetR Θ₃ I m:= by
  rcases z with z|z
  · change ¬z∉_ at hp; obtain ⟨w,rfl⟩: z ∈ Set.range (boothsR Θ₃ I):= Classical.byContradiction hp; filter_upwards [retiresR w] with m hm; exact inl_mem_disjSum.mpr (mem_map_of_mem _ hm)
  obtain ⟨⟨s,i⟩,hv⟩:= (rollers c).surjective z
  have h: Meadow.melody T.down i≤ B:= by rw [← arc_receipt T.down s i, show legs s i=z from hv]; exact le_of_not_gt hp
  filter_upwards [burgeoning T.down B i h] with m hm; exact inr_mem_disjSum.mpr (mem_map.mpr ⟨(s,i),mem_product.mpr ⟨mem_univ _,hm⟩,hv⟩)

variable (Θ₃) in
def debrisR (I:Cash W p a L₀ X o U T R') (k:ℕ) (w:ℕ) := ¬keepR Θ₃ I (Song.pennant I w).2∧ (Song.pennant I w).2∉ bouquetR Θ₃ I k
lemma dissolvedR (I:Cash W p a L₀ X o U T R') (w:ℕ): ∀ᶠ k in atTop,¬debrisR Θ₃ I k w := by
  by_cases h:keepR Θ₃ I (Song.pennant I w).2
  · filter_upwards with k using (fun hx=> hx.1 h)
  exact (unfurlsR _ h).mono fun k h H=> H.2 h



end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
section petals
variable (I) (k:ℕ)
variable (Θ₃) in
def panelR : Finset ℕ := (univ ×ˢ (Meadow.bouquetR Θ₃ I k)).map (pennant I).symm.toEmbedding
variable {k}
lemma petaledR (i:ℕ) : i∈panelR Θ₃ I k ↔ (pennant I i).2∈Meadow.bouquetR Θ₃ I k:= by
  unfold panelR; simp only [mem_map_equiv,mem_product]; simp

end petals
section apo
variable (I) (p' : BudgetPoint) (x:Site c)
-- radius ℓ; purch post c
variable (Θ₃) in
abbrev studioR (l b:ℕ) := roomSizeR Θ₃ l b + 2*b
local notation "D''" => Meadow.studioR Θ₃ X.halo B
lemma modestR (i: Magazine I) (hv: i∈Meadow.bouquetR Θ₃ I m) (hB:p'.B=B) (ht: share I p' x i≠0): x∈(Beam.contents I p' i).support ∧ (Beam.contents I p' i).support⊆ neighbors D'' x := by
  rcases i with i|i
  · obtain ⟨⟨z,hz⟩,hi,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp hv)
    let z':=vintageR z hz; have he: x∈perf I z':= by contrapose! ht; exact if_neg ht
    change x∈(Beam.dashboard I z').support ∧ (Beam.dashboard I z').support ⊆_; rw [Beam.see]
    exact ⟨he, fun i hi=>(neighbors_mem ..).mpr (((neighbors_mem ..).1 (enteredR hz x he hi)).trans (Nat.le_add_right ..))⟩
  obtain ⟨⟨s,i'⟩,he,rfl⟩:=mem_map.mp (inr_mem_disjSum.mp hv); have hf : Meadow.melody T.down i'≤ B:= (mem_filter.mp ((mem_product.mp he).2)).2
  let k:= strings T.down p' (legs s i'); have he:k.site=x:= by contrapose! ht; exact if_neg ht
  change x∈k.support∧ k.support⊆_
  refine ⟨he ▸ k.anchor,?_⟩; rw [show x=s.2 from he.symm.trans (tunesAnchor ..)]; intro x hx; have h:= (neighbors_mem ..).1 (yarn T.down p' s i' hx); apply (neighbors_mem ..).2; dsimp only [Meadow.studioR]; omega
lemma assignedR (i:ℕ) (h : i∈Meadow.panelR Θ₃ I m) (hB:p'.B=B) (hp:garnerAt I p' x i≠0):x∈((Beam.marquee I p').reg i).support ∧ ((Beam.marquee I p').reg i).support⊆ neighbors D'' x:= by
  let p:=Song.pennant I i; let θ:=spin p.1; let u:=θ.symm x
  obtain ⟨hy,hz⟩:=modestR I p' u p.2 ((petaledR I i).1 h) hB hp
  change x∈ Finset.image θ _ ∧ Finset.image θ (Beam.contents I p' p.2).support⊆ _
  refine ⟨mem_image.mpr ⟨u,hy,θ.apply_symm_apply x⟩,fun i hi=>?_⟩; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; apply (neighbors_mem ..).2
  rw [show x=θ u from (θ.apply_symm_apply x).symm, show separation (θ u) (θ k)=separation u k from ?_] -- lemma
  exact (neighbors_mem ..).mp (hz hk)
  change separation (p.1.1.act u+p.1.2) (p.1.1.act k+p.1.2)=_; rw [separation_translate,separation_signed]
end apo
section pact
variable (p':BudgetPoint) (X' : Match.Alliance I H 1 0)
  (hp:R'.path=R.path) (he:I.supportP=H.supportP) (hz:X'.units=Equiv.refl _)
    (χ) (γ:ℝ) (k:ℕ)
include p' X' hp he hz χ γ
lemma tuneshipsR (x:Site c) (V:Config G c) : Meadow.echoingR Θ₃ H χ k x V + Meadow.garner T.down T.low R.beta γ B k x V=∑ i∈Meadow.bouquetR Θ₃ I k, Meadow.share I p' x i * opus I X' χ γ i V:= by
  let X:=firstBatchR (Θ₃:=Θ₃) hp he
  have h (i:PoetR Θ₃ I) : X i∈ Meadow.calendarR Θ₃ H k ↔ i∈Meadow.calendarR Θ₃ I k:= by rw [tunesR,tunesR]; rfl
  unfold bouquetR; rw [sum_disjSum, sum_map,sum_map]; dsimp only [Equiv.toEmbedding_apply]
  apply congr_arg₂ HAdd.hAdd
  · unfold echoingR; rw [Finset.sum_filter]; symm; refine Finset.sum_equiv X (fun i=> (h i).symm) ?_; intro i hi
    obtain ⟨z,hx⟩:= i; let i: PoetR Θ₃ I:=⟨z,hx⟩
    let w:=boothsR Θ₃ I i; have hx:(perf I w)= Meadow.pasture H (X i).val:= Eq.trans (reconnects I X' _) (by rw [identifiesR X' hp hz he]; rfl)
    let v:= X i
    change (if x∈ perf I w then _ else _) * ((-1:ℝ)*stream H χ V (X'.furrow w))=if x ∈ Meadow.pasture H v.val then -(Meadow.voteR v)*_ else _
    rw [show X'.furrow w= boothsR Θ₃ H v from identifiesR X' hp hz he i,hx]; split_ifs
    · change _= -(Meadow.voteR v)* stream H χ V (boothsR Θ₃ H v); simp only [voteR]; ring
    rw [zero_mul]
  unfold garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down p' (legs s i)).site=x then (1:ℝ) else 0) * opus I X' χ γ (.inr (legs s i)) V
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rfl
lemma asterR (x:Site c) : Meadow.baronyR Θ₃ H χ k γ x= ∑ i∈Meadow.panelR Θ₃ I k, Meadow.garnerAt I p' x i • ((plusone I X' χ γ).logRead i) := by
  ext V; unfold baronyR atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold likely; unfold panelR; rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [tuneshipsR χ p' X' hp he hz γ k]; rw [Finset.mul_sum] -- edit
  apply sum_congr rfl; intro θ _; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
  dsimp only [plusone,garnerAt,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]
  let q:= share I p' ((spin θ).symm x) i; let v:=opus I X' χ γ i (θ.view V); change Rim c*(q*v)=q*(Rim c*v); ring
end pact
end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
variable (X' : Match.Alliance I H 1 0) (p' : BudgetPoint)
lemma cap_RsumR {ι:Type} (f h u:ι→ Config G c→ℝ) (he : u=f+h) (A: ι→RegularAddress c) (p : BudgetPoint)
   (hp : Budget p A f a) (hv:Budget p A h W): Budget p A u (a+W):= by
  obtain ⟨k,h',hv'⟩:=hv; obtain ⟨c',hc,hF⟩:=hp; rw [he]; refine ⟨c'+k,fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (hc i) (h' i) using 2 with x; dsimp only [Pi.add_apply]; split <;> ring
  have hh:(f+h) i=f i-((-1:ℝ) • h i):= by simp
  have hp:= CouplingShape.reg_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1); rw [hh]; refine ⟨hp,?_⟩
  have hb:= CouplingShape.sup_scale (-1) (hv' i).2; rw [abs_neg,abs_one,one_mul] at hb; exact CouplingShape.sup_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1) (hF i).2 hb
variable (γ : ℝ)
variable (Θ₃) in
def hKeepR (t : ℕ) (z:Magazine I) := if z∈Meadow.bouquetR Θ₃ I t then 0 else opus I X' χ γ z

variable (Θ₃) in
def timbresR (t:ℕ): Collection.Source G c:= ⟨choir (hKeepR Θ₃ X' (χ:=χ) γ t) ∘ pennant I, fuse I X' χ ∘ Refrain.badge I⟩

lemma compassR (k:ℕ) (x: ℕ) : (timbresR Θ₃ X' (χ:=χ) γ k|>.logRead x) = (if (pennant I x).2 ∈ Meadow.bouquetR Θ₃ I k then 0 else (plusone I X' χ γ).logRead x):= by
  unfold timbresR plusone choir; let y:= Song.pennant I x; change Rim c • ((if _ then (_:Config G c→ℝ) else _) ∘ y.1.view)= _; split
  · ext; simp
  rfl

-- add any towerR Θ₃.D.Dep support + Preserved Phi.A.
lemma candlesR (k:ℕ) {t w : ℝ} (h : Budget p' (Beam.marquee I p').reg (choir (towerR Θ₃ (χ:=χ) X' γ) ∘ pennant I) t) (hp: Budget p' (Beam.marquee I p').reg (fun i=> if debrisR Θ₃ I k i then (plusone I X' χ γ).logRead i else 0) w) :
   Budget p' (Beam.marquee I p').reg (timbresR Θ₃ X' γ k (χ:=χ)|>.logRead) (t+w):= by
  refine cap_RsumR _ _ _ ?_ _ _ h hp
  ext x i; rw [compassR]; let y:= pennant I x; let z:= y.2; let u:= y.1.view i
  change ((if z∈ bouquetR Θ₃ I k then (_:Config G c→ℝ) else _) i)= Rim c * ((if keepR Θ₃ I z then (_:Config G c→ ℝ) else _) u)+(if Meadow.debrisR Θ₃ I k x then (_:Config G c→ ℝ) else _) i
  by_cases he:z∈ bouquetR Θ₃ I k; · rw [if_pos he, if_neg (notKeptR z he), if_neg (show ¬debrisR Θ₃ I k x from (fun h=> h.2 he))]; simp
  rw [if_neg he]; split
  next hv=> rw [if_neg (show ¬debrisR Θ₃ I k x from (fun h=> h.1 hv))]; change _= _ + 0; rw [add_zero]; rfl
  next hh=> rw [if_pos (show debrisR Θ₃ I k x from ⟨hh,he⟩)]; simp


end YM.PhysicalNext.Repeat.Meadow

set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Θ₃ : ℕ}
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
local notation "D''" => Meadow.studioR Θ₃ X.halo B
open Brim Height Refrain
section bay
variable (X' : Match.Alliance I H 1 0) {χ:Chi} (k:ℕ) {p': BudgetPoint} (x:Site c) {γ t v z : ℝ} (hp : Collection.Local (posting p' I) p' (plusone I X' χ γ) t v) (hq : Meadow.Budget p' (Beam.marquee I p').reg (timbresR Θ₃ X' (χ:=χ) γ k|>.logRead) z) (hB:p'.B=radiusB p)
-- Local from Collection
include X' hp hB
lemma regularWR (i:ℕ) (h:i∈panelR Θ₃ I k) : p'.Regular (neighbors D'' x) (garnerAt I p' x i • (plusone I X' χ γ).logRead i) := by
  by_cases hF:garnerAt I p' x i=0; · rw [hF,zero_smul]; exact CouplingShape.reg_const _
  have hM:= (assignedR I p' x i h hB hF).2; rw [Beam.rewrite_rule] at hM
  exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hp.smooth i) hM)
omit hB
lemma unearnedR (V:Config G c) :
    (posting p' I|>.read (plusone I X' χ γ)|>.additive p' V) = (Beam.marquee I p'|>.read (timbresR Θ₃ X' (χ:=χ) γ k)|>.additive p' V) +
       ∑ i∈Meadow.panelR Θ₃ I k, masked p'.threshold ((Beam.marquee I p').reg i).support ((plusone I X' χ γ).logRead i) V:= by
  let t' i:= masked p'.threshold ((Beam.marquee I p').reg i).support ((plusone I X' χ γ).logRead i) V; let h i:=if i∈ Meadow.panelR Θ₃ I k then t' i else 0
  let f i:= ((posting p' I).read (plusone I X' χ γ)).regularOccurrence p' i V; let g i:= ((Beam.marquee I p').read (timbresR Θ₃ X' (χ:=χ) γ k)).regularOccurrence p' i V
  have he : g=f-h:= by
    funext i; change masked _ _ ((timbresR Θ₃ X' (χ:=χ) γ k).logRead i) V=f i-h i; rw [Meadow.compassR]; have hh : f i=t' i:= by unfold t'; rw [Beam.rewrite_rule]; rfl
    rw [hh]; unfold h; split
    next hz=> rw [if_pos ((Meadow.petaledR I i).2 hz),sub_self]; simp [masked]
    next hz=> rw [if_neg (mt (Meadow.petaledR I i).1 hz),sub_zero]; rfl
  have hs: Summable f:= Roof.Embrasure.series _ _ hp V
  have h':HasSum h (∑ i∈ Meadow.panelR Θ₃ I k,t' i):=by
    convert hasSum_sum_of_ne_finset_zero (s:= Meadow.panelR Θ₃ I k) (f:=h) (fun i hi=> if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
    infer_instance
  have he': (∑' i, g i)= (∑' i, f i)-∑ i∈ Meadow.panelR Θ₃ I k,t' i:= by rw [he]; exact (hs.hasSum.sub h').tsum_eq
  change (∑' i,f i)=(∑' i, g i)+_; rw [he',sub_add_cancel]
variable (he:I.supportP=H.supportP) (hX:R'.path=R.path) (hz:X'.units=Equiv.refl _)
include hB he hX hz
lemma regularYR : p'.Regular (neighbors D'' x) (Meadow.baronyR Θ₃ H χ k γ x):= by rw [asterR χ p' X' hX he hz γ k]; exact Meadow.regularA _ fun i hi=> regularWR X' k x hp hB i hi
omit hB
variable {β v₀ C L E : ℝ} {Y : BudgetPoint}
local notation "λ₀" => (timbresR Θ₃ X' (χ:=χ) γ k)
local notation "P₀" => (posting p' I)
lemma chorusR (V:Config G c) (hR:R=Pane.virgin T Y β)
    (ht:S.push β R.eval V=earlyValue (P₀) T.down T.low p' (plusone I X' χ γ) β v₀ γ V) (h':T.down.Bounds T.low C L E)
    (hh:flags p'.threshold V=∅): Token.arrayE T Y β γ V= v₀*(Fintype.card (Site c):ℝ)- (∑ x, Meadow.baronyR Θ₃ H χ k γ x V) - ∑' i, (λ₀).logRead i V:= by
  -- get ht
  let D i:= (λ₀).logRead i V; have hK : ∑ i∈Meadow.panelR Θ₃ I k, masked p'.threshold ((Beam.marquee I p').reg i).support ((plusone I X' χ γ).logRead i) V=
      ∑ x, Meadow.baronyR Θ₃ H χ k γ x V := by
    simp_rw [asterR χ p' X' hX he hz γ k, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i hi
    rw [← Finset.sum_mul, Meadow.paysOne,one_mul]; exact masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
  have hx : (Beam.marquee I p'|>.read (λ₀)|>.additive p' V)= ∑' i, D i:= tsum_congr fun i=> masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
  unfold Token.arrayE; rw [← hR,ht]; have hg : ((P₀).read (plusone I X' χ γ)).gas p' V=1:= Activities.gas_one _ _ hh; have hf: Collection.receipt T.down T.low p' V= secondTerm T.low T.down V:= VerifiedReset.allGoodPrice h' V hh
  unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only; rw [hg,mul_one, ← Real.exp_add,Real.log_exp, Pane.crystalline _ _ _ _ _ hh, hf, unearnedR (Θ₃:=Θ₃) X' k hp,hK,hx]; change _= _ -∑' i,D i; ring
end bay
end YM.PhysicalNext.Repeat.Meadow
