import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Blox
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Tableau
/-!
 # Petals = EXACT per-fragrance support allocation of unmasked truncated germ.
 Mask enlargements later. No new Regular prices asserted.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
section petals
variable (I) (k:ℕ)
def panel : Finset ℕ := (univ ×ˢ (Meadow.bouquet I k)).map (pennant I).symm.toEmbedding
variable {k}
lemma petaled (i:ℕ) : i∈panel I k ↔ (pennant I i).2∈Meadow.bouquet I k:= by
  unfold panel; simp only [mem_map_equiv,mem_product]; simp

end petals
section apo
variable (I) (p' : BudgetPoint) (x:Site c)
def share (i :Magazine I):ℝ:= i.elim (fun z=> if x∈ Song.perf I z then ((Song.perf I z).card:ℝ)⁻¹ else 0) (fun z=> if (strings T.down p' z).site=x then 1 else 0)
def honor (w:Song.ballad I) := share I p' ((spin w.1).symm x) w.2
def garnerAt (j:ℕ): ℝ := honor I p' x (pennant I j)
lemma nonnegative (i:ℕ) : 0 ≤ garnerAt I p' x i:= by
  let e:= pennant I i
  change 0 ≤ share I p' ((spin e.1).symm x) e.2
  cases h:e.2<;> simp only [share,Sum.elim_inl,Sum.elim_inr]<;> split_ifs<;> positivity
lemma paysOne (i:ℕ) : ∑ x:Site c,garnerAt I p' x i=1:= by
  let j:= (Song.pennant I i)
  unfold garnerAt
  change ∑ x:Site c,share I p' ((spin j.1).symm x) j.2=1
  rw [Equiv.sum_comp (spin j.1).symm (fun x=>share I p' x j.2)]
  cases he:j.2 with
  | inl p=> simp_rw [share,Sum.elim, ← sum_filter]; rw [sum_const,nsmul_eq_mul]; have hh: (univ.filter (fun x=> x∈ perf I p))= perf I p:= by ext; simp
            rw [hh]; have hv := Finset.card_pos.mpr (crest I p); exact mul_inv_cancel₀ (by positivity)
  | inr p=> simp [share]
lemma portions (i:ℕ) : garnerAt I p' x i≤1:= (paysOne I p' i) ▸ (single_le_sum (fun k _=> nonnegative I p' k i) (mem_univ x))
-- radius ℓ; purch post c
abbrev studio (l b:ℕ) := roomSize l b + 2*b
local notation "D''" => Meadow.studio X.halo B
lemma modest (i: Magazine I) (hv: i∈Meadow.bouquet I m) (hB:p'.B=B) (ht: share I p' x i≠0): x∈(Beam.contents I p' i).support ∧ (Beam.contents I p' i).support⊆ neighbors D'' x := by
  rcases i with i|i
  · obtain ⟨⟨z,hz⟩,hi,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp hv)
    let z':=vintage z hz; have he: x∈perf I z':= by contrapose! ht; exact if_neg ht
    change x∈(Beam.dashboard I z').support ∧ (Beam.dashboard I z').support ⊆_; rw [Beam.see]
    exact ⟨he, fun i hi=>(neighbors_mem ..).mpr (((neighbors_mem ..).1 (entered hz x he hi)).trans (Nat.le_add_right ..))⟩
  obtain ⟨⟨s,i'⟩,he,rfl⟩:=mem_map.mp (inr_mem_disjSum.mp hv); have hf : Meadow.melody T.down i'≤ B:= (mem_filter.mp ((mem_product.mp he).2)).2
  let k:= strings T.down p' (legs s i'); have he:k.site=x:= by contrapose! ht; exact if_neg ht
  change x∈k.support∧ k.support⊆_
  refine ⟨he ▸ k.anchor,?_⟩; rw [show x=s.2 from he.symm.trans (tunesAnchor ..)]; intro x hx; have h:= (neighbors_mem ..).1 (yarn T.down p' s i' hx); apply (neighbors_mem ..).2; dsimp only [Meadow.studio]; omega
lemma assigned (i:ℕ) (h : i∈Meadow.panel I m) (hB:p'.B=B) (hp:garnerAt I p' x i≠0):x∈((Beam.marquee I p').reg i).support ∧ ((Beam.marquee I p').reg i).support⊆ neighbors D'' x:= by
  let p:=Song.pennant I i; let θ:=spin p.1; let u:=θ.symm x
  obtain ⟨hy,hz⟩:=modest I p' u p.2 ((petaled I i).1 h) hB hp
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
lemma tuneships (x:Site c) (V:Config G c) : Meadow.echoing H χ k x V + Meadow.garner T.down T.low R.beta γ B k x V=∑ i∈Meadow.bouquet I k, Meadow.share I p' x i * opus I X' χ γ i V:= by
  let X:=firstBatch hp he
  have h (i:Poet I) : X i∈ Meadow.calendar H k ↔ i∈Meadow.calendar I k:= by rw [tunes,tunes]; rfl
  unfold bouquet; rw [sum_disjSum, sum_map,sum_map]; dsimp only [Equiv.toEmbedding_apply]
  apply congr_arg₂ HAdd.hAdd
  · unfold echoing; rw [Finset.sum_filter]; symm; refine Finset.sum_equiv X (fun i=> (h i).symm) ?_; intro i hi
    obtain ⟨z,hx⟩:= i; let i: Poet I:=⟨z,hx⟩
    let w:=booths I i; have hx:(perf I w)= Meadow.pasture H (X i).val:= Eq.trans (reconnects I X' _) (by rw [identifies X' hp hz he]; rfl)
    let v:= X i
    change (if x∈ perf I w then _ else _) * ((-1:ℝ)*stream H χ V (X'.furrow w))=if x ∈ Meadow.pasture H v.val then -(Meadow.vote v)*_ else _
    rw [show X'.furrow w= booths H v from identifies X' hp hz he i,hx]; split_ifs
    · change _= -(Meadow.vote v)* stream H χ V (booths H v); simp only [vote]; ring
    rw [zero_mul]
  unfold garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down p' (legs s i)).site=x then (1:ℝ) else 0) * opus I X' χ γ (.inr (legs s i)) V
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rfl
lemma aster (x:Site c) : Meadow.barony H χ k γ x= ∑ i∈Meadow.panel I k, Meadow.garnerAt I p' x i • ((plusone I X' χ γ).logRead i) := by
  ext V; unfold barony atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold likely; unfold panel; rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [tuneships χ p' X' hp he hz γ k]; rw [Finset.mul_sum] -- edit
  apply sum_congr rfl; intro θ _; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
  dsimp only [plusone,garnerAt,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]
  let q:= share I p' ((spin θ).symm x) i; let v:=opus I X' χ γ i (θ.view V); change Rim c*(q*v)=q*(Rim c*v); ring
end pact
end YM.PhysicalNext.Repeat.Meadow
