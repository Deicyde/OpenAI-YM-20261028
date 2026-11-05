import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Layering
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Payout

/-! # Insert every source kernel in the **same** sector swatch

Mark rough shadows and protect leading W with Γ. Exact even at bad
masks. Infer Spot from actual input `SourceAt`, `Shine` and
(for W dual troupe leading) the guard-away estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Docking
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Filter Station Thirst
     YM.PhysicalNext.PhysicalGuard7f546 Curved
open scoped Topology BigOperators Classical ENNReal ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ l k e z : ℝ} {L : Lantern G S} {A : Stores S} {P : Teller G} {W ι α : Type} [Fintype W] [DecidableEq W]
    {θ : W→Site f} {u : W→ Site c} {r : W→ℝ}
variable (R : Rep G f) (Q : Rep G c) (L : Lantern G S) (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30≤ Wg) (hv : u=S.ratio.parent ∘ θ)

def bead (p : SourceAt G θ) : Flake S G x L.park u Q.p.threshold where
  space := wings S Wg p.extent
  notes:=p.fires
  face:=fun A k U z=>masked R.p.threshold p.extent p.value (gazed (A:=A) T k.tag L.χ U x R.beta L.hood z)
  script:= forage ht L _ _ (Flux.inner_visits _ (Flux.toInner p)) (Flux.innerMeas _ (Flux.toInner p)) (Flux.inner_inv _ (Flux.toInner p)) _ hs _ _
  nontrivial:= p.chosen
  placed i hi:= hv.symm ▸ involved Wg _ (p.remembers i hi)
variable [Fintype ι] (Z : ι→ SourceAt G θ)
def pearls (i) := Docking.bead R Q L ht hs hv (Z i)
local notation "JH" => pearls R Q L ht hs hv Z
lemma acts : audition R Q JH Z (T:=T):= by
  intro V A k z; rw [Exponential.pass_sum]; swap; intro i _; exact Flux.asleep _ (Z i).chosen _
  apply prod_congr rfl; intro i _; exact Flux.solo _ _ (Z i).chosen
lemma bead_worth (p : SourceAt G θ) (_hp : ∀ i,0< r i) {a} (h : p.pays R.p r e a) (U : Config G c) k (p' : Stores S) y :
    stroke (p:=flakeTone (bead R Q L ht hs hv p)) r p' k U y ≤ penny p.extent R.p e a := by
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  let u := gazed (A:=p') (F:=k.wood) T k.tag L.χ U x R.beta L.hood y
  change ((Poly.toll r p.fires)*‖masked _ p.extent p.value u‖) * Value.charge R.p e p.extent ≤ a
  by_cases he:Healthy R.p.threshold p.extent u
  · rw [masked_eq _ _ _ _ he,mul_comm, ← mul_assoc]; exact h.2 u he
  rw [masked_ne _ _ _ _ he,norm_zero,mul_zero,zero_mul]; exact h.1
lemma pains {σ a : ℝ} (H : Shine Z R.p r σ k) (hR : Parachute S R.p Q.p e σ Wg a) (hr : ∀ i,0<r i) (hp : 1≤l) : Spot Q JH (fun _=>False) T l r e ((l*a)*k):= by
  obtain ⟨p,hp',H⟩:= H
  let B(i:ι):= penny (Z i).extent R.p σ (p i)
  have he i: 0≤B i:= penny_nn _ _ (hp' i).1
  have hl:=zero_le_one.trans hp
  refine ⟨fun i=>l*B i, fun i=>mul_nonneg hl (he i),fun i A U k z _=>?_,fun i _ U A k _=>Or.inl (fun y=>?_),?_⟩
  · exact (bead_worth R Q L ht hs hv (Z i) hr (hp' i) U k A z).trans (le_mul_of_one_le_left (he i) hp)
  · exact mul_le_mul_of_nonneg_left (bead_worth R Q L ht hs hv _ hr (hp' i) _ _ _ _) hl
  exact price_wave S Z p (fun i=>(hp' i).1) hR hl le_rfl H

-- true and shadow shards of arbitrary source. shade only from Lamp; after implementation they are always priced through Glow.
variable (f₀ : ℝ)
variable (T' : ι→ Site f) (t : ℕ) (hq : ∀ i,(Z i).extent=Spindle.patch t (T' i))
private def ray (i : ι) : Shader G S x L.park ℝ:= fun A _ _ y=> InteractingRank.shade A _ f₀ R.beta L.χ (T' i) t y
include hs hq
omit [Fintype ι] in
private lemma spun (i) : Sees (ray (x:=x) (S:=S) R L f₀ T' t i) (wings S Wg (Z i).extent) False Q.p.threshold := by rw [hq]; exact shade_sees L hs
-- Use exactly original H amount with its local `masked` check
def lampBead (b : Bool) (i:ι) : Flake S G x L.park u Q.p.threshold where
  space:= wings S Wg (Z i).extent
  notes:= (Z i).fires
  face:=fun A k U y=> (if b then (ray R L f₀ T' t i A k U y) else (1-ray R L f₀ T' t i A k U y)) • (JH i).face A k U y
  script:= by
    have h := spun R Q L hs Z f₀ T' t hq i
    have hB:=(h.pair (JH i).script)
    split
    · exact hB.comp _ (measurable_fst.smul measurable_snd)
    exact hB.comp _ ((measurable_const.sub measurable_fst).smul measurable_snd)
  nontrivial:= (Z i).chosen
  placed:= (JH i).placed
local notation "P0" => lampBead R Q L ht hs hv Z f₀ T' t hq

def troupe := Sum.elim (P0 true) (P0 false)
def lightcast {ι : Type} (i : ι⊕ι) := Sum.elim (fun _=>True) (fun _=>False) i
lemma enlightens : audition R Q (troupe R Q L ht hs hv Z f₀ T' t hq) (T:=T) Z:= by
  intro V A k z
  let u (i) := ingrain (flakeTone ∘ JH) i A k V z
  let p (i) := ingrain (flakeTone ∘ (troupe R Q L ht hs hv Z f₀ T' t hq)) i A k V z
  change _= ∏ i,(p i+1)
  rw [acts R Q L ht hs hv Z, Fintype.prod_sum_type, ← prod_mul_distrib]
  apply prod_congr rfl; intro i _
  have hz:p (.inl i)+p (.inr i)=u i:= by
    ext j; change ((Poly.send (Z i|>.fires) _)+(Poly.send (Z i|>.fires) _)).part j=(Poly.send (Z i|>.fires) _).part j
    rw [Poly.part_plus];simp_rw [Poly.part_send]; split
    · let w:=ray R L f₀ T' t i A k V z
      let y := (JH i).face A k V z
      change w • y+(1-w) • y=y; rw [← add_smul]; rw [add_sub_cancel .., one_smul]
    rw [add_zero]
  change u i+1=(p (.inl i)+1)*(p (.inr i)+1)
  have hh:p (.inl i)*p (.inr i)=0:= Eq.trans (Glyph.plate_pair (Z i).fires (Z i).fires _ _) (if_neg (by simp [(Z i).chosen.ne_empty]))
  rw [←hz,add_mul,mul_add,hh]; ring

-- payout requires purchase for actual hazard under every authorization -- infer from Morning below
include hs ht
lemma purchases (H : Shine Z R.p r e k) (hR : Parachute S R.p Q.p e e Wg (salary e)) (hr : ∀ i,0<r i) (_hp : 1≤l)
    (hx : 0<f₀) (hb : 0<R.beta) (he : ∀ (i:ι) (V : Config G c) (A : Stores S),Positioned x A V → ∀ k : Streak L.park,
      l * ((viewer T A x k.wood k.tag V).real (Prod.snd ⁻¹' away (parasol (T' i) t) (haze G f₀ R.beta S.patch.L/2))) ≤ 1) : Spot Q (troupe R Q L ht hs hv Z f₀ T' t hq) lightcast T l r e (salary e*k+salary e*k):= by
  obtain ⟨c,h,H⟩:=H
  let F(i:ι):=penny (Z i).extent R.p e (c i)
  have hz := haze_pos (G:=G) hx hb S.patch.L
  let M := Sum.elim F F; have hm i:0≤M i:=by cases i with|inl i=>exact penny_nn _ _ (h i).1|inr i=> exact penny_nn _ _ (h i).1
  refine ⟨M,hm,?_,?_,?_⟩
  · intro i A U k z hu
    have he i b : stroke (flakeTone (P0 b i)) r A k U z ≤ F i:= by
      let y:= (ray R L f₀ T' t i A k U z); let g:=if b then y else 1-y
      have hh:= (paid_veil (parasol (T' i) t) L.χ _ hz).probability z.2
      have hg:0≤g ∧ g≤1:=by unfold g; change 0≤y ∧ y≤1 at hh; split <;> (constructor <;> linarith only [hh.1,hh.2])
      apply le_trans _ (bead_worth R Q L ht hs hv (Z i) hr (h i) U k A z)
      change Poly.toll r (Z i).fires*‖g • (JH i).face A k U z‖ ≤ Poly.toll r _ * ‖(JH i).face A k U z‖
      rw [norm_smul,Real.norm_of_nonneg hg.1]; exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hg.2) (Poly.worth hr _).le
    rcases i with i|i; exact he i true; exact he i false
  · rintro (i|i) hi U A k hA
    · exact False.elim (hi trivial)
    refine Or.inr ⟨_, measurable_snd (away_meas ..),he i U A hA k,fun y hy=> ?_⟩
    have ht: ray R L f₀ T' t i A k U y=1:= (paid_veil _ L.χ _ hz).plateau _ (Classical.not_not.mp (show ¬¬Guards (parasol (T' i) t) y.2 _ from hy))
    change Poly.toll r _ * ‖(1-ray R L f₀ T' t i A k U y) • _‖ =0; rw [ht]; simp
  intro i
  rw [Flux.locus]
  have he:= price_wave S Z c (fun i=>(h i).1) hR zero_le_one le_rfl H i; simp_rw [one_mul] at he
  exact add_le_add he he
end YM.PhysicalNext.InteractingRank.Display.Docking
