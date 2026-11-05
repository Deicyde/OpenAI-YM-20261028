import YM.Next.RANK.Flux.Conductor
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Dockets
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gallery

/-!
# Accumulate packed logarithm inputs, at the required finite Rank weights

Opening from seam tariffs, not an assumption on summed clusters.

Mercy: owes
also actual unmarked holes costs (phase) from supplied Vac as specified.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Filter
open scoped Topology BigOperators Classical ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ e h₀ : ℝ} {L : Lantern G S} {F : Orchard S} {T : Tube G S}
    {A : Stores S} {P : Teller G} {W ι κ α : Type} [Fintype W] [DecidableEq W] {θ : W→Site f} {u : W→Site c}
section backend
variable [Fintype ι] (Q : ι→PaintCan S G x F u τ) (g : ι→ℝ) (P' : BudgetPoint)
lemma inks (Can : Club Q→Prop) (hp : Hits (zones Q) g P' (e+1) h₀) (ht : Risible P'.B h₀) (hg : ∀ i,0≤g i) (he : 0≤e) :
    Hits (fun i : Subtype Can=> zone Q i.val) (fun i : Subtype Can=> ∏ j∈ i.val.val,g j) P' e (Real.exp h₀-1) := by
  intro V
  let F' (i : Subtype Can):Prop := V∈zone Q i.val
  letI : DecidablePred F':=fun _=>Classical.propDecidable _; let F:= univ.filter F'
  let p(i:Subtype Can):= i.val.val
  have hf : Injective p := Subtype.val_injective.comp Subtype.val_injective
  have H:= Ac.forest (zones Q) P'.B he hg (quotas _ _ _ hg hp) ht.grain ht.day V
  let g' := Ac.roots (zones Q) P'.B g e V
  apply le_trans (b:=∑ i∈ F.image p, g' i)
  · rw [Finset.sum_image hf.injOn]; change (∑ i∈F, alarm (fun i : Subtype Can=>zone Q i.val) (fun i : Subtype Can=>∏ j∈ p i,g j) P'.B e i ) ≤ _
    apply sum_le_sum; intro i hi
    unfold g' Ac.roots; rw [if_pos (show Spark (zones Q) _ ∧ V∈ (p i).biUnion (zones Q) from ⟨i.val.property.1,(mem_filter.mp hi).2⟩)]; exact (mul_comm ..).le
  exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> H.1 i)).trans ((tsum_fintype ..).symm.trans_le H.2.2)
lemma probes (hp : Hits (zones Q) g P' (e+1) h₀) (ht : Risible P'.B h₀) (hg : ∀ i,0≤g i) (he : 0≤e) (i : W):
    strike (fun i:Inn Q=> zone Q i.val) (fun i : Inn Q=>∏ j∈i.val.val,g j) P' (fun j=>i∈(fires Q j.val.val).val) e ≤ strike (zones Q) g P' (fun j=>i∈(Q j).hues.val) (e+1):= by
  let a := alarm (fun i:Inn Q=> zone Q i.val) (fun i=>∏ j∈i.val.val,g j) P'.B e
  have hz j:0≤a j:= alarm_pos _ _ _ _ (fun j=> prod_nonneg fun i _=>hg i) j
  let T (j:Inn Q):Prop:=i∈(fires Q j.val.val).val
  let P(j:ι):Prop:=i∈(Q j).hues.val
  letI : DecidablePred T:=fun a=>Classical.propDecidable _; letI : DecidablePred P:=fun a=>Classical.propDecidable _
  change (∑ i∈univ.filter T,a i) ≤ ∑ j∈univ.filter P,alarm (zones Q) g P'.B (e+1) j
  apply promote a (alarm (zones Q) g P'.B (e+1)) (univ.filter T) (univ.filter P) (fun i j=> j∈i.val.val) (fun i _=>hz i)
  · intro j hj; obtain ⟨k,hk,h⟩:=mem_biUnion.mp (show _ from (mem_filter.mp hj).2); exact ⟨k,mem_filter.mpr ⟨mem_univ _,h⟩,hk⟩
  intro j hj S hs hu
  let v(s : Inn Q):=s.val.val
  have hf : Injective v:= Subtype.val_injective.comp Subtype.val_injective
  have hx t h: j∈ v t:= hu t h
  let P(s:Finset ι):=(∏ i∈s,g i)* Value.charge P' e (s.biUnion (zones Q))
  rw [show ∑ j∈S,a j=∑ i∈S.image v,P i by rw [Finset.sum_image hf.injOn]; rfl]
  apply le_trans _ (anchor_tag (zones Q) g P' j hg hp he ht.grain ht.day)
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi; obtain ⟨t,hh,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _,t.val.property.1,hx t hh⟩
  exact fun i _ _=> mul_nonneg (prod_nonneg fun i _=>hg i) (Real.exp_pos _).le
end backend
section
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (K : κ→ Lifted G θ R.p.threshold)
    (H : α → Flake S G x L.park u R'.p.threshold) (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ) (C : α→Prop)
    (z : ι→ℝ) (v : κ→ℝ) (w : α→ℝ) [Fintype ι] [Fintype κ] [Fintype α]
local notation "Q"=> picture R R' p K H ht hs hv
local notation "HC"=> LetterCost R R' p K H ht hs hv C z v w
local notation "B"=> bid z v w
local notation "GQ"=> Gathered R R' p K H ht hs hv C

-- Restoration receipts from unmarked supplier: pay exactly hole refreshes;
-- Y decremented for source use via packing names. No arithmetic here beyond physical demand.
def Reparations (u : W→Site c) (R : Rep G c) (p : Flux.Vac u R) (r : W→ℝ) (e l h₂ h₃ : ℝ) := ∃ (v : p.R → ℝ) (w : p.K → ℝ),
    (∀ i,0≤v i) ∧ (∀ i,0≤w i) ∧ (∀ i U,l*Poly.price r ((raised (measureH p i)).covets U) ≤ v i) ∧
      (∀ i U, Poly.price r ((p.pay i).covets U) ≤ w i) ∧ Hits (fun i=> (raised (measureH p i)).extent) v R.p (ucap e) h₂ ∧
      Hits (fun i=> (p.pay i).extent) w R.p (ucap e) h₃
lemma repair_lower {e l k a b : ℝ} {p : Flux.Vac u R'} (r) (hr : ∀ i,0<r i) (h : Reparations u R' p r e k a b) (hl : l ≤ k) : Reparations u R' p r e l a b := by
  obtain ⟨v,p,hv,hp,H,h⟩:=h; exact ⟨v,p,hv,hp,fun i U=> (mul_le_mul_of_nonneg_right hl (Poly.nonnegative hr _)).trans (H i U),h⟩
omit [Fintype ι] [Fintype κ] [Fintype α] in
lemma learned_club {r l m} (hp : HC l m r) (hl : 1≤l) (hm : 1≤m) (hr : ∀ i,0<r i) (i : Club Q) (U) :
    tune R R' p K H ht hs hv C i l m * Poly.price r (proceeds Q T i U) ≤∏ j∈ i.val,B j := by
  rw [proceeds]; split
  next he =>
    rw [Poly.solo,← mul_assoc]; let L':= letter Q (T:=T) i U; let q:= Poly.toll r (fires Q i.val); let t:=tune R R' p K H ht hs hv C i l m
    let P:=∏ j ∈ i.val,B j
    change (t*q)*‖L'‖≤P
    let A:=stapled x (glow Q i.val) U; let μ(k:Streak L.park):= viewer T A x k.wood k.tag U
    let g k := stage Q i.val A k U; let q':=t*q; have hq:0≤q':=mul_nonneg (zero_le_one.trans (tune_safe R R' p K H ht hs hv C hl hm i)) (Poly.worth hr _).le
    have he' k:q' * ‖ ∫ y, g k y∂μ k‖ ≤ P:= (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hq).trans (refund R R' p K H ht hs hv C z v w hp hr hl hm i U k he).2
    calc
      _ ≤ q' * ∑ k, ‖Streak.share k • ∫ y,g k y∂μ k‖ := mul_le_mul_of_nonneg_left (norm_sum_le ..) hq
      _ ≤ ∑ k : Streak L.park,Streak.share k*P := by
        rw [Finset.mul_sum]; apply Finset.sum_le_sum;intro k _
        have hh : 0≤Streak.share k:= k.share_nn
        rw [norm_smul,Real.norm_of_nonneg hh, mul_left_comm]; exact mul_le_mul_of_nonneg_left (he' k) hh
      _ = _:= by rw [← Finset.sum_mul,Streak.full ht.produced.branched,one_mul]
  rw [Poly.zero_price,mul_zero]; exact Finset.prod_nonneg fun i _=> incomes _ _ _ _ _ _ _ _ _ _ _ _ hp i

def Glaze (i : Inn Q) := GQ i.val
local notation "GQ1"=> Glaze R R' p K H ht hs hv C

-- Populate the `rawRadii` estimates above this compilation.
lemma finances (V : Flux.Vac u R') {l m r s n h} (hp : HC l m fun _=>r) (hl : 1≤l) (hm : 1≤m) (hr : 0<r)
    (hV : Reparations u R' V (fun _=>r) e l h s) (he : 0≤e)
    (hb : Hits (zones Q) B R'.p (ucap e+1) h₀) (hA : Risible R'.p.B h₀) (hh : Real.exp h₀-1+h≤s) (hx : ∀ i : W,strike (zones Q) B R'.p (fun j=> i∈(Q j).hues.val) (ucap e+1) ≤ n):
    rawRadii V (bequeath Q ht) GQ1 r e m l s n:= by
  obtain ⟨y,p',hy,hp',hv',hE,hF,hK⟩:= hV
  let T':= bequeath Q ht; let g(i:Inn Q):= ∏ j∈i.val.val,B j; let f:= Sum.elim g y
  have hm': 0≤ ucap e := by unfold ucap; linarith only [he]
  have hg : ∀ i,0 ≤ B i:= incomes _ _ _ _ _ _ _ _ _ _ _ _ hp
  have hf i: 0≤g i:=prod_nonneg fun i _=>hg i
  refine ⟨f,p', ⟨fun i=>?_,hp',fun i U=>?_,hv',hE, plus_hits _ _ g y _ ?_ hF hh,hK,fun i=>?_⟩⟩
  · rcases i with i|i; exacts [hf i,hy i]
  · have hh: (T' i).landed ↔ (cardGoal Q i.val.val).Nonempty := by rw [Plug.landed]; unfold T'; rw [(heirs Q ht i).2.2.1]
    have H:= learned_club R R' p K H ht hs hv C z v w hp hl hm (fun _=>hr) i.val U
    rw [← (heirs Q ht i).2.2.2 U] at H
    split_ifs with hg
    · rw [show tune ..=m from if_pos (hh.1 hg)] at H; exact H
    rw [tune,if_neg (show ¬_ from mt hh.2 hg)] at H; exact H
  · rw [show (fun i=> (bequeath Q ht i).extent)=(fun i:Inn Q=> zone Q i.val) from funext fun i=>(heirs Q ht i).2.1]
    exact inks Q B _ (promotes Q) hb hA hg hm'
  let k:= ucap e; let p₁:=measureH V; let D' := dish T' p₁; let q':=R'.p
  let U (j : _⊕V.R) : Prop:= ∃ p,j=.inl p ∧ ¬(T' p).landed ∧ i∈(T' p).fires.val
  have hL(j:Inn Q):D' (.inl j)=zone Q j.val:= (dishfest T' p₁ j).trans (heirs Q ht j).2.1
  have hh : strike (D'∘Sum.inl) g q' (U∘Sum.inl) k ≤ strike (zone Q ∘ Subtype.val) g q' (fun j : Inn Q=>i∈(fires Q j.val.val).val) k:= by
    rw [show (D'∘ Sum.inl)=zone Q ∘ (Subtype.val : Inn Q → Club Q) from funext hL]
    apply supple (h:=?_) (he:=hf); rintro j ⟨t,h,h',hQ⟩
    have hz:=heirs Q ht t|>.1; exact Sum.inl.inj h|>.symm ▸ (show _ from hz ▸ (show i∈(bequeath Q ht t).fires.val from hQ))
  change strike D' f q' U k ≤ n; rw [Flux.locus]
  have hZ : strike (D'∘ Sum.inr) (f∘Sum.inr) q' (U∘Sum.inr) k=0:= by unfold strike U Function.comp; simp
  rw [hZ,add_zero]; exact hh.trans ((probes Q B _ hb hA hg hm' i).trans (hx i))
end
end YM.PhysicalNext.InteractingRank.Display
