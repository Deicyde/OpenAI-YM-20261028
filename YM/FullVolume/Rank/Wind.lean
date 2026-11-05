import YM.FullVolume.Rank.Lucid
/-! Posts through ropes after chart alignment at all requested orientations. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι κ:Type}
open Push.AbsoluteSums Finset
namespace Rank
local notation "R"=> S.orient
abbrev Doll (t:ℕ→ Coefficient F n)(A:Hol G)(S:Desk G n)(v:ℝ): Prop:=∀ i,(t i).Format 0 A S.orient∧ (t i).remBound 0 S.orient S.k v∧ F.coeffSize (t i).x ≤ v
structure Hue (p q:ℕ→ Coefficient F n)(A:Hol G)(S:Desk G n):Prop where
   same i :(p i).support=(q i).support
   reads: Tendsto (fun i=> (p i).x-(q i).x) atTop (𝓝 0)
   turns i:(breakP (p i) (q i)).Format 0 A S.orient
   sent (v:ℝ)(h:0<v):∀ᶠ i in atTop,(breakP (p i) (q i)).remBound 0 S.orient S.k v
-- singular.True. Use epsilon cutoff charges.Rates
variable {p t:ℕ→ι→ Pin F n} {f:ι→ℝ}
lemma slip (P Q:File G n) {u v:F.Coeff}{p:Rep G n}(h:(book u P).Format 0 A p)(ht:(book v Q).Format 0 A p){a b k:ℝ}(hp: (book u P).remBound 0 p k a)(hz: (book v Q).remBound 0 p k b): (breakP (book u P) (book v Q)).Format 0 A p ∧ (breakP (book u P) (book v Q)).remBound 0 p k (a+b) :=by
    let f:= -Q; let j:=(-1:ℂ); have hh:Extra.Histories.stretch (-1) (book v Q)=book (-v) f:=by rw [disguise]; simp only [neg_smul,one_smul]; rfl
    have hq:=stretch_format j ht; have hZ:= stretch_rem j hz; unfold j at *; rw [hh] at hq hZ; rw [norm_neg,norm_one,one_mul] at hZ
    have h₂ : breakP (book u P) (book v Q)=book (u-v) (P+f):=by rw [show P+f=P-Q from (sub_eq_add_neg ..).symm];rfl
    rw [h₂]; exact ⟨formatK F _ _ (format_add F u (-v) h hq),boundK F _ _ (remAdd F _ h (formatK F _ _ hq) hp (boundK F _ _ hZ))⟩
lemma equips {w:ι→ℝ}(hw:Summable w)(r:ℝ)(ht:0<r){C:ℕ→ι→ ℝ→Prop}(h:∀ i k,C i k (w k))(he:∀ i v,v>0 →∀ᶠ n in atTop,C n i v)(hz:∀ i,0≤w i):∀ᶠ n in atTop,∃ v, (∀ i,C n i (v i))∧SumBudget v r := by
    obtain ⟨Z,hZ⟩:= (Sparse.constant hw hz).stalls _ (half_pos ht); let v:= (r/2)/(Z.card+1); have hv:0<v:=by unfold v; positivity
    filter_upwards [(eventually_all_finset Z).2 (fun x _=>he x v hv)] with i hi;let g p:= if p∈Z then v else w p; have hh p:0≤ g p:= by unfold g; split <;>first|exact hv.le|exact hz _
    refine ⟨g,fun x=>?_,budget_of_sum hh fun S=>?_⟩
    · unfold g;split; next hp=>exact hi x hp
      next=>exact h ..
    let T:= S.filter fun i=> i∉ Z; let H:=S.filter fun i=>i∈Z
    rw [← sum_filter_add_sum_filter_not S (fun i=> i∈Z)]; change ∑ i∈H,g i+∑ i∈T,g i ≤r
    have hs : H⊆Z:= fun i hi=> (mem_filter.mp hi).2
    refine (add_le_add (?_ : ∑ i∈H,g i ≤ r/2) (?_ : ∑ i∈T,g i ≤r/2)).trans_eq (add_halves r)
    · rw [sum_congr rfl (g:=fun _=>v) (fun i hi=>if_pos (hs hi)),sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((Finset.card_le_card hs).trans (Nat.le_add_right _ 1))) hv.le).trans_eq (by push_cast; unfold v; field_simp)
    rw [sum_congr rfl (g:=w) (fun i hi=> if_neg ((mem_filter.mp hi).2))]; exact hZ 0 _ (Finset.disjoint_left.mpr fun i hi hx=> (mem_filter.mp hx).2 hi)
lemma uplift [Countable ι](ℓ : ℕ≃ι×ℕ)(h: Summable f) (he:∀ i,Doll (fun n=> Matric.tell (p n i)) A S (f i))(hp:∀ i,Doll (fun n=> Matric.tell (t n i)) A S (f i))(hv:∀ i,Shift S (fun n=>p n i) (fun n=>t n i)): Hue (fun i=>Extra.Histories.merge ℓ (Matric.tell ∘ p i)) (fun i=> Extra.Histories.merge ℓ (Matric.tell ∘ t i)) A S:=by
    let H(n k):=Matric.tell (p n k); let T n k:=Matric.tell (t n k); let X n i:= breakP (H n i) (T n i)
    have ht(G:ℕ→ι→ Pin F n)(hv:∀ i,Doll (fun n=> Matric.tell (G n i)) A S (f i)) (n):
       SumBudget (fun i=> ‖(G n i).1‖) (∑' i,f i) ∧ ∀ i V,Summable (fun k=>(G n k).2.2 i V) :=by
      refine ⟨budget_mono (show SumBudget f (∑' i,f i) from ⟨fun x=> rem_nonneg (hp x 0).2.1,h,le_rfl⟩) (fun i=>norm_nonneg _) (fun i=> (norm_le_size ..).trans (hv i n|>.2.2)),fun i V=>?_⟩
      exact ((((merge_budget ℓ _ S.sane (fun i=>(hv i n).2.1) h).2.2.summable V).prod_symm).prod_factor i)
    have hf : Sparse (fun _ : ℕ=> f):= Sparse.constant h (fun i=> rem_nonneg (hp i 0|>.2.1))
    have hM(n):Extra.Histories.merge ℓ (X n)=breakP (Extra.Histories.merge ℓ (Matric.tell ∘ p n)) (Extra.Histories.merge ℓ (Matric.tell ∘ t n)):= melt ℓ (ht p he n).1.2.1.of_norm (ht t hp n).1.2.1.of_norm (ht p he n).2 (ht t hp n).2
    have hh n i: (X n i).Format 0 A (R)∧ (X n i).remBound 0 R S.k (f i+f i):= slip _ _ (he i n).1 (hp i n).1 (he i n|>.2.1) (hp i n|>.2.1)
    refine ⟨fun i=>rfl, fisher (hf.smaller (fun i j=> norm_nonneg _) (fun n i=> (Local.norm_le_size ..).trans (he i n|>.2.2))) (hf.smaller (fun i j=> norm_nonneg _) (fun n i=> (Local.norm_le_size ..).trans (hp i n|>.2.2))) (fun i=> (hv i).charge),fun i=> hM i ▸ merge_format ℓ (X i) (fun j=> (hh i j).1), fun r hr=>?_⟩ -- syntax slip
    let w n i(p:ℝ):= (X n i).remBound 0 R S.k p; filter_upwards [equips (C:=w) (w:=fun i=> f i+f i) (h.add h) r hr (fun n i=>(hh n i).2) (fun i b he=> trigger (hv i) b he) (fun i=> rem_nonneg (hh 0 i).2)] with n hn; rw [← hM n]; obtain ⟨v,hv,h⟩:= hn; exact rem_mono (merge_budget ℓ (X n) S.sane hv h.2.1|>.1) h.2.2
end Rank
end YM.FullVolume.Paint
