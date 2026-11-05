import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.Extra.MULTISOURCE_TRAJECTORIES.Hangers
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Pattern
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Tissue
import YM.Push.RELAY_DIFFERENCE.Shuffles
import YM.Push.STRESS_FLUX.Orbits
/-!
# Reindex the Soft addends

Keep orientation at every stencil for further computations. `appendE`
integrates with previous K sheets: only the new budgeted E values on top,
no assertion that an old, kernel-paid system automatically aligns hereafter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Next.Rank RankCovariance Thirst Pump
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι : Type} {p : BudgetPoint} {r d τ : ℝ}
section spin
def cash (n : Side) := (Fintype.card (Wheel n):ℝ)⁻¹
variable (P : ι→ Piece G n τ)
def market (v : Wheel n × ι) := ((P v.2).turn v.1).reweight (cash n)
lemma solidity {P : ι→ Piece G n p.threshold} (h : Pieces (p:=p) P d) : Pieces (p:=p) (market P) d:=by
  have he : 0 ≤ cash n:= inv_nonneg.mpr (Nat.cast_nonneg _)
  apply Pieces.across (Pieces.eachAxis (fun _=> |cash n| *d) fun i=> ((h.turn i).scaling (cash n)))
  have ht : (Fintype.card (Wheel n):ℝ)>0:= by exact_mod_cast (Fintype.card_pos (α:=Wheel n))
  simp only [sum_const,card_univ,nsmul_eq_mul,abs_of_nonneg he]; unfold cash; rw [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
lemma Piece.scale_turn (i : Piece G n τ) (x y : Wheel n) : orient (meet x y) i.atWay.site= orient x (orient y i.atWay.site) := together ..
def changeE (e : Wheel n) : Equiv.Perm (Wheel n × ι) := (gear e).prodCongr (Equiv.refl _)
variable (X : ι→ Piece G n p.threshold)
lemma site_e (e : Wheel n) (x) : (market X (changeE e x)).atWay.site=orient e (market X x).atWay.site:= (X x.2).scale_turn e x.1
lemma support_e (e : Wheel n) (x) : (market X (changeE e x)).atWay.support=swath e.1 e.2 (market X x).atWay.support:= (swath_comp ..).symm
lemma value_e (e : Wheel n) (x) V : (market X (changeE e x)).value V=(market X x).value (pull e.1 e.2 V):=
  congr_arg _ (congr_arg _ (pull_pull ..).symm)

lemma markets_unchanged (h : Pieces (p:=p) X d) (V) (hV : ∀ k : Wheel n,∑' i,(X i).value (pull k.1 k.2 V)=∑' i,(X i).value V) : (∑' i,(market X i).value V)=∑' i,(X i).value V := by
  rw [((solidity h).all V).tsum_prod,tsum_fintype]
  have ht : (Fintype.card (Wheel n):ℝ)>0:= by exact_mod_cast (Fintype.card_pos (α:=Wheel n))
  change ∑ e : Wheel n,∑' i,cash n*(X i).value (pull _ _ _)=_
  simp_rw [tsum_mul_left,hV]; unfold cash; rw [Finset.sum_const,card_univ,nsmul_eq_mul,← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
end spin

-- include infinite zero padding only if needed by the deployment. Work with P as determined (no K padding theorem from palette independence)
variable (Q : Rep G n) (X : ι→ Piece G n Q.p.threshold) (e : ℕ ≃ Wheel n × ι)
def appendE : Rep G n := {Q with activities :=
  { Q.activities with
      reg:=fun i=> (market X (e i)).atWay
      E:= fun i=>(market X (e i)).value } }
local notation "Φ"=>market X
local notation "R"=>appendE Q X e
lemma cost_e (i) U : (R).activities.regularOccurrence (R).p i U=(Φ (e i)).value U:=by
  unfold Activities.regularOccurrence; by_cases h: (Φ (e i)).value U=0
  swap
  · exact masked_eq _ _ _ _ ((Φ (e i)).leave U h)
  by_cases hv: Healthy Q.p.threshold (Φ (e i)).atWay.support U
  exact masked_eq _ _ _ _ hv
  change masked Q.p.threshold (Φ (e i)).atWay.support _ _=_; rw [masked_ne _ _ _ _ hv]; exact h.symm
lemma pollen (h : Pieces (p:=Q.p) X d) : Petals R d := by
  have h0 i : (R).activities.regularOccurrence (R).p i =(Φ (e i)).value:= funext (cost_e Q X e i)
  obtain ⟨c,hv,h⟩:= (solidity h).worth
  refine ⟨fun i=> h0 i|>.symm ▸ (Φ (e i)).gauge,fun i=>h0 i|>.symm ▸ (Φ (e i)).probes,fun i=> h0 i |>.symm ▸ (Φ (e i)).look,c ∘ e,fun i=> ?_,fun i=> ?_⟩
  · rw [h0]; exact hv _
  let f (j:Wheel n × ι):= if (Φ j).atWay.site=i then Q.p.mass (Φ j).atWay.support (c j) else 0
  have hh : SumBudget f d:= h i
  exact ⟨fun i=>hh.1 _,hh.2.1.comp_injective e.injective,(e.tsum_eq f).trans_le hh.2.2⟩
lemma represented (h : Pieces (p:=Q.p) X d) (V : Config G n) (hV : ∀ k : Wheel n, (∑' i,(X i).value (pull k.1 k.2 V))=∑' i,(X i).value V) : (R).activities.additive (R).p V=∑' i,(X i).value V:= by
  apply (tsum_congr (cost_e Q X e · V)).trans; exact (e.tsum_eq (fun i=> (Φ i).value V)).trans (markets_unchanged X h V hV)
lemma subjects (a : Signed) (z : Site n) (H : Nonempty (Q.activities.Moves a z)) : Nonempty ((R).activities.Moves a z):= by
  obtain ⟨H⟩:=H; let f:= e.trans ((changeE (a,z)).trans e.symm)
  have he i : e (f i)= changeE (a,z) (e i):= e.apply_symm_apply _
  refine ⟨f,H.kp,fun i=>?_,fun i=>?_,H.forced_support,H.forced_inventory,H.forced_tests,fun i=> ?_, H.valuesK⟩
  · change (Φ (e (f i))).atWay.site=_; rw [he]; exact site_e X (a,z) _
  · change (Φ (e (f i))).atWay.support=_; rw [he]; exact support_e X (a,z) _
  intro U; change (Φ (e (f i))).value U=_; rw [he]; exact value_e X (a,z) _ U
end YM.PhysicalNext.InteractingRank.Soft
