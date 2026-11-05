import YM.MergeProof.Badlands
import YM.Next.RANK.Compass

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Spindle Extra.Multi Motion Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{d:ℕ}{F:Labels.Frame G d}(B: SectionData F){s:Side} (A:Rep G s)(o:Site s)(P:Coefficient F s)
section
variable (U:Config G s) {u C k t:ℝ}
lemma tendrils (h:P.remBound o A k t)(hk:k≤1) : ‖∑' i,P.maskedTerm A i U‖≤ t ∧ (∑ i,‖profile A.activities P.forced i U‖) ≤ t:=by
    obtain ⟨a,b,hA,hB,he,hD,⟨u,hX,hU⟩,y,hP,h⟩:=h
    have hu:Summable u:= hX.2.1.of_nonneg_of_le (fun i=> (hU i).1) (fun i=> A.p.loMass _ _ (hU i).1)
    have hv:Summable y:= hP.2.1.of_nonneg_of_le (fun i=> (h i).1) (fun i=> A.p.loMass _ _ (h i).1)
    have hh(i): ‖P.maskedTerm A i U‖ ≤ u i:=by
       unfold Coefficient.maskedTerm;by_cases ht:Healthy A.p.threshold (P.support i) U
       · rw [masked_eq _ _ _ _ ht]; exact (hU i).2 U ht [] (by simp) (by simp)
       rw [masked_ne _ _ _ _ ht,norm_zero]; exact (hU i).1
    have hx:= hu.of_nonneg_of_le (fun i=> norm_nonneg _) hh
    refine ⟨(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum hh hu).trans ((hu.tsum_le_tsum (fun i=> A.p.loMass _ _ (hU i).1) hX.2.1).trans (hX.2.2.trans (le_trans (le_add_of_nonneg_right hB) he)))),?_⟩
    let s:=barcode A.activities
    apply le_trans (Finset.sum_le_sum (g:=cram s y) (fun i _=> metric_cram s hv (fun i=> (h i).2 U) _))
    have he':= (MergeProof.heavy s hv).tsum_eq; rw [tsum_fintype] at he'; rw [he']
    exact (hv.tsum_le_tsum (fun i=> A.p.loMass _ _ (h i).1) hP.2.1).trans (hP.2.2.trans ((mul_le_of_le_one_left hB hk).trans (le_trans (le_add_of_nonneg_left hA) he)))
lemma hull {t:ℝ}(hB:∀ i:F.Index, A.p.Regular (B.footprint o) (B.places (Pi.single i 1) o) ∧ A.p.supBounds o (B.footprint o) (B.places (Pi.single i 1) o) (C*A.p.threshold^(F.grades i).2)) (h:P.remBound o A k t)(he:k≤1)(hc:0 ≤ C): ‖P.exponentialEntry o B A U‖ ≤ (1+C)*F.coeffSize P.x + t:=by
    unfold Coefficient.exponentialEntry; refine (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans ?_) (tendrils A o P _ h he).1)
    rw [add_mul,one_mul]; refine add_le_add (BasisCost.coord_le P.x _) ?_
    by_cases ht:Healthy A.p.threshold (B.footprint o) U
    · rw [masked_eq _ _ _ _ ht]; exact ((BasisCost.analytic B A.p (F.core P.x) o hB).2.2 U ht [] (by simp) (by simp) : ‖B.places _ _ _‖ ≤ _).trans (mul_le_mul_of_nonneg_left (BasisCost.coeff_le P.x) hc)
    rw [masked_ne _ _ _ _ ht,norm_zero]; exact mul_nonneg hc (BasisCost.coeff_nonneg P.x)
end
section
variable (C:Family G)(v:C.label d) (k p N : ℕ) (s : Motion) (o:∀ i:ℕ, Site (C.side i p))
local notation "K"=> C.path.rep N p k
local notation "Z"=> parcel C d k N p v
local notation "F'"=> C.labels.level d
local notation "α"=> pinHat C d k
set_option quotPrecheck false
lemma scratch (h:C.Makes)(hk:C.ref d ≤ k)(ht:k≤N) (U): ‖indexX C d N p v o s k U‖ ≤ 3*moneys C d k N p v ∧ (∑ j, ‖Ktone C d N p v o s k j U‖) ≤ moneys C d k N p v:=by
   let T:=col C k; have hf:= col_ge C k
   let Y:= Z; let κ:= divisor C k
   let y:= T*(C.labels.level d).coeffSize (F'|>.core Y.x); have hP:Y.remBound 0 K κ y:= (h.calibrated d N p (hk.trans ht)).cap k hk ht _
   have hr:(K).p=point C k:= (h.wilson.represents N p k ht).vac; let g:=pull s.1 (o k) U
   let P:=K; let f(i):=(C.labels.level d).coeffSize i
   have hv : 1≤ T:= col_ge ..
   have hp: y ≤ T*f Y.x:= mul_le_mul_of_nonneg_left (BasisCost.coeff_le _) (zero_le_one.trans hv)
   have hX :moneys C d k N p v= ‖α‖*(T*f Y.x):= by
      change T*(C.labels.level d).coeffSize (α • Y.x)=_; rw [Extra.Histories.Size.smul]; exact mul_left_comm ..
   rw [hX]; constructor
   · change ‖α * scalar s (Y.exponentialEntry 0 (C.localSection d) P g)‖ ≤ _; rw [norm_mul,norm_scalar, mul_left_comm (3:ℝ),← mul_assoc (3:ℝ)]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
     have he:= hull (C.localSection d) P 0 Y g (C:=T) (fun i=> by change (K).p.Regular _ _ ∧ (K).p.supBounds _ _ _ (T*(K).p.threshold ^ _); rw [hr]; exact h.priced d k p hk 0 i) hP (divisor_le ..) (zero_le_one.trans hv)
     apply he.trans; have ht:=le_mul_of_one_le_left (show 0 ≤ f Y.x from BasisCost.coeff_nonneg _) hv; linarith only [hp,ht]
   let h:=puff s (o k); rw [← Equiv.sum_comp h]; unfold Ktone sunny; simp_rw [Pi.smul_apply,smul_eq_mul,floatUp]; simp only [h, Equiv.symm_apply_apply]; unfold stepUp
   simp_rw [norm_mul,norm_scalar,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((tendrils _ 0 Y g hP (divisor_le ..)).2.trans hp) (norm_nonneg _)
end
end YM.MergeProof.Accent
