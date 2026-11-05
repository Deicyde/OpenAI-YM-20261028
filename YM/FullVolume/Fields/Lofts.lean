import YM.FullVolume.Fields.Basin
import YM.FullVolume.Table.Vars
/-! EOS.Strong evaluation, without measure null tail.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Retreat
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom MergeProof MergeProof.Accent MergeProof.Menu Motion Extra.Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Finset Urns
variable {G: Gauge}{n:Side}{S:Urns.Price G n}
local notation "X"=> Show S
variable {f:X}
open Push.AbsoluteSums
private lemma total (M:ℕ→ℝ) (v:Site n→ℕ→ℝ)(w:ℝ)(h:∀ x,SumBudget (v x) w)(hv:∀ i,0≤ M i)(hp:∀ i,M i≤∑ x,v x i): SumBudget M (Fintype.card (Site n)*w):=by
    apply budget_of_sum hv; intro K; apply le_trans (Finset.sum_le_sum fun j _=> hp j); rw [sum_comm]; simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (s:=univ) (g:=fun _=>w) (fun i _=>budget_sum (h i) K)
lemma storedE (f:Show S): let A:= f.proper.regularOccurrence S.p; ∃ a:ℕ→ℝ,SumBudget a ((Fintype.card (Site n)*S.b)*‖f‖) ∧ ∀ i U, ‖A i U‖≤a i:=by
    intro A; obtain ⟨b,hb,hK⟩:= (Show.budget f ‖f‖|>.mp le_rfl).2.2.1; let T i:= f.proper.reg i
    let v(x:Site n)(i:ℕ):=if (T i).site=x then S.p.mass (T i).support (b i) else 0
    have hh(x): SumBudget (v x) (‖f‖*S.b):=hK x
    refine ⟨b,?_,fun i U=>?_⟩
    · rw [mul_assoc,mul_comm S.b]; apply total b v _ hh (fun i=>(hb i).1) _; intro i; simp_rw [v,sum_ite_eq,Finset.mem_univ,if_true]; exact S.p.loMass _ _ (hb i).1 -- syntax
    unfold A Activities.regularOccurrence
    by_cases h:Healthy S.p.threshold (T i).support U; rw [masked_eq _ _ _ _ h]; exact (hb i).2 U h [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ h,norm_zero]; exact (hb i).1
lemma storedK (f:Show S): let A:=f.proper.K; ∃ a:ℕ→ℝ,SumBudget a ((Fintype.card (Site n)*S.k)*‖f‖) ∧ ∀ i U, ‖A i U‖≤a i:=by
    intro A; obtain ⟨b,hb,hK⟩:= (Show.budget f ‖f‖|>.mp le_rfl).2.2.2; let T i:= f.proper.forced i
    let v (x:Site n)(i:ℕ):= if x∈(T i).support then S.p.mass (T i).support (b i) else 0; have h (x):SumBudget (v x) (‖f‖*S.k):= hK x
    refine ⟨b,?_,fun i U=> (hb i).2 U⟩; rw [mul_assoc,mul_comm S.k]; apply total b v _ h (fun i=>(hb i).1); intro i; obtain ⟨x,hx⟩:= (T i).inventory_ne.mono (T i).inventory_sup; refine (S.p.loMass (T i).support _ (hb i).1).trans ((show S.p.mass (T i).support (b i)=v x i from Eq.symm (if_pos hx)).trans_le (single_le_sum (fun k _=> (h k).1 i) (Finset.mem_univ x)))
variable {E:Type}[NormedAddCommGroup E][CompleteSpace E]
lemma currency {ι:Type}{f:ι→E}{a:ℝ}(h:∃ b:ι→ℝ, SumBudget b a∧ ∀ i, ‖f i‖≤b i): Summable f ∧ ‖∑' i,f i‖≤ a:= by
    obtain ⟨b,hf,hc⟩:=h; have hp: SumBudget (fun i=> ‖f i‖) a:=Extra.Multi.Budget.mono hf (fun i=>norm_nonneg _) hc le_rfl; exact ⟨hp.2.1.of_norm,(norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2⟩
-- Vase etc via sheers
variable {p:ℕ→ Show S} (hc:CauchySeq p)
include hc
lemma vases : Confluence (fun n=> (p n).proper.additive S.p):=by
   let q x:= (x:Show S).proper.additive S.p
   have he (x:Show S)(U:Config G n):= currency (f:=fun i=> x.proper.regularOccurrence S.p i U) (by obtain ⟨b,hb,hA⟩:=storedE x; exact ⟨b,hb,fun i=> hA i U⟩)
   refine sheers q (Fintype.card (Site n)*S.b) p (fun _=>⟨_,fun U=> (he _ U).2⟩) (fun x y U=>?_) hc -- existential inference.dep
   rw [dist_eq_norm,dist_eq_norm]
   have hm:q x U-q y U=q (x-y) U:= by
       unfold q Activities.additive; rw [← Summable.tsum_sub (he _ U|>.1) (he _ U|>.1)]; apply tsum_congr; intro i; unfold Activities.regularOccurrence; let T:= x.proper.reg i; by_cases h:Healthy S.p.threshold T.support U; rw [masked_eq _ _ _ U h,masked_eq _ _ _ _ (show Healthy S.p.threshold (y.proper.reg i).support U from h),masked_eq _ _ _ _ (show Healthy S.p.threshold ((x-y).proper.reg i).support U from h)]; rfl
       rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (show ¬Healthy S.p.threshold (y.proper.reg i).support U from h),masked_ne _ _ _ _ (show ¬ Healthy S.p.threshold ((x-y).proper.reg i).support U from h),sub_self]
   rw [hm]; exact (he ..).2
-- profile cost.Sum exact.Suppress algebra p.Core.Context.Turn.Lift.
lemma logK (P:Box n) : Confluence (fun i=> profile (p i).proper (fun j=> Complex.ofReal ∘ (p i).proper.K j) P):=by
   let f(v:X):=profile v.proper (fun j=> Complex.ofReal ∘ v.proper.K j) P; let B:= (Fintype.card (Site n):ℝ)*S.k
   have hp(v:X)(U:Config G n): Summable (fun i:{i//barcode v.proper i=P}=> (v.proper.K i.val U:ℂ)) ∧ ‖f v U‖≤ B*‖v‖:=by
      obtain ⟨b,hb,hC⟩:=storedK v; apply currency; exact ⟨fun i=> b i.val, Local.sumBudget_subtype _ hb,fun i=> (Complex.norm_real _|>.trans_le (hC i.val U))⟩
   refine sheers f B p (fun z=>⟨B*‖p z‖,fun U=> (hp ..).2⟩) (fun v w U=>?_) hc
   rw [dist_eq_norm,dist_eq_norm]
   have hv: f v U - f w U= f (v-w) U:=by
       let τ:=(v-w).proper; let K:=barcode v.proper
       let A(z:X)(i:{i//K i=P}):=(z.proper.K i.val U:ℂ); have hg z:Summable (A z):= (hp z U).1; change (∑' i,A v i)-(∑' i,A w i)=∑' i,A (v-w) i; rw [← Summable.tsum_sub (hg v) (hg w)]; exact tsum_congr (fun i=>show _=_ from (Complex.ofReal_sub (v.proper.K i.val U) (w.proper.K i.val U)).symm)
   rw [hv]; exact (hp ..).2
end YM.FullVolume.Retreat
#print axioms YM.FullVolume.Retreat.logK
#print axioms YM.FullVolume.Retreat.vases
