import YM.MergeProof.SwitchCost
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Cruise
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-! # Following reallocations. Use Switch lift under awards. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Motion
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Switch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type}[Fintype ι] {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
structure Pays (A : Activities G n)(P: BudgetPoint)(f : ℝ → Finset ι → Code G n)(w α : ℝ): Prop where
    term j : f 0 j=A.K
    licensed x j : x∈Set.Icc 0 1 → (black A (f x j)).ForcedFamily P
    bought : ∃ c:ℕ→ℝ,(∀ i,Paid (fun y t j=> f t j i y) (c i)) ∧ Ac.Hit (fun i=>(A.forced i).support) P.B c α w
variable {W : ℝ→ Finset ι → Code G n} (h : Pays (X.pours d) P W B (P.supportExponent+1))
lemma PaidK {t : ℝ} {X:Activities G n} (h:Pays X P W B A)(hx:0 ≤ A)(ht : t∈Set.Icc (0:ℝ) 1)(v: Finset ι): Dominated (W t v):=by
   obtain ⟨f,hF,hM⟩:=h.bought
   have hp:=AbsoluteSums.Product.everyone_ne _ _ (fun i=> (hF i).rocket) (fun i _=> (X.forced i).inventory_ne.mono (X.forced i).inventory_sup) hM
   refine ⟨f,hp.2.1.of_nonneg_of_le (fun i=> (hF i).rocket) (fun i=> le_mul_of_one_le_right (hF i|>.rocket) (Real.one_le_exp (mul_nonneg hx (by positivity)))),fun i u=> Paid.tasting (hF i) u t ht v⟩
variable (hp : Vapor X d P w) (he: Payments.Rates P.B A B w κ)
include h hp
lemma kitch (x : ℝ)(ht:x∈ Set.Icc (0:ℝ) 1)(i:Finset ι): Kiln X (spice d (W x i)) P := by
  refine ⟨h.licensed _ _ ht,fun i V hi hu=> hi (hp.visits i V hu),?_,hp.travels,hp.texts,hp.tails,PaidK h (le_add_of_le_of_nonneg P.exponent_pos.le zero_le_one) ht i⟩
  obtain ⟨f,hF,hv⟩:= hp.funds
  have hh := (Activities.summable_charge X.sites hF.1 (Payments.drop_reserve P _ hF.1 hF.2)); exact ⟨f,hh,hv⟩
omit h hp
private def primaryP (p q : ℕ → ℝ) (κ : ℝ) : Ovens.Label → ℝ:= Sum.elim (fun i=> Real.exp κ * p i) (fun i=> 2*q i)
private def mild (κ : ℝ)(i:Ovens.Label) := Sum.elim (fun _=> Real.exp (-κ)) (fun _=>1) i
private theorem scaleInk {ι : Type*}(p : ι→Support n)(b : ι→ℝ){P : BudgetPoint} (hh:Ac.Hit p P.B b (P.supportExponent+1) v)(ha:0≤a): Ac.Hit p P.B (fun i=> a*b i) (P.supportExponent+1) (a*v):=by
   intro i; convert! budget_scale ha (hh i) using 1; ext j; by_cases hk:i∈p j <;> simp [hk,mul_assoc]
-- pure prop certification
include h hp he
lemma wallets : ∃ f : Ovens.Label → ℝ,(∀ i,0≤ f i) ∧ Ac.Hit X.patch P.B f (P.supportExponent+1) (Payments.inflation B w κ) ∧ ∀ i, Paid (fun U t j=>reach (spice d (W t j)) i U) (mild κ i*f i):= by
  obtain ⟨f,hP,hH⟩:= h.bought
  have hf i:= (hP i).rocket; obtain ⟨v,hv,hg⟩:= hp.funds
  refine ⟨primaryP f v κ,fun i=>?_, ?_,fun i=> ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_pos _).le (hf _)
    exact mul_nonneg zero_le_two (hv.1 _)
  · exact Labels.together _ _ _ (scaleInk _ _ (P:=P) hH (Real.exp_pos κ).le) (scaleInk _ _ (P:=P) hv.2 (show (0:ℝ)≤2 by norm_num))
  rcases i with i|i; simp only [primaryP,mild, Sum.elim_inl,Real.exp_neg,inv_mul_cancel_left₀ (Real.exp_pos κ).ne']; exact hP i
  simp only [primaryP,mild,Sum.elim_inr,one_mul]; refine Switch.constant (reach d (Sum.inr i)) (mul_nonneg zero_le_two (hv.1 i)) ?_
  intro U
  change |Real.exp (d.logarithm i U)-1|≤2*v i
  apply (Real.abs_exp_sub_one_le ?_).trans (mul_le_mul_of_nonneg_left (hg i U) zero_le_two); obtain ⟨p,hp⟩:= X.sites i
  have he' := Samples.one_le_quote (Payments.drop_reserve P _ hv.1 hv.2 p) i; rw [if_pos hp] at he'
  exact (hg i U).trans ((P.loMass _ _ (hv.1 i)).trans (he'.trans he.soft_limit))
lemma harvest (F : ℕ ≃ Pellet X): Pays (fused F P d) P (fun t i=> solid F P (spice d (W t i))) A P.supportExponent:=by
  constructor
  · intro j; rw [show spice d (W 0 j)=d by rw [h.term]; rfl]; rfl
  · intro t j ht; obtain ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩:= Passage.fused_forcedFamily F (kitch h hp t ht j)
    exact ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩
  obtain ⟨f,hF,hW,hK⟩:=wallets h hp he
  let v i:= ∏ j∈ (F i).val, f j; let M i:= Real.exp (-κ)*v i; let γ:=Payments.inflation B w κ
  have hp : 0≤ γ:= add_nonneg (mul_nonneg (Real.exp_pos _).le he.hard) (mul_nonneg zero_le_two he.soft)
  have hv i :0≤ v i:= prod_nonneg fun j _=> hF _; have hh i:0≤ M i:=mul_nonneg (Real.exp_pos _).le (hv i)
  refine ⟨M,fun i=>?_,fun x=>?_⟩
  · let f':= ∏ j∈(F i).val,fun U t i'=>reach (spice d (W t i')) j U
    have hg:= Paid.prod (F i).val _ _ (fun j (_ : j∈(F i).val)=> hK j)
    refine Paid.congr ((Paid.gate (X:={U|(addr F P i).eligible P.threshold U}) (hg.weaken ?_))) (fun U t ht=> ?_)
    · rw [prod_mul_distrib]; unfold M v; apply mul_le_mul_of_nonneg_right _ (hv _)
      obtain ⟨j,hj⟩:= (F i).property.1
      have hm (i : Ovens.Label):mild κ i≤1:=by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.heading); rfl
      rw [← mul_prod_erase _ _ (Finset.mem_toLeft.mp hj)]
      exact mul_le_of_le_one_right (Real.exp_pos (-κ)).le (Finset.prod_le_one (fun i hi=> by cases i; exact (Real.exp_pos _).le; exact zero_le_one) (fun i hi=> hm i))
    ext i'; by_cases hz: (addr F P i).eligible P.threshold U
    · rw [Set.indicator_of_mem (show U∈_ from hz)]; simp_rw [Finset.prod_apply]; exact (if_pos hz).symm
    rw [Set.indicator_of_notMem]; exact (if_neg (show ¬ (addr F P i).eligible P.threshold U from hz)).symm; exact hz
  · have hR:= Ac.forest X.patch P.B P.exponent_pos.le hF hW he.capital hp x
    let b (p):= (F p).val; have hi : Injective b:= Subtype.val_injective.comp F.injective
    refine budget_loosen (budget_mono (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)) (fun i=>?_) (fun i=> ?_)) he.returns
    · split; · exact mul_nonneg (hh _) (Real.exp_pos _).le
      exact le_rfl
    split
    next h=>
      unfold Ac.roots; dsimp only; rw [if_pos ⟨(F i).property.2.1,h⟩]; apply le_of_eq; change M i*_=Real.exp (-κ) *(Real.exp _* v i) -- orientation?
      unfold M v; ring_nf; rfl
    exact (budget_scale (Real.exp_pos (-κ)).le (budget_pull b hi hR)).1 _
omit he hp
lemma widening : Pays ((drawer G n).pours (widen X d)) P (fun t i=>stuff (upK X) (W t i)) B (P.supportExponent+1):=by
  refine ⟨fun j=> ?_,fun v j hv=>?_,?_⟩
  · rw [h.term]; rfl
  · apply (Rack.preserves X (spice d (W v j)) P).forced_family (?_) (fun _ _ _ => Iff.rfl) (fun _ => MeasurableSet.univ) (fun _ _ _ _ _ => rfl)
    exact h.licensed v j hv
  obtain ⟨f,hv,hB⟩:=h.bought; let i:=upK X; refine ⟨stuff i f, fun k=> ?_, fun x=> ?_⟩
  · by_cases ht:k∈Set.range i
    · obtain ⟨k,rfl⟩:=ht; simp_rw [i,stuffed];exact hv k
    rw [blank _ _ ht];unfold i at ht;simp_rw [blank _ _ ht];exact paidZero (ι:=ι) (U:=Config G n)
  refine transfer_budget i ?_ ?_ (hB x)
  · intro z; simp only [pours,i,stuffed]; rw [hard_up]; rfl
  intro z hz; split; rw [blank _ f hz, zero_mul]; rfl
include hp
lemma winter (F : ℕ ≃ (drawer G n).Pellet) (t : ℝ)(i:Finset ι)(ht:t∈ Icc (0:ℝ) 1)(U:Config G n): HasSum (fun p=> (fused F P (widen X (spice d (W t i)))).gasOccurrence P p U)
    ((black (X.pours d) (W t i)).gas P U * Real.exp (∑' i,d.logarithm i U)):=by
  have hy:= Passage.gathered (F:=F) (kitch (Motion.widening h) (shown hp) t ht i) U
  rw [show spice (widen X d) (stuff (upK X) (W t i))=widen X (spice d (W t i)) from rfl] at hy
  rw [(Rack.preserves _ _ _).same_gas,Rack.same_log] at hy;exact hy
end YM.Merge.Motion
