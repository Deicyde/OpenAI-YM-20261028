import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Curtail
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Passage
import YM.Progress.DIRECTED_RECIPE.Tender


/-! # score bookkeeping on increment bonds changes only K.Priced.Test Soft costs from original tap. Reveal.C.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Daisy Daisy.Charity Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
-- MOR.K

def spice (d : Tap G n)(f : Code G n): Tap G n:= {d with forced:=f}
def black (A : Activities G n)(f : Code G n): Activities G n:= {A with K:=f}
def fuel {V : Type*}(A:ℕ → Support n)(f: ℝ→ ℕ→ V→ℝ)(P: BudgetPoint)(o : Site n) (r w α : ℝ):Prop := 0≤r ∧ (∀ (v:ℝ)(_ : |v| * r≤1) (i), o∉ A i→f v i=f 0 i) ∧
    ∃ v : ℕ→ℝ,(∀ i,0≤ v i) ∧ Ac.Hit A P.B v α w ∧ ∀ x : ℝ,|x| * r≤1 → ∀ i y, Est (v i) r x (fun j=>f j i y)
-- retain exact payload on same X. Use Porch for U outside.Anchor.
structure Season (A : Activities G n)(P : BudgetPoint)(f : ℝ→Code G n)(o : Site n)(r w α : ℝ): Prop where
    term : f 0=A.K
    permit x : |x| * r≤1 → (black A (f x)).ForcedFamily P
    burn : fuel (fun i=>(A.forced i).support) f P o r w α
variable {W : ℝ → Code G n}
lemma burning {X:Activities G n}(h:Season X P W o r B A) (hA:0≤A)(x : ℝ)(he: |x| * r≤1): Dominated (W x):=by
  obtain ⟨hr,_,f,hf,hp,hZ⟩:=h.burn
  have he':= AbsoluteSums.Product.everyone_ne (fun i=>(X.forced i).support) _ hf (fun i _=> (X.forced i).inventory_ne.mono (X.forced i).inventory_sup) hp
  refine ⟨f,he'.2.1.of_nonneg_of_le hf (fun i=>?_),fun i U=> (hZ x he i U).value⟩
  exact le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg hA (by positivity)))

variable (h : Season (X.pours d) P W o r B (P.supportExponent+1))
structure Vapor (X:Pipes G n)(d : Tap G n)(P : BudgetPoint)(w:ℝ): Prop where
  texts i : UsesFinal P.threshold (X.softer i) (d.logarithm i)
  visits i : ∀ U, Healthy P.threshold (X.softer i) U → d.logarithm i U=0
  travels i : GaugeInvariant (d.logarithm i)
  tails i : Measurable (d.logarithm i)
  funds : ∃ f:ℕ→ℝ, Payments.softCost P X f w ∧ ∀ i V, ‖d.logarithm i V‖≤f i

variable (hp : Vapor X d P w)
include h hp
lemma hearth (t : ℝ)(hv:|t| * r≤1): Kiln X (spice d (W t)) P:=by
  refine ⟨(h.permit t hv),fun i V hi hu=>hi (hp.visits i V hu),?_,hp.travels,hp.texts,hp.tails,burning h (le_add_of_le_of_nonneg P.exponent_pos.le zero_le_one) t hv⟩
  obtain ⟨f,hF,hv⟩:= hp.funds
  have hh := (Activities.summable_charge X.sites hF.1 (Payments.drop_reserve P _ hF.1 hF.2)); exact ⟨f,hh,hv⟩
-- Help schedule.Test + actual carries via Shelf. injection no.Y.Covers. share.
omit h hp
private def primaryP (p q : ℕ → ℝ) (κ : ℝ) : Ovens.Label → ℝ:= Sum.elim (fun i=> Real.exp κ * p i) (fun i=> 2*q i)
private def mild (κ : ℝ)(i:Ovens.Label) := Sum.elim (fun _=> Real.exp (-κ)) (fun _=>1) i
private theorem scaleInk {ι : Type*}(p : ι→Support n)(b : ι→ℝ){P : BudgetPoint} (hh:Ac.Hit p P.B b (P.supportExponent+1) v)(ha:0≤a): Ac.Hit p P.B (fun i=> a*b i) (P.supportExponent+1) (a*v):=by
   intro i; convert! budget_scale ha (hh i) using 1; ext j; by_cases hk:i∈p j <;> simp [hk,mul_assoc]
-- pure prop certification
variable (he : Payments.Rates P.B A B w κ)
include h he hp
lemma wallets : ∃ f : Ovens.Label → ℝ,(∀ i,0≤ f i) ∧ Ac.Hit X.patch P.B f (P.supportExponent+1) (Payments.inflation B w κ) ∧ ∀ x, |x| * r≤1→∀ i U, Est (mild κ i*f i) r x (fun t=>reach (spice d (W t)) i U):= by
  obtain ⟨hz,hQ,f,hf,hH,hP⟩:= h.burn
  obtain ⟨v,hv,h⟩:= hp.funds
  refine ⟨primaryP f v κ,fun i=>?_, ?_,fun x hh i U=> ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_pos _).le (hf _)
    exact mul_nonneg zero_le_two (hv.1 _)
  · exact Labels.together _ _ _ (scaleInk _ _ (P:=P) hH (Real.exp_pos κ).le) (scaleInk _ _ (P:=P) hv.2 (show (0:ℝ)≤2 by norm_num))
  rcases i with i|i; simp only [primaryP,mild, Sum.elim_inl,Real.exp_neg,inv_mul_cancel_left₀ (Real.exp_pos κ).ne']; exact hP x hh i U
  simp only [primaryP,mild,Sum.elim_inr,one_mul]; refine Est.nil (reach d (Sum.inr i) U) _ _ _ hz ?_
  change |Real.exp (d.logarithm i U)-1|≤2*v i
  apply (Real.abs_exp_sub_one_le ?_).trans (mul_le_mul_of_nonneg_left (h i U) zero_le_two); obtain ⟨p,hp⟩:= X.sites i
  have he' := Samples.one_le_quote (Payments.drop_reserve P _ hv.1 hv.2 p) i; rw [if_pos hp] at he'
  exact (h i U).trans ((P.loMass _ _ (hv.1 i)).trans (he'.trans he.soft_limit))
lemma harvest (F : ℕ ≃ Pellet X): Season (fused F P d) P (fun t=> solid F P (spice d (W t))) o r A P.supportExponent:=by
  have hz:spice d (W 0) = d:=by rw [h.term]; rfl
  refine ⟨?_,fun t ht=> ?_,⟨h.burn.1, ?_,?_⟩⟩
  · rw [hz]; rfl
  · obtain ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩:= Passage.fused_forcedFamily F (hearth h hp t ht)
    exact ⟨h,h₁,h₂,h₃,h₄,h₅,h₆⟩
  · intro v hv i ho; funext U
    unfold solid; dsimp only; split
    · refine Finset.prod_congr rfl (fun j hj=> ?_); cases j
      · exact congr_fun (h.burn.2.1 v hv _ (fun hk=>ho (Finset.mem_biUnion.mpr ⟨_,hj,hk⟩))) U
      rfl
    rfl
  obtain ⟨f,hF,hW,hK⟩:=wallets h hp he
  let v i:= ∏ j∈ (F i).val, f j; let M i:= Real.exp (-κ)*v i; let γ:=Payments.inflation B w κ
  have hp : 0≤ γ:= add_nonneg (mul_nonneg (Real.exp_pos _).le he.hard) (mul_nonneg zero_le_two he.soft)
  have hv i :0≤ v i:= prod_nonneg fun j _=> hF _; have hh i:0≤ M i:=mul_nonneg (Real.exp_pos _).le (hv i)
  refine ⟨M,hh, fun x=> ?_,fun t ht i U=>?_⟩
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
  unfold solid; dsimp only; split_ifs
  · apply (Est.summit (F i).val _ _ h.burn.1 (fun j (_:j∈(F i).val)=> hK t ht j U)).upto
    rw [prod_mul_distrib]; unfold M v; apply mul_le_mul_of_nonneg_right _ (hv _)
    obtain ⟨j,hj⟩:= (F i).property.1
    have hm (i : Ovens.Label):mild κ i≤1:=by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.heading); rfl
    rw [← mul_prod_erase _ _ (Finset.mem_toLeft.mp hj)]
    exact mul_le_of_le_one_right (Real.exp_pos (-κ)).le (Finset.prod_le_one (fun i hi=> by cases i; exact (Real.exp_pos _).le; exact zero_le_one) (fun i hi=> hm i))
  exact Est.nil _ _ _ _ h.burn.1 (abs_zero.le.trans (hh i))
end YM.PhysicalNext.Repeat.Mallow
