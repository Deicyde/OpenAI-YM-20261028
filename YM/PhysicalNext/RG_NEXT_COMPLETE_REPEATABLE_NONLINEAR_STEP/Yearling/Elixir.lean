import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Tower
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Interval
import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
import YM.Planned.STATIONARY_JET_PORT.AtHome
/-! # Cluster differences in hit-small sector. Compare without repaying root controls.
    telescope simultaneous product jets with exactly old ONE Brush under footprint restriction.
    slack tiny chosen after lattice (for continuity). No salary rerolled under perturbation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple
open ConnectedActivityE6 Blaze Brush
open scoped Topology ContDiff BigOperators Classical
variable {E α ι: Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Side} (X : ι→Support n) (B : ℕ) {u e a γ δ t : ℝ} (j : ℕ) (w:ι→ℝ)

lemma lapride (M : Finset ι) (f g : ι→ E→ℝ) (h d:ι→ℝ) (x:E) (_ht:0≤t) (hu:t≤1) (hg : ∀ i∈M,Brush j (h i) 1 (f i) x) (hf : ∀ i∈M,Brush j (t*d i) 1 (g i-f i) x) (hy : ∀ i∈M,0≤d i) :
    let u:= ∏ i∈M,(h i+d i)
    Brush j u (M.card:ℝ) (fun y=>∏ i∈M,g i y) x ∧ Brush j (t*(u-∏ i∈M,h i)) (M.card:ℝ) ((fun y=>∏ i∈M,g i y)-(fun y=>∏ i∈M,f i y)) x := by
  induction M using Finset.induction_on with
  | empty=>
    simp_rw [Finset.prod_empty,sub_self,card_empty,Nat.cast_zero,mul_zero]; refine ⟨(Brush.certified (x:=x) (le_refl 0) (1:ℝ)).climb (by simp) le_rfl,?_⟩; exact Brush.zi EventuallyEq.rfl le_rfl le_rfl
  | insert i M hm ih=>
    obtain ⟨he,h'⟩:= ih (fun i hi=> hg i (mem_insert_of_mem hi)) (fun i hi=> hf i (mem_insert_of_mem hi)) (fun i hi=> hy i (mem_insert_of_mem hi))
    simp_rw [prod_insert hm,card_insert_of_notMem hm,Nat.cast_add,Nat.cast_one]
    let T' y:= ∏ i∈M,g i y; let W' y:=∏ i∈M,f i y
    have hx:=hg i (mem_insert_self ..); have hv:= hf i (mem_insert_self ..)
    rw [add_comm (M.card:ℝ)]; have hh: Brush j (h i+d i) 1 (g i) x:= by
      apply ((hx.gathering hv).climb (add_le_add_right (mul_le_of_le_one_left (hy i (mem_insert_self ..)) hu) _) le_rfl).shimmy; exact Eventually.of_forall fun _=> (add_sub_cancel ..).symm
    refine ⟨hh.paints he, ((((hv.paints he).gathering (hx.paints h')).climb (le_of_eq ?_) le_rfl).shimmy (Eventually.of_forall fun i'=>?_))⟩
    · ring
    change g i i'*T' i'- f i i'*W' i'= (g i i'-f i i')*T' i'+f i i'*(T' i'-W' i'); ring

lemma laproll (p : ℝ) (M : ℕ) (n n' m v:ℝ) (hp : 0 ≤ p) (h₁ : p≤1) (hv : 0 ≤ v) (he : |n| ≤ m) (ht : |n'-n| ≤ p*v) :
    |n'^M-n^M| ≤ p*((m+v)^M-m^M) := by
  let X (j:ℕ) (_:ℝ):= n; let Y (j:ℕ) (_:ℝ):= n'; let M':=Finset.range M
  have hh : ∀ i∈M',Brush 0 m 1 (X i) 0:= fun i _=> (Brush.certified zero_le_one (x:=(0:ℝ)) n).climb he le_rfl
  have hv':∀ i∈M',Brush 0 (p*v) 1 (Y i-X i) 0 := fun i _=> (Brush.certified zero_le_one (x:=(0:ℝ)) (n'-n)).climb ht le_rfl
  have hz := (lapride 0 _ _ _ _ _ _ hp h₁ hh hv' (fun _ _=> hv)).2.bound
  simpa only [X,Y, M', prod_const,card_range,Pi.sub_apply,Real.norm_eq_abs] using hz
lemma license (g f : ι→ℝ) (h d:ι→ℝ) (ht:0≤t) (hy:t≤1) (hg:∀ i,|f i|≤h i) (hf : ∀ i,|g i - f i| ≤ t*d i) (hx:∀ i, 0≤d i) (p : Multiple.Reps ι) :
    |manyW g p-manyW f p| ≤ t*manyW (h+d) p := by
  let n (i:↥p.fst):=p.snd i+1; let v i:= (n i).factorial; let φ (f : ι→ℝ) (i:↥p.fst):ℝ:= f i.val^n i / v i
  have hQ i : φ h i≤ φ (h+d) i := div_le_div_of_nonneg_right (pow_le_pow_left₀ ((abs_nonneg _).trans (hg i.val)) (le_add_of_nonneg_right (hx _)) _) (by positivity)
  let D (i:↥p.fst):= φ (h+d) i-φ h i; let f' i (_:ℝ):= φ f i; let g' i (_:ℝ):= φ g i
  have hz i : |φ f i| ≤ φ h i:= by unfold φ; rw [abs_div,abs_pow,abs_of_nonneg (show 0 ≤ (v i:ℝ) from Nat.cast_nonneg _)]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hg i.val) _) (Nat.cast_nonneg _)
  have he i : |φ g i- φ f i|≤ t*D i:= by
    apply (le_trans (b:=t*((h i.val+d i.val)^n i-(h i.val)^n i)/ v i))
    · unfold φ; rw [← sub_div, abs_div,abs_of_nonneg (show 0 ≤ (v i:ℝ) from Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (laproll t _ _ _ _ _ ht hy (hx _) (hg _) (hf _)) (Nat.cast_nonneg _)
    unfold D φ; change _ ≤ t*((h i.val+ d i.val)^n i/_-_/ v i); exact le_of_eq (by ring)
  have hh:= (lapride 0 univ f' g' (φ h) D 0 ht hy (fun i _=> (Brush.certified zero_le_one (φ f i)).climb (hz i) le_rfl) (fun i _=> (Brush.certified zero_le_one (φ g i-φ f i)).climb (he i) le_rfl) (fun i _=> sub_nonneg.mpr (hQ i))).2
  apply hh.bound.trans; simp_rw [show ∀ i,φ h i+D i= φ (h+d) i from fun i=> add_sub_cancel ..]; exact mul_le_mul_of_nonneg_left (sub_le_self _ (prod_nonneg fun i _=> (abs_nonneg _).trans (hz i))) ht

/- continuum slack chosen at fixed TORUS; exact energy footprint count constant here. -/
lemma comforts (h : Ready X B (fun i=> (2:ℝ)^j*w i) a γ δ (1/2)) (he:0≤e) : ∃ K:ℝ,0 < K ∧∀ Z:ι→ℝ,SumBudget Z e →
    Ready X B (fun i=> 2^j*(w i+K*Z i)) a (γ+γ/2) δ (3/4) := by
  let z (i:Finset (Site n)):= Real.exp ((a+δ)* (coverNumber B i))
  let k:= ∑ i,z i; have hp i : z i ≤ k:=Finset.single_le_sum (f:=z) (fun i _=> Real.exp_nonneg _) (mem_univ _); have hk:0<k:= (Real.exp_pos _).trans_le (hp ∅)
  obtain ⟨hg,hd,h,hB,hW,hZ⟩:=h
  let c:= γ/ (2*k*(2^j)*(1+e)); have hc:0<c:=by unfold c; positivity
  refine ⟨c,hc,fun Z hy=> ⟨by linarith,hd,?_,by norm_num,?_,?_⟩⟩
  · rw [show degreePrice B (γ+γ/2) δ=3/2*degreePrice B γ δ by unfold degreePrice stretch; ring]; linarith
  · intro i; dsimp only; rw [mul_add]; exact add_nonneg (hW _) (by have hx:=hy.1 i; positivity)
  intro x; have hx i : 0 ≤ (2:ℝ)^j*c*Z i:=by have h:= hy.1 i; positivity
  have hp : SumBudget (fun i=> if x∈X i then 2^j*(c*Z i)*z (X i) else 0) (γ/2) := by
    have he' := budget_scale hk.le (budget_scale (show 0 ≤ 2^j * c by positivity) hy)
    refine budget_loosen (budget_mono he' ?_ fun i=>?_) ?_
    · intro i; split; next=> rw [← mul_assoc (2^j)]; exact mul_nonneg (hx i) (Real.exp_nonneg _)
      exact le_rfl
    · split; next => rw [← mul_assoc (2^j)]; exact ((mul_le_mul_of_nonneg_left (hp _) (hx _)).trans_eq (mul_comm ..))
      exact he'.1 i
    calc
      _ ≤ k*(2^j*c*(1+e)) := by gcongr; linarith only
      _ = γ/2 := by unfold c; field_simp
  have hz := budget_plus (hZ x) hp; convert hz using 2 with i; dsimp only; split_ifs; unfold z; ring
  rw [zero_add]
end YM.PhysicalNext.Repeat.Yearling
