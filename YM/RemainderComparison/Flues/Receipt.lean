import YM.RemainderComparison.Flues.Yard
import YM.PhysicalNext.RECURSIVE_SECANTS_079.Masses

/-!
# Reclose forcing with obligatory hardware and capacity rescaling
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums Finset Merge AnalyticBridge.VerifiedReset
open Mosaic Mosaic.Verse Marker PhysicalNext.RecursiveSecants079
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι θ : Type}[DecidableEq θ] {α:Type*} {J : Census θ}
variable (H:Yard ι α G n) (L:Scone ι α G n) (P:BudgetPoint) (root:ι→Support n)(Z:Set ι) (k:ℕ)
local notation "C" => fireplace H L
variable (F:ℕ ≃ (fireplace H L).Pellet)
local notation "D" => flash H L P Z F
variable {r v d b B σ w t y γ σ' : ℝ}
-- budget economics
structure Resonant (M k:ℕ)(v b d σ B w t γ: ℝ): Prop where
   gain : 0<w
   hope : w ≤ 1
   shrink : 1 ≤ t
   exponent : 0 ≤ σ
   small : v ≤ 1
   joint : w⁻¹*b + (2*v+t⁻¹*d)≤ γ
   margin : (M+M+1:ℕ)^4*(γ:ℝ) ≤ 1
   sustained : t^k * w * (Real.exp γ - 1) ≤ B
local notation "S" => load Z

def speed (w:ℝ) (v:Ovens.Label):ℝ:= Sum.elim (fun _=>w) (fun _=> (1:ℝ)) v
variable (Hp: Resonant P.B k v b d σ B w t γ) (hp:H.Pays Z k P.B (σ+1) b) (he:L.Treasures Z k P.B (σ+1) v d)
local notation "Ψ" => rune H L
include Hp hp he
lemma scaled : ∃ f:Ovens.Label→ℝ,(∀ i, 0≤ f i)∧Ac.Hit (C).patch P.B f (σ+1) γ∧∀ i, load Z (rune H L i)≤k → ∀ a V,
     ‖stoke H L Z a i V‖ ≤ t ^ load Z (rune H L i) * (speed w i * f i):=by
   obtain ⟨q,hq,hf,hx⟩:= hp.wages
   obtain ⟨g,o,hg,ht,hc,hh,h⟩:= he.wages
   let u:= fun j=> w⁻¹*q j; let c:=fun j=> 2*g j + t⁻¹ * o j; have hz:=Hp.gain; have hy:=zero_lt_one.trans_le Hp.shrink
   have hu j: 0≤ c j:= add_nonneg (mul_nonneg zero_le_two (hg j)) (mul_nonneg (by positivity) (ht j))
   let f:=Sum.elim u c; have hp i : 0≤ f i:=by cases i with
                                           | inl j=> exact mul_nonneg (by positivity : 0 ≤ w⁻¹) (hq _)
                                           | inr j=> exact hu _
   refine ⟨f,hp,fun i=> budget_loosen (Labels.together _ _ _ (show Ac.Hit H.plane P.B u (σ+1) (w⁻¹*b) from ?_) (show Ac.Hit L.leg P.B c (σ+1) (2*v+t⁻¹*d) from ?_) i) Hp.joint,fun j hj a V=>?_⟩
   · exact Quotes.hit_scale (by positivity) hf
   · exact BothSides.hit_plus (Quotes.hit_scale zero_le_two hc) (Quotes.hit_scale (by positivity) hh)
   rcases j with j|j
   · change ‖H.glow a j V‖ ≤ t ^ load Z (H.score j) * (w * (w⁻¹ * q j)); rw [mul_inv_cancel_left₀ (ne_of_gt hz)]
     exact (hx j hj a V).trans (le_mul_of_one_le_left (hq _) (one_le_pow₀ Hp.shrink))
   change ‖L.tinct Z a j V‖ ≤ t ^ load Z (L.glyph j) * (1*c j)
   rw [one_mul]; have hp' := h j hj a V; unfold Scone.tinct; split
   next hl=>
     rw [if_pos hl] at hp'; rw [hl,pow_zero,one_mul]; have hv :‖L.glow a j V‖≤1:= hp'.trans ((BothSides.hit_one hc (add_nonneg Hp.exponent zero_le_one) hg j (L.rest j)).trans Hp.small)
     rw [Real.norm_eq_abs] at hp' hv ⊢
     exact (Real.abs_exp_sub_one_le hv).trans ((mul_le_mul_of_nonneg_left hp' zero_le_two).trans (le_add_of_nonneg_right (mul_nonneg (by positivity : 0 ≤ t⁻¹) (ht _))))
   next hl=>
     rw [if_neg hl] at hp'; refine hp'.trans ((le_trans (show _ ≤ t*c j from ?_) (mul_le_mul_of_nonneg_right ?_ (hu j))))
     · refine (le_trans ?_ (mul_le_mul_of_nonneg_left (show t⁻¹*o j≤c j from le_add_of_nonneg_left (mul_nonneg zero_le_two (hg _))) hy.le)); rw [mul_inv_cancel_left₀ (ne_of_gt hy)]
     exact le_self_pow₀ Hp.shrink hl

omit Hp hp he in
lemma height (b:Finset Ovens.Label): load Z (∑ i∈b,rune H L i)=∑ i∈b,load Z (rune H L i):=by
   induction b using Finset.induction with
   | empty=>simp [load]
   | insert i s h he=>rw [sum_insert h,sum_insert h,←he]; unfold load; rw [Multiset.filter_add,Multiset.card_add]
lemma corner : Yard.Pays D Z k P.B σ B :=by
   obtain ⟨f,hf,ht,hc⟩:=scaled H L P Z k Hp hp he
   let e (i:ℕ):=(F i).val; let y := t^k * w
   have hz := Hp.gain.le; have hu:=Hp.shrink; have hv : 0 ≤ t:= zero_le_one.trans hu; have hy: 0 ≤ y := mul_nonneg (pow_nonneg hv _) hz
   let p i:=∏ j∈e i,f j; have hr i: 0≤ p i := prod_nonneg (fun i _=> hf i)
   let b i:= y*p i; have hh i:0 ≤ b i:= mul_nonneg hy (hr i)
   refine ⟨b,hh,fun j=>?_ ,fun i hi a U=>?_⟩
   · have hm:=Ac.forest (C).patch _ Hp.exponent hf ht Hp.margin (budget_nonneg (ht j)) j
     let g:=fun i=>Ac.roots (C).patch P.B f σ j (e i)
     convert budget_loosen (budget_scale hy (budget_pull e (Subtype.val_injective.comp F.injective) hm)) Hp.sustained using 1
     ext i; simp only [flash,Yard.plane,Ovens.Pipes.addr,Ac.roots,Ovens.Pipes.skin,← show e i=(F i).val from rfl,show Ac.Spark (C).patch (e i) from (F i).property.2.1,true_and]; split; next=> unfold b p; ring
     rw [mul_zero]
   change load Z (∑ j∈ (F i).val,rune H L j)≤ k at hi; rw [height H L Z] at hi
   have hb j (hj:j∈ e i): load Z (rune H L j)≤k:=(single_le_sum (fun i _=>Nat.zero_le (load Z (rune H L i))) hj).trans hi
   have hl (j:Ovens.Label): (0≤ speed w j)∧ speed w j≤1:=by cases j with
                                            | inl j=> exact ⟨hz,Hp.hope⟩
                                            | inr j=> exact ⟨zero_le_one,le_rfl⟩
   have hs : ∏ j∈e i, speed w j ≤ w:=by
      obtain ⟨j,hj⟩:= (F i).property.1; have hm : ({Sum.inl j}:Finset Ovens.Label) ⊆ e i:= singleton_subset_iff.mpr (mem_toLeft.mp hj)
      exact (prod_le_prod_of_subset_of_le_one hm (fun _ _=> (hl _).1) (fun _ _ _=> (hl _).2)).trans_eq (show ∏ j∈({Sum.inl j}:Finset Ovens.Label), speed w j = w from prod_singleton ..)
   unfold flash; dsimp only; split
   next hx=>
     rw [norm_prod]; apply le_trans (prod_le_prod (fun _ _=>norm_nonneg _) fun j hj=>hc j (hb j hj) a U)
     simp_rw [prod_mul_distrib,Finset.prod_pow_eq_pow_sum,b,y,mul_assoc]; exact mul_le_mul (pow_le_pow_right₀ hu hi) (mul_le_mul_of_nonneg_right hs (hr i)) (mul_nonneg (prod_nonneg fun j _=>(hl _).1) (hr i)) (by positivity)
   next=> rw [norm_zero]; exact hh i
end YM.RemainderComparison.Flues
