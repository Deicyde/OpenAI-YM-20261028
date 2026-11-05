import YM.UVExtension.Copse.Berry
/-! Exchange currencies at root including built-in path rates. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Set Lattice RG Wilson Finset Relation Push Push.AbsoluteSums Animals Ac Trees Reserves
open scoped Topology BigOperators Classical
variable {ι:Type*}{n:Side} (X:ι→Support n)(B : ℕ)
section
variable [DecidableEq ι]{f:ι→ℝ}{a δ γ:ℝ}
-- beware fork.Lam
noncomputable def ascent (f:ι→ℝ) (j:ι)(a:ℝ)(p:Finset ι):ℝ:= if j∈p∧ Ac.Spark X p then (∏ i∈p.erase j,(f i*currency B a (X i))) else 0
variable (hf:∀ i,0≤ f i)(hh: Hit X B f (a+δ) γ)(hp:(Animals.ballCost B:ℝ)*γ ≤ δ)(he:0≤γ)
include hf hp he hh
lemma vapors (j:ι): SumBudget (ascent X B f j a) (currency B δ (X j)):=by
   let v:= ascent X B f j a; refine budget_of_sum (fun i=>?_) fun D =>?_ 
   · unfold ascent; split; next=> exact Finset.prod_nonneg fun i _=> mul_nonneg (hf _) (Real.exp_pos _).le
     exact le_rfl
   let D':=D.filter fun i=> j∈i ∧ Ac.Spark X i; have h' i(h:i∈D'):j∈i∧Ac.Spark X i:= (mem_filter.mp h).2
   let r:=D.biUnion id; let k:= r.erase j; let e : Finset ι → Finset ι:=fun s=> s.erase j; let g i:= f i*Trees.currency B a (X i)
   have hx: Set.InjOn e (D':Set (Finset ι)):=fun p h q he eq=>by rw [← Finset.insert_erase (h' _ h).1,← Finset.insert_erase (h' _ he).1, show p.erase j=q.erase j from eq]
   have he i (h:i∈ D') : e i ∈ Ac.pouch X k (X j):= Ac.op ..|>.2 ⟨Finset.erase_subset_erase j (fun x hh=>Finset.mem_biUnion.mpr ⟨i,(mem_filter.mp h).1,hh⟩),Ac.excise X (h' _ h).2 (h' _ h).1⟩
   have hV: ∑ s∈D,v s=∑ s∈D',v s:= Eq.symm (sum_subset (Finset.filter_subset ..) (fun i hi hj=>if_neg (fun h=> hj (mem_filter.mpr ⟨hi,h⟩))))
   have hu:= sapT X B 0 hf hh hp ‹0≤γ› k (X j); unfold worth at hu; rw [one] at hu
   change ∑ s∈D,v s≤_; rw [hV]; refine le_trans ?_ hu
   calc
     ∑ s∈D',v s=∑ s∈D'.image e, ∏ j∈s,g j:=by rw [Finset.sum_image hx]; exact Finset.sum_congr rfl fun x h=> if_pos (h' x h)
     _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun i hi=> by obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact he _ hj) (fun i _ _=>prod_nonneg fun j _=> mul_nonneg (hf j) (Real.exp_pos _).le)

omit hh hp he hf
noncomputable def spannedW (f extra:ι→ℝ) (a:ℝ)(k:ℕ)(j:ι)(p:Finset ι):= if j∈p ∧ Ac.Spark X p then Real.exp (a*(coverNumber B (p.biUnion X):ℝ))*(1+Reserves.setPrice X B extra p)^k *∏ i∈p.erase j,f i else 0
variable (j:ι)(k:ℕ)(extra mark:ι→ℝ)(hx:∀ i,0 ≤ extra i)(hm: ∀ i,0 ≤ mark i){q ε:ℝ} (he':0 < ε)(ha:0 ≤ a)(hP:Ready X B (tariff f extra mark ε) (a+2*ε) γ δ q)
local notation "U!"=> tariff f extra mark ε
local notation "T!"=> currency
local notation "F!" => Reserves.weight X B extra
include he' hm hx ha hf hP
lemma salvo : SumBudget (spannedW X B f extra a k j) (currency B a (X j)*polyPrice ε k*Real.exp (2*ε*F! j)*currency B δ (X j)):=by
   let v:= currency B a (X j)* polyPrice ε k* Real.exp (2*ε*F! j); have hv:0≤v:=by unfold v polyPrice currency; positivity
   have hz : (ballCost B:ℝ)*γ ≤ δ:=by
      have he₁:=hP.2.1; have hq := hP.2.2.1; have ht : Trees.stretch B γ δ ≤ 1:=by unfold degreePrice at hq; linarith only [hq,hP.2.2.2.1]
      unfold stretch at ht; linarith only [(div_le_iff₀ he₁).mp ht]
   have he:=vapors X B hP.2.2.2.2.1 hP.2.2.2.2.2 hz hP.1.le j
   have hX i:0≤F! i:= add_nonneg (Nat.cast_nonneg _) (hx _); refine budget_mono (budget_scale hv he) (fun i=>?_) (fun p=>?_)
   · unfold spannedW; split; next h=> exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun i _=>hX _)) k)) (Finset.prod_nonneg fun i _=> hf i)
     exact le_rfl
   unfold spannedW ascent; split; next h=>
    let d:=p.erase j; let e:= ∏ i∈d,f i; let w:=∑ i∈d,F! i; let u:=F! j+w
    have hw:0≤ w:= sum_nonneg fun i _=> hX i; have hu:0≤u:= add_nonneg (hX _) hw
    have he:∏ i∈d,(f i*currency B a (X i)*Real.exp (2*ε*F! i))≤ ∏ i∈d,(U! i*currency B (a+2*ε) (X i)):=by
       refine Finset.prod_le_prod (fun i _=> mul_nonneg (mul_nonneg (hf _) (Real.exp_pos _).le) (Real.exp_pos _).le) fun i _=>?_ ; rw [show U! i*currency B (a+2*ε) (X i) =_ from exchange X B f extra mark ε a i]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (le_add_of_nonneg_right (hm i))) (mul_nonneg (hf _) (Real.exp_pos _).le)
    apply le_trans _ (mul_le_mul_of_nonneg_left he hv)
    simp_rw [prod_mul_distrib,←Real.exp_sum]; rw [← Finset.mul_sum]
    have hp : Real.exp (a*(coverNumber B (p.biUnion X):ℝ)) ≤ currency B a (X j)*∏ i∈d,currency B a (X i) := by
       have hk:= Ac.cover X B h.2; rw [← Finset.add_sum_erase p _ h.1] at hk
       unfold currency; rw [← Real.exp_sum,← Real.exp_add,← Finset.mul_sum,← mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hk) ha)
    have he : setPrice X B extra p=u:= (Finset.add_sum_erase _ (F!) h.1).symm
    have hc:0≤polyPrice ε k:=by unfold polyPrice; positivity
    refine (mul_le_mul_of_nonneg_right (mul_le_mul hp (show _ ≤ polyPrice ε k*Real.exp (2*ε*u) from ?_) (by rw [he]; positivity) (mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _=> (Real.exp_pos _).le))) (Finset.prod_nonneg fun _ _=> hf _)).trans_eq ?_
    · rw [he]; refine (polynomial_cost he' hu k).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [he']) hu)) hc)
    unfold u v w; rw [mul_add,Real.exp_add]; ring
   next h=> rw [mul_zero]
end
end YM.UVExtension.Copse
