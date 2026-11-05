import YM.UVExtension.Copse.Spring
import YM.Push.ABSOLUTE_SUMS.Copies
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Lattice RG Push.AbsoluteSums Animals Ursell Trees Graph Relation Finset Multiple
open scoped Topology BigOperators Classical
variable {ι:Type*}{n:Side} (X:ι→Support n)(B d:ℕ)
set_option quotPrecheck false
section
variable {f u:ι→ℝ} {b g a δ γ:ℝ} (he:∀ i,0≤ f i)(hu:∀ i,0 ≤ u i)
-- derivative on Reps.RIGHT
noncomputable def duskVal (f u:ι→ℝ)(p:Reps ι) (x: p.fst) := ∏ i:p.fst, if i=x then (f i.val ^ (p.2 i) * u i.val) / (p.2 i).factorial else f i.val ^ (p.2 i+1)/(p.2 i+1).factorial
noncomputable def dusk (f u:ι→ℝ)(p:Reps ι) :ℝ:= ∑ x:p.fst,duskVal f u p x
include hu he
lemma signed (p:Reps ι)(x:p.fst): 0≤ duskVal f u p x:=by
   refine prod_nonneg fun i _=>?_ ; split
   next h=> exact div_nonneg (mul_nonneg (pow_nonneg (he _) _) (hu _)) (Nat.cast_nonneg (α:=ℝ) _)
   exact div_nonneg (pow_nonneg (he _) _) (Nat.cast_nonneg (α:=ℝ) _)
omit he hu
noncomputable def rose (f u:ι→ℝ)(p:Reps ι) (t:p.fst):ℝ:= (∏ b∈univ.erase t,f b.val ^ (p.2 b+1)/(p.2 b+1).factorial)*(f t.val ^ (p.2 t) * u t.val / (p.2 t).factorial)
lemma stars (p:Reps ι)(x:p.fst): duskVal f u p x= rose f u p x := by
   unfold duskVal rose; rw [←prod_erase_mul _ _ (mem_univ x), if_pos rfl]; exact congr_arg (·*_) (prod_congr rfl (fun j hj=> if_neg (ne_of_mem_erase hj)))
private lemma product_sum {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℕ → ℝ) (c : α → ℝ)
    (hw : ∀ i, SumBudget (w i) (c i)) : SumBudget (fun z : α → ℕ => ∏ i, w i (z i)) (∏ i, c i) := by
  let f := fun z : Unit × (α → ℕ) => ∏ i, w i (z.2 i)
  have hp i : 0 ≤ f i := prod_nonneg fun j _ => (hw j).1 _
  have H : SumBudget f (∏ i,c i) := budget_assignments f hp (fun D => by
    simp only [Fintype.sum_unique,f]; rw [← Fintype.prod_sum (fun (i:α) (x : D) => w i x.val)]
    apply prod_le_prod (fun i _ => sum_nonneg fun _ _ => (hw i).1 _)
    intro i _; rw [← Finset.sum_subtype D (p:=(·∈D)) (fun i => Iff.rfl) (w i)]
    exact budget_sum (hw i) D)
  exact budget_pull (fun z : α → ℕ => ((),z)) (fun i j e => congr_arg Prod.snd e) H


include he hu
variable (hz:0≤g)(h':g<1)(hg:∀ i,f i≤ g)
local notation "pA"=> (1-g)⁻¹
include hz hg h'
lemma stove (D:Finset ι)(v:D): SumBudget (fun z=> duskVal f u ⟨D,z⟩ v)
    (∏ j:D,if j=v then pA*u j.val else f j.val*pA):=by
   refine product_sum (α:=↥D) (fun i k=> if i=v then (f i.val^k*u i.val)/k.factorial else f i.val^(k+1)/(k+1).factorial) (fun i=> if i=v then pA*u i.val else f i.val*pA) fun i=>?_
   split
   next h=>
     simp only [h]; rw [mul_comm]; apply budget_mono (budget_geometric (hu v) hz h')
     · exact fun i=> div_nonneg (mul_nonneg (pow_nonneg (he _) _) (hu _)) (Nat.cast_nonneg (α:=ℝ) _)
     intro k; exact (div_le_self (mul_nonneg (pow_nonneg (he _) _) (hu _)) (Nat.one_le_cast.mpr (Nat.factorial_pos k))).trans ((mul_comm ..).trans_le (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (he _) (hg _) _) (hu _)))
   next h =>
     refine budget_mono (budget_geometric (he _) hz h') (fun k=> div_nonneg (pow_nonneg (he _) _) (Nat.cast_nonneg (α:=ℝ) _)) (fun k=>?_)
     exact (div_le_self (pow_nonneg (he _) _) (Nat.one_le_cast.mpr (Nat.factorial_pos (k+1)))).trans ((pow_succ' ..).trans_le (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (he _) (hg _) _) (he _)))
lemma rice (S:Finset ι): SumBudget (fun z=> dusk f u ⟨S,z⟩) (∑ i∈S,pA*(u i*(∏ j∈S.erase i, f j*pA))):=by
  let w(z:↥S):= ∏ j:S,if j=z then pA*u j.val else f j.val*pA
  have he:= budget_over univ (fun (x:↥S) z=> duskVal f u ⟨S,z⟩ x) w (fun x _=> stove he hu hz h' hg S x)
  refine budget_loosen he (le_of_eq ?_)
  rw [Finset.sum_subtype S (p:=(·∈S)) (fun _=> Iff.rfl)]; refine Finset.sum_congr rfl fun i _=>?_
  let v j:= if j=i.val then pA*u j else f j*pA; have hp : w i=∏ j∈S,v j:=by
     rw [Finset.prod_subtype S (p:=(·∈S)) (fun _=>Iff.rfl)]; unfold w; refine Finset.prod_congr rfl fun j _=> by unfold v; simp only [← Subtype.ext_iff]
  rw [hp, ←Finset.mul_prod_erase S _ i.property,show v i.val= _ from (if_pos rfl : v i.val=pA*u i),mul_assoc]; refine congr_arg (fun k=> pA*(u i.val*k)) (Finset.prod_congr rfl fun j hj=>if_neg (ne_of_mem_erase hj))
variable (hH : Ac.Hit X B (fun i=> f i*(1-g)⁻¹) (a+δ) γ)(ha:0≤ a)(hp : (ballCost B:ℝ)*γ ≤ δ)(hγ:0≤γ)(hm:SumBudget (fun i=> u i *worth d B (a+δ) (X i)) b)
attribute [local instance] Classical.propDecidable
include hH ha hp hm hγ
noncomputable def syrup (f u:ι→ℝ)(p:Reps ι):= if Ac.Spark X p.1 then dusk f u p else 0
lemma blinks: SumBudget (fun i:Reps ι=> syrup X f u i*worth d B a (i.1.biUnion X)) (pA * b):=by
   let v i:= f i*pA; have hP : 0<1-g:=sub_pos.mpr h'; have hv i:0≤ v i:=mul_nonneg (he _) (inv_pos.mpr hP).le
   apply sigma_total _ _ _ (budget_scale (inv_pos.mpr hP).le (compass X B d hv hH hp hγ ha u b hu hm))
   intro i; change SumBudget (fun z=> syrup X f u ⟨i,z⟩ * worth d B a (i.biUnion X)) (pA * (∑ j∈i,u j*flight X B d v j a i))
   by_cases hx : Ac.Spark X i; swap; · simp only [syrup,hx,if_false,zero_mul]; refine budget_of_sum (fun _=>le_rfl) (fun s=> ?_); rw [Finset.sum_const_zero]; exact mul_nonneg (inv_pos.mpr hP).le ((compass X B d hv hH hp hγ ha u b hu hm).1 _)
   simp only [syrup,hx,if_true]; let Z:= worth d B a (i.biUnion X)
   change SumBudget (fun z=>dusk f u ⟨i,z⟩ *Z) _; simp_rw [mul_comm _ Z]
   refine budget_loosen (budget_scale (show 0≤ Z from (Real.exp_pos _).le) (rice he hu hz h' hg i)) ?_
   change Z*(∑ j∈i,pA * (u j*∏ k∈i.erase j,v k)) ≤ _; rw [mul_sum,mul_sum]; refine le_of_eq (Finset.sum_congr rfl fun j hj=>?_); unfold flight; rw [if_pos ⟨hj,hx⟩]; change Z*_=_*(_*(Z*_)); ring
end
end YM.UVExtension.Copse
