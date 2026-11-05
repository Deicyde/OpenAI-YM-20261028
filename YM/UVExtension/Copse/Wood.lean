import YM.UVExtension.Copse.Cover

/-! # distinct with whole-polymer marked root
 sharpen exponential recursion with adjustable room. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Lattice RG Wilson Finset Relation
open Push Push.AbsoluteSums Ac Animals
open scoped Topology BigOperators Classical
variable {ι:Type*}{n:Side} (X:ι→Support n)(B : ℕ)(m:ℕ)
set_option quotPrecheck false
-- coeff
noncomputable def worth (d M:ℕ)(a : ℝ)(p:Support n) := Real.exp (a*Copse.cover d M p)
private lemma grad [DecidableEq ι]{f:ι→ℝ}{a δ γ:ℝ}(hf:∀ i,0≤ f i)(hh: Hit X B f (a+δ) γ)(D:Finset ι)(Y:Support n)(H : ∀ P,P ⊂ D → ∀ y, Ac.film X P y (fun i=> f i*Trees.currency B a (X i)) ≤ Trees.currency B δ y) : Ac.film X D Y (fun i=> f i*Trees.currency B a (X i)) ≤ Real.exp (Y.card*γ):=by
   let g i:= f i*Trees.currency B a (X i); let u i:= f i* Real.exp ((a+δ)*coverNumber B (X i)); have hw i:0≤ g i:=mul_nonneg (hf i) (Real.exp_pos _).le
   refine (Ac.lookup X D Y g hw).trans (le_trans (b:=∏ i∈buds X D Y,Real.exp (u i)) ?_ ?_); swap; · rw [←Real.exp_sum]; exact Real.exp_monotone (Ac.demand X B hh Y D)
   refine prod_le_prod (fun i _=>add_nonneg zero_le_one (mul_nonneg (hw _) (sum_nonneg fun p _=> prod_nonneg fun i _=>hw i))) fun i hi=> ?_
   apply le_trans _ (Real.add_one_le_exp _); rw [add_comm]; gcongr; exact (mul_le_mul_of_nonneg_left (H _ (erase_ssubset ((alive X D Y).mp hi).1) (X i)) (hw i)).trans_eq (by unfold g Trees.currency u; rw [add_mul,Real.exp_add,mul_assoc])
lemma sapT [DecidableEq ι]{f:ι→ℝ}{a δ γ:ℝ}(hf:∀ i,0≤ f i)(hh: Ac.Hit X B f (a+δ) γ)(hp:(ballCost B:ℝ)*γ ≤ δ)(he:0≤γ)(D:Finset ι)(Y:Support n) : Ac.film X D Y (fun i=>f i*Trees.currency B a (X i)) ≤ worth m B δ Y:=by
   induction D using Finset.strongInduction generalizing Y with
   | H S hs =>
      have hδ:0≤δ:= (mul_nonneg (Nat.cast_nonneg _) he).trans hp
      apply le_trans (grad X B hf hh S Y (fun P h y=> (hs P h y).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (oldCost ..)) hδ)))) (Real.exp_monotone _)
      have h : (Y.card:ℝ) ≤ ballCost B*(Copse.cover m B Y:ℝ):=by rw [mul_comm]; exact_mod_cast Copse.size m B Y
      nlinarith only [mul_le_mul_of_nonneg_right h he,mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α:=ℝ) (Copse.cover m B Y))]

-- cost written output * weighted Partners.S(all connected). includes polynomial from reserves freely. no cap pedantry.
section
variable [DecidableEq ι]{f:ι→ℝ}{a δ γ:ℝ}
-- avoid quot ambiguity decimal
local notation "B₀" => worth m B
noncomputable def flight (f:ι→ℝ) (j:ι)(a:ℝ)(p:Finset ι):ℝ:= if j∈p∧Ac.Spark X p then worth m B a (p.biUnion X)*(∏ i∈p.erase j,f i) else 0
variable (hf:∀ i,0≤ f i)(hh: Hit X B f (a+δ) γ)(hp:(ballCost B:ℝ)*γ ≤ δ)(he:0≤γ)(ha:0≤ a)
local notation "F" => flight X B m f
include hf
lemma flight_nn (j:ι)(q:Finset ι):0≤F j a q:=by
   unfold flight; split; next h=> exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _=>hf _)
   exact le_rfl
include hh he hp ha
lemma flights (j:ι): SumBudget (F j a) (worth m B (a+δ) (X j)):=by
   let v:= F j a; refine budget_of_sum (flight_nn X B m hf j) fun D =>?_
   let D':=D.filter fun i=> j∈i ∧ Ac.Spark X i; have h' i(h:i∈D'):j∈i∧Ac.Spark X i:= (mem_filter.mp h).2
   let r:=D.biUnion id; let k:= r.erase j; let e : Finset ι → Finset ι:=fun s=> s.erase j
   let g i:= f i*Trees.currency B a (X i); let t:= B₀ a (X j)
   have hx: Set.InjOn e (D':Set (Finset ι)):=fun p h q he eq=>by
       rw [← Finset.insert_erase (h' _ h).1,← Finset.insert_erase (h' _ he).1, show p.erase j=q.erase j from eq]
   have he i (h:i∈ D') : e i ∈ Ac.pouch X k (X j):= Ac.op ..|>.2 ⟨Finset.erase_subset_erase j (fun x hh=>Finset.mem_biUnion.mpr ⟨i,(mem_filter.mp h).1,hh⟩),Ac.excise X (h' _ h).2 (h' _ h).1⟩
   have hV: ∑ s∈D,v s=∑ s∈D',v s:= Eq.symm (sum_subset (Finset.filter_subset ..) (fun i hi hj=>if_neg (fun h=> hj (mem_filter.mpr ⟨hi,h⟩))))
   change ∑ i∈D,v i ≤ _; rw [hV]; unfold worth; rw [add_mul,Real.exp_add]; change _≤t*(B₀ δ (X j))
   apply le_trans (b:= t*Ac.film X k (X j) g) _ (mul_le_mul_of_nonneg_left (sapT X B m hf hh hp ‹0≤γ› k (X j)) (Real.exp_pos _).le)
   calc
     _ ≤ ∑ i∈D', t*∏ x∈e i,g x := sum_le_sum fun i hi=> by
        obtain ⟨hm,h⟩:= h' _ hi; unfold v flight; rw [if_pos ⟨hm,h⟩, show e i=i.erase j from rfl]; simp only [g,Trees.currency,prod_mul_distrib,← Real.exp_sum]; rw [mul_left_comm t,mul_comm (B₀ _ _)]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun x _=>hf x)
        unfold t worth; rw [← Real.exp_add,← Finset.mul_sum,← mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Copse.priced m B X h hm) ha)
     _ = t*∑ i∈D'.image e,∏ j∈i,g j := by rw [Finset.sum_image hx, mul_sum]
     _ ≤ _:= mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (fun i hi=> by obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact he _ hj) (fun i _ _=>prod_nonneg fun j _=> mul_nonneg (hf _) (Real.exp_pos _).le)) (Real.exp_pos _).le
variable (u:ι→ℝ) (w:ℝ)
lemma compass (ht:∀ i,0≤ u i)(h:SumBudget (fun i=>u i*B₀ (a+δ) (X i)) w) : SumBudget (fun p:Finset ι=>∑ j∈ p,u j*F j a p) w := by
   let U (p:Finset ι) i:=u i*F i a p; have hu p i:0≤ U p i:=mul_nonneg (ht _) (flight_nn X B m hf ..)
   refine budget_of_sum (fun i=> Finset.sum_nonneg fun j _=> hu i j) fun S=> ?_
   let D:= S.biUnion id
   calc
     _ ≤ ∑ i∈S,∑ j∈D,U i j:= sum_le_sum (fun i hi=> sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem id hi) (fun j _ _=> hu i j))
     _ ≤ _:= by rw [Finset.sum_comm]; exact le_trans (sum_le_sum (fun i _ => budget_sum (budget_scale (ht i) (flights X B m hf hh hp he ha i)) S)) (budget_sum h _)
end
end YM.UVExtension.Copse
