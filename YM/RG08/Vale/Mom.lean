import YM.RG08.Tall.Ridge
import YM.Planned.PRIMARY_INTEGRAL_295.Stain
/-!
# Read of a marked kernel in true cover moments

For convenience we can use product moments at fixed bigger order; applies
*also* without a strip, as at capture. Higher-order cross terms in stable
induction may have to use bigger moment orders at strict taxa. Charges
and demands to be made before block choices.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire
open scoped Topology ContDiff Classical BigOperators
variable {α β γ E F ι : Type} [NormedAddCommGroup E] {r k u : ℕ} {m : Side}
variable {V U:Rooted E α r} {C A σ : ℝ}
abbrev dime := Carrier.liftCost
def mint (k : ℕ) (b : Beads α r) := ∏ i,dime k (b i).1
lemma dime_more {n k:ℕ} (h:n≤k) : dime n ≤ dime k := fun i=> pow_le_pow_right₀ (by simp) h
lemma mint_more {n k:ℕ} (h:n≤k): mint (r:=r) (α:=α) n≤mint k := fun i=> prod_le_prod (fun j _=>Carrier.liftCost_pos ..) (fun j _=> dime_more h _)
lemma mint_one (α:Type) (r k:ℕ): 1≤mint (r:=r) (α:=α) k := fun i=> one_le_prod (fun j _=> Carrier.liftCost_ge ..)
lemma mint_pos (α:Type) (r k:ℕ): 0≤mint (r:=r) (α:=α) k := fun i=> (mint_one α r k i).trans' zero_le_one
lemma lower_bill (b : Beads α r) (k : ℕ) : (1+(girth b:ℝ))^k≤mint k b := by
  unfold mint dime Carrier.liftCost; rw [prod_pow]; apply pow_le_pow_left₀ (by positivity)
  simp only [girth,Nat.cast_sum]; suffices ∀ s:Finset (Fin r), 1+∑ i ∈s,(size (b i).1:ℝ) ≤ ∏ i∈s,(1+(size (b i).1:ℝ)) from this _
  intro s; induction s using Finset.induction_on with
  | empty=>simp
  | insert i s hi ih=>
    rw [sum_insert hi,prod_insert hi]; calc
     _ ≤ (1+(size (b i).1:ℝ))*(1+∑ j∈s, (size (b j).1:ℝ)) := by nlinarith [show 0≤(size (b i).1:ℝ) by positivity, show 0≤∑ j∈s,(size (b j).1:ℝ) by positivity]
     _ ≤ _ := mul_le_mul_of_nonneg_left ih (by positivity)
lemma greater_bill (b : Beads α r) (k : ℕ) : mint k b≤ (1+(girth b:ℝ))^(k*r) := by
  calc
    _ ≤ ∏ _ : Fin r,(1+(girth b:ℝ))^k := prod_le_prod (fun i _=>Carrier.liftCost_pos ..) (fun i h=> by
      unfold Carrier.liftCost; gcongr; exact single_le_sum (fun j _=>Nat.zero_le (size (b j).1)) h)
    _=_ := by rw [prod_const, pow_mul]; simp
abbrev Polished (U : Rooted E α r) := ∀ k, ∃ A:ℝ, Ink (mint k) U A
lemma polish (he:Lit U σ A)(hp:0<σ) (k:ℕ): Ink (mint k) U (((σ⁻¹)^(k*r)*((k*r).factorial:ℝ)* Real.exp σ)*A) := by
  have hc : 0 ≤ (σ⁻¹)^(k*r)*((k*r).factorial:ℝ)* Real.exp σ := by positivity
  apply budget_mono (budget_scale hc he) (fun i=>mul_nonneg (mint_pos α r k i) (norm_nonneg _)); intro i
  have hx := greater_bill i k
  refine (mul_le_mul_of_nonneg_right (hx.trans (polynomial_price hp (show 0 ≤ (1+(girth i:ℝ)) by positivity) (k*r))) (norm_nonneg _)).trans_eq ?_
  rw [mul_add,mul_one,Real.exp_add,ling]; ring
lemma scarlet (h : Lit U σ A) (hp:0<σ): Polished U := fun i=>⟨_,polish h hp i⟩
lemma polished_zero (E α:Type)[NormedAddCommGroup E] (r : ℕ): Polished (0:Rooted E α r) := fun i=>⟨_,Ink.none ..⟩
lemma polished_neg (h:Polished U) : Polished (-U) := by intro i; obtain ⟨x,h⟩:=h i; exact ⟨_, Ink.neg h⟩
lemma polished_more (h:Polished U)(hv:Polished V) : Polished (U+V) := by intro i; obtain ⟨x,h⟩:=h i; obtain ⟨y,hv⟩:=hv i; exact ⟨_, Ink.plus h hv (mint_pos _ _ _)⟩
lemma polished_scale [NormedSpace ℝ E] (h:Polished U)(k:ℝ) : Polished (k•U) := by intro i; obtain ⟨x,h⟩:=h i; exact ⟨_, h.scale _⟩
lemma polished_pens (h : Polished U) : Pens U := (Ink.pens (h 0).choose_spec (mint_one _ _ _))
lemma polished_fun [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℝ E] (h:Polished U) (e:E→L[ℝ] F) : Polished (e∘U) := by intro i; obtain ⟨x,h⟩:=h i; exact ⟨_, h.some _ (mint_pos _ _ _)⟩
lemma polished_sum {s : Finset ι} {f:ι→Rooted E α r} (h:∀ i∈s, Polished (f i)) : Polished (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty]; exact polished_zero E α r
  | insert i s hi ih=>rw [sum_insert hi]; exact polished_more (h i (mem_insert_self ..)) (ih fun j hj=> h _ (mem_insert_of_mem hj))

variable {H H': Shale α r}
def wallet (g : Shale α r) (v : Fin r→ Cover×α→ℝ) := ∑' b:Beads α r, g b * ∏ i,v i (b i)
lemma takes (h : Ink (mint k) H A) {v : Fin r→Cover×α→ℝ} {C:Fin r→ℝ} (hp : 0 ≤ C) (hv : ∀ i p, ‖v i p‖ ≤ C i*dime k p.1) :
    SumBudget (fun b : Beads α r => ‖H b * ∏ i,v i (b i)‖) ((∏ i,C i)*A) := by
  have he : 0≤∏ i,C i := Finset.prod_nonneg fun i _=> hp i
  apply budget_mono (budget_scale he h) (fun _=> norm_nonneg _); intro i
  rw [norm_mul,norm_prod]
  calc
    _ ≤ ‖H i‖*(∏ j,C j*dime k (i j).1) := (mul_le_mul_of_nonneg_left (prod_le_prod (fun j _=> norm_nonneg _) (fun j _=> hv j _)) (norm_nonneg _))
    _ = _:= by rw [prod_mul_distrib,mint]; ring
lemma wallet_cost (h : Ink (mint k) H A) {v : Fin r → Cover×α→ℝ} {C:Fin r→ℝ} (hp:0≤C)(he:∀ i p, ‖v i p‖≤C i*dime k p.1): ‖wallet H v‖≤(∏ i,C i)*A := (norm_tsum_le_tsum_norm (takes h hp he).2.1).trans (takes h hp he).2.2
variable [Fintype α]
lemma wallet_limit {m : ℕ→Side} (hm : Tendsto (fun i=>(m i).val) atTop atTop) (h : Polished H)
    {f : Fin r→ Cover×α→ℝ} {v : (n:ℕ)→Fin r→PAC α (m n)} (hp : ∀ (j : Fin r) p, Tendsto (fun n=>v n j (wrap (m n) p.1,p.2)) atTop (𝓝 (f j p)))
    {C:Fin r→ℝ} (k:ℕ)(he:0≤C)(hv : ∀ i p (a:α) n, ‖v n i (wrap (m n) p,a)‖ ≤ C i*dime k p) :
    Tendsto (fun n=> stitch H (m n) 0 (v n)) atTop (𝓝 (wallet H f)) := by
  have hx:= budget_scale (f:=fun i=>mint k i*‖H i‖) (show 0≤∏ i,C i from prod_nonneg fun i _=>he i) (h k).choose_spec
  unfold wallet; simp_rw [stitch_apply (polished_pens h).of_norm,rosary,silks,zero_add]
  refine tendsto_tsum_of_dominated_convergence hx.2.1 (fun b=> ?_) (Eventually.of_forall fun n i=>?_)
  · exact tendsto_const_nhds.mul (tendsto_finsetProd _ fun j _=> hp j _)
  rw [norm_mul,norm_prod]; refine (mul_le_mul_of_nonneg_left (prod_le_prod (fun j _=> norm_nonneg _) (fun j _=> hv j (i j).1 _ _)) (norm_nonneg _)).trans_eq ?_
  rw [prod_mul_distrib,mint]; ring
end YM.RG08.Vale
