import YM.RemainderComparison.Creek.Observatory

/-! # Paying root sums before flattening parent addresses -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Breeze
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {ι α J:Type} {c f:Side} {G : Gauge} {S: StepData c f} {a d : ℝ}{n:ℕ}
lemma charge_root {g:ι→ℝ}{b:ℝ} (h:SumBudget g b) (k:ℕ): SumBudget (fun v:Finset ι=>if v.card≤ k then ∏ i∈v,g i else 0) (((b+1)^k)*Real.exp 1):=by
   let y:= b+1; have hp: 1≤ y:=le_add_of_nonneg_left (budget_nonneg h); have hv:0 < y:=zero_lt_one.trans_le hp
   have he: y⁻¹*b≤1:=by rw [inv_mul_eq_div]; apply (div_le_one hv).2; exact le_add_of_nonneg_right zero_le_one
   apply budget_mono (budget_scale (pow_nonneg hv.le k) (Product.set_products (budget_loosen (budget_scale (by positivity) h) he)))
   · intro i; split; exact prod_nonneg (fun j _=> h.1 j); exact le_rfl
   intro i; split
   next h'=>
     let p:= (∏ j∈i,g j); have hz:0 ≤ p:=prod_nonneg (fun j _=>h.1 j)
     rw [Finset.prod_mul_distrib, Finset.prod_const, inv_pow, ← mul_assoc]; exact le_mul_of_one_le_left hz (show 1 ≤ y^k* (y^i.card)⁻¹ from (by rw [← div_eq_mul_inv]; exact (one_le_div (by positivity)).2 (pow_le_pow_right₀ hp h')))
   next h'=> exact mul_nonneg (pow_nonneg hv.le k) (prod_nonneg fun j _=>mul_nonneg (inv_pos.mpr hv).le (h.1 j))

-- Pose designate PAGE Universe. Geometry receipts at each projected chart root. Doesn’t assume per leaf uniforms (important when any fine positions and any p.K.Prior). If only possible structural sheets FIN-involvement.V independent.S
structure Careers (ι E:Type)(c:Side)(o:ι→Site c) (r k:ℕ) where
    pocket : E↪ Finset ι
    o' : E→Site c
    localR i j : j∈ pocket i → separation (o' i) (o j)≤r
    admits i : (pocket i).card ≤ k
variable (o:ι→Site c) (w:ι→ℝ){r k:ℕ} {B:ℝ}

def areaBudget (r k:ℕ)(A:ℝ):ℝ:= (((ballCost r:ℕ)*A+1)^k)*Real.exp 1
lemma ribbons (X: Careers ι J c o r k)(hw:∀ i,0≤ w i)(hh:∀ i:Site c, SumBudget (fun j=> if o j=i then w j else 0) B):
    ∀ x:Site c, SumBudget (fun i=> if X.o' i=x then ∏ j∈ X.pocket i, w j else 0) (areaBudget r k B) :=by
    intro x; let S:= neighbors r x; let b i:= if o i ∈ S then w i else 0
    have hb : SumBudget b ((ballCost r)*B):=by
       have ht:= budget_over S (fun i j=> if o j=i then w j else 0) _ (fun i _=> hh i)
       simp only [Finset.sum_ite_eq,sum_const,nsmul_eq_mul] at ht; exact budget_loosen ht (mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (budget_nonneg (hh x)))
    let p:=charge_root hb k
    refine budget_mono (budget_pull _ X.pocket.injective p) (fun i=>by split; exact prod_nonneg (fun j _=>hw j); exact le_rfl) (fun i=>?_)
    split
    next hx=>
       rw [if_pos (X.admits i)]; exact le_of_eq (prod_congr rfl (fun j hj=> Eq.symm (if_pos (show o j∈ S from (neighbors_mem ..).2 (hx ▸ X.localR i j hj)))))
    next=> exact p.1 _

-- Can reduce projected capacity to fine-site histories when RU data priced. Include P.Occupancy on ACT clocks.C.Align.
variable [Fintype α] (F:α→Site c) {K:ι→Finset α}
lemma splines (hv:∀ i,0≤w i)(h: Extra.Multi.Occupancy F n) (hq: ∀ s : α, SumBudget (fun i=> if s∈K i then w i else 0) a) (ha:0≤ a)(ht:∀ i,0<w i→∃ k∈K i,o i=F k):
     ∀ x:Site c, SumBudget (fun i=>if o i=x then w i else 0) ((n:ℝ)*a) :=by
   intro x; let p:= (univ:Finset α).filter (fun i=> F i=x)
   refine budget_loosen (budget_mono (budget_over p _ _ (fun i _=> hq i)) (fun i=>by split; exact hv i; exact le_rfl) fun i=>?_) ?_
   · split; next H=>
       by_cases hp:0<w i
       · obtain ⟨k,hk,hv⟩:= ht i hp; have he:k∈p:=mem_filter.mpr ⟨mem_univ _,hv.symm.trans H⟩; exact le_trans (le_of_eq (show w i=(if k∈K i then w i else 0) from (if_pos hk).symm)) (single_le_sum (f:=fun j:α=>if j∈K i then w i else 0) (fun _ _=>(hq _).1 i) he)
       exact le_trans (not_lt.mp hp) (sum_nonneg (fun j _=>(hq j).1 i))
     next=> exact sum_nonneg fun j _=>(hq j).1 i
   rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h x) ha
end YM.RemainderComparison.Breeze
