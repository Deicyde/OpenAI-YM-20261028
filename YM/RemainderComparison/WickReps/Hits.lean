import YM.RemainderComparison.WickReps.Coffer

/-! # Single representation acquisitions before assembly: new E and mask price
    cost on every unmasked occurrence and absorbed for ANY enlargement (uniform reserves)
    This is the seam mechanism; any redo onto canonical paths must honor these costs
    and mask budgets before invoking merger again.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n c C f L : Side} {Y:Stars→Side} {P:BudgetPoint}{r z k w m p:ℕ}{a b β v R e x:ℝ}
variable {α:Type*}{ι J J' θ:Type}

lemma boot (P:BudgetPoint) (hv:r ≤ m*P.B) {t:J→ℝ} {o:J→Site c} {τ:ℝ} (ht:∀ i,0 ≤ t i) (hp:∀ i:Site c, SumBudget (fun j=> if o j=i then t j else 0) τ) (k:ℝ)(h:0≤k):
     Ac.Hit (fun i=> neighbors r (o i)) P.B t k (Real.exp (k*((m+m+1)^4:ℕ))* (ballCost r *τ)):=by
    intro x
    let s:= Real.exp (k*((m+m+1)^4:ℕ)); have hz : 0 ≤ s:= Real.exp_nonneg _
    have hW:= budget_over (neighbors r x) (fun i j=> if o j=i then t j else 0) _ (fun i _=>hp i)
    refine budget_loosen (budget_mono (budget_scale hz hW) ?_ ?_) ?_
    · intro i; split; exact mul_nonneg (ht _) (Real.exp_pos _).le; exact le_rfl
    · intro i; split; next h' =>
         have hx : o i ∈ neighbors r x:= (neighbors_mem ..).2 (by rw [separation_comm]; exact (neighbors_mem ..).1 h')
         dsimp only; rw [sum_ite_eq,if_pos hx,mul_comm]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ h)) (ht i); exact_mod_cast Arc.viewM (o i) hv
      next h'=> exact (budget_scale hz hW).1 i
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (budget_nonneg (hp x))) hz

-- fin card event cost for leaks. T_S selection disjoint on reindexed branches. Keep allocations at support HIT orientations. When expanding further root positions, may rely on these before budgets.
lemma founding (P:BudgetPoint) (hv:r ≤ m*P.B) (ht:0 ≤ b) (k:ℝ)(h:0≤k):
     Ac.Hit (fun i:Site c=> neighbors r i) P.B (fun _=> b) k (Real.exp (k*((m+m+1)^4:ℕ))* ((ballCost r)*b)):=
    boot P hv (fun _=>ht) (fun i=>budget_finite (fun j=>by split; exact ht; exact le_rfl) (by simp)) k h

namespace Manor
variable (T:Manor G c ι α J)(s:Finset J)
variable (B:T.Basis s r) {root:ι→ Support c}
variable (Q: ∀ i:Stars,(Y i).val=2*(w+i.val))
variable (fa:α→∀ i:Stars,Offer G (Y i)) {q p':Stars→ℝ} {t:α→ Stars→ℝ}

def mansion (k:ℕ) : Manor G c ι α (Site c):= ⟨fun x=>⟨x,neighbors k x,(neighbors_mem ..).mpr (by simp [separation,pdist]; -- normalize
                  )⟩,fun y=> Trio.ornament Q (fa y),fun _=>∅,fun _=> False⟩ -- explicit c variables r
local notation "X" => (Manor.mansion Q fa z : Manor G c ι α (Site c))
lemma cast (hf: z ≤ m*P.B)(ha:0 ≤ a)(hp:∀ y i j,P.Regular univ (fa y i j)) (hw:w+5≤ z)(hc:2*z<c.val) (hρ:Arc.Deduct G P β z R)(hg:0≤ R)(hO:∀ u i,Portal.Mare P (Trio.froth (fa u i) -fun _=>t u i) β R (q i)) (hQ:∀ i,0 ≤ q i):
     Templary X Set.univ root P a ((warmth P z q)*Real.exp (a*((m+m+1)^4:ℕ))):=by
    have he (u:α)(x:Site c):=Southern Q (fa u) hg hw hc (hp u) hρ (hO u) x
    let c':=warmth P z q; have hc:0≤ c':=by unfold c' warmth oroW; exact sum_nonneg fun i _=> mul_nonneg (abs_nonneg _) (mul_nonneg (by unfold Trio.tilt; positivity) (add_nonneg (hQ _) (hQ _)))
    refine ⟨fun _=>c',fun _=>hc,fun i _=>⟨⟨fun a=> (he a i).1,fun a j h=> (Multiset.notMem_zero _ h).elim,fun a h=> ?_⟩,fun a=> (he a i).2⟩,fun x=>?_⟩
    · contradiction
    refine budget_finite (fun i=>?_) ?_
    · split; exact mul_nonneg hc (Real.exp_pos _).le; exact le_rfl
    rw [Finset.sum_eq_single x]; rotate_left
    · intro i _ hh; exact if_neg hh
    · simp
    dsimp only; rw [if_pos (show port X x=x from rfl)]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ ha)) hc; exact_mod_cast (Arc.viewM x hf)

-- Leak cost witnesses with predicates before cancellation and sup over all α. Components cut all explicit and grouped.
variable {K ℓ:ℕ}{V σ:ℝ}
variable (P : BudgetPoint) (h:T.Templary (s:Set J) root P V v)
section
structure Expulsion (T:Manor G c ι α J) (s:Finset J) (P:BudgetPoint) {r:ℕ} (B:T.Basis s r) (Q: ∀ i:Stars,(Y i).val=2*(w+i.val)) (k z:ℕ)
   (fa:α→∀ i:Stars,Offer G (Y i)) (a b:ℝ) : Prop where
   awake u i : Tidy P (neighbors k i) (T.currencies u s P B Q (fa u) z i)
   missed x y i : Healthy P.threshold (neighbors k i) y→ T.currencies x s P B Q (fa x) z i y=0
   budget : ∃ f:Site c→ℝ,(∀ x,0 ≤ f x) ∧ Ac.Hit (fun x=>neighbors k x) P.B f a b∧ ∀ i x v, ‖T.currencies x s P B Q (fa x) z i v‖≤ f i
include h
lemma seized (hq : ∀ u, Sensible P r (sector T u s B) (fa u))(hp:0 ≤ V)(hσ:0 ≤ σ)(hr:0<r) (hrt:2*r≤w)(he:2*z≤k)(hc: 4*r+16≤c.val)(hw:w+4≤ z) (hh:∀ a i j,P.Regular univ (fa a i j)) (p:Stars→ℝ) (hv:∀ a i x (V:Config G (Y i)),flags P.threshold V=∅→‖fa a i x V‖ ≤ p i) (hz:k≤ m*P.B) (ht:∀ i,0≤ p i):
    Expulsion T s P B Q k z fa σ (Real.exp (σ*((m+m+1)^4:ℕ))* ((ballCost k)*Manor.salary Y (ballCost r) v p)):=by
   have hv(u:α)(i:Site c):= Manor.region T u s P B h Q (fa u) hp (hq u) hr hrt he hc hw (hh u) i p (hv u)
   let y:=Manor.salary Y (ballCost r) v p; have hy: 0 ≤ y:=by unfold y salary; have he:= budget_nonneg (h.grants.choose_spec.2.2 (0:Site c)); exact add_nonneg (by positivity) (sum_nonneg fun i _=> mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (add_nonneg (ht _) (ht _))))
   exact ⟨fun u i=> (hv u i).1,fun i x V=> ((hv i V).2 x).2,fun _=> y,fun _=>hy,founding P hz hy σ hσ,fun i x V=>((hv x i).2 V).1⟩
end
end Manor
end YM.RemainderComparison.WickReps
