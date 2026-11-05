import YM.FullVolume.Ray.Special
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
/-! Exact quantitative pricing of (degree bounded)-in-parameter entries from on-unit real nodes, V-derivative scale arbitrary. Handles optional exp points by inverting log. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Finset Polynomial Metric
open scoped Topology BigOperators NNReal ContDiff
section poly
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k m:ℕ} (r:Fin (k+1)→↑sun)
    {f:ℝ→E→ℝ} {x:E} {a p d : ℝ} (he:Injective (fun i=> (r i).val)) (hp:1≤p)
abbrev side (i:Fin (k+1)) := ink.lamp (fun j=> (r j).val) i
def pot (i:Fin (k+1)) : ℝ:= ∑ l∈range (k+1), ‖(Lagrange.basis Finset.univ (fun j=> (r j).val) i).coeff l‖
def bounty :ℝ:=∑ i,pot r i
lemma pot_nn (i):0≤pot r i:=by unfold pot; positivity
lemma bounty_nn: 0≤bounty r:= Finset.sum_nonneg (fun i _=>pot_nn _ i)
include he hp
lemma candles (i): Scout p (side r i) (pot r i * p^k):=by
  let s:= Finset.univ (α:=Fin (k+1))
  let V:=Lagrange.basis s (fun j=>(r j).1) i
  have h: V.natDegree<k+1:=by
    rw [show V.natDegree=s.card-1 from (by unfold V; exact Lagrange.natDegree_basis he.injOn (Finset.mem_univ i)),show s.card=k+1 from (by simp [s])]; omega
  have hf n: Scout p (fun t=> V.coeff n*t^n) (‖V.coeff n‖*p^n):= ((Scout.line hp).power n).scale _
  refine ((Scout.pieces (range (k+1)) _ _ hp (fun k _=> hf k)).enlarged ?_).replace (fun t ht=> (eval_eq_sum_range' h t).symm)
  unfold pot; rw [Finset.sum_mul]; apply sum_le_sum; intro j hj; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (Nat.le_of_lt_succ (mem_range.mp hj))) (norm_nonneg _)
lemma starpath (hq:0≤ a) (hz: ∀ i,Brush m a d (f (r i).val) x) (ht : ∀ y:E,∃ g:ℝ→ℝ,EqOn g (fun t=>f t y) sun∧ ink k g) :Weigh m x p ((bounty r*p^k)*a) d f:=by
  have hm (t:ℝ) (h:t∈sun): f t=(fun y=> ∑ i,side r i t*f (r i).val y):=by
    funext y; obtain ⟨g,he',hh⟩:= ht y; rw [show f t y=g t from (he' h).symm, ink.tour _ hh he]; apply sum_congr rfl; intro i _; rw [mul_comm (side ..),show g (r i).val=f _ _ from he' (r i).property]
  have hb : 0≤d:= (hz 0).pos
  refine ⟨hb,fun i hi=>by rw [hm i hi]; exact ContDiffAt.sum (fun j _=> contDiffAt_const.mul (hz j).smooth),fun y hy n hn=>?_⟩
  let g j t := side r j t*marked n (f (r j).val) x y; let P j:= (a*d^n)*(pot r j * p^k)
  have hx j: Scout p (g j) (P j):= ((Scout.multiplies (candles r he hp j) ((Scout.still hp _).enlarged (point_norm (hz j) hn hy)))).enlarged (le_of_eq (mul_comm ..))
  refine ((Scout.pieces Finset.univ g P hp (fun i _=>hx i)).enlarged ?_).replace ?_
  · apply le_of_eq; unfold P; rw [← mul_sum, ← sum_mul]; unfold bounty; ring
  intro t ht; symm; dsimp only; rw [hm t ht]; unfold marked
  let b j (z:ℝ):= (f (r j).val ∘ tintM x y) z; have hv j : ContDiffAt ℝ n (b j) 0:= sheen ((hz j).smooth.of_le (Nat.cast_le.mpr hn)) y
  exact (iteratedDeriv_fun_sum (I:=Finset.univ) (fun j _=> show ContDiffAt ℝ n (fun z=>side r j t*b j z) 0 from contDiffAt_const.mul (hv j))).trans (sum_congr rfl fun j _=> iteratedDeriv_const_mul _ (hv j)) -- edit
end poly
end YM.FullVolume.Ray
