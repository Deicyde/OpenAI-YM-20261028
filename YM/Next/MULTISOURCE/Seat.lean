import YM.Next.MULTISOURCE.Coffee
import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.Larger


/-! Scalar polynomial approximations of ordinary vacuum densities.
    Receipts may choose z-dependent weights *even at each cutoff scalar*.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open MvPolynomial RG Wilson Lattice Finset Filter MeasureTheory Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {G : Gauge} {n : Side}

/-- Assemble on the actual coverage supports. -/
def chip (P : Rep G n) (U : Config G n) (D : Pack n → Wave I) :=
    C (Real.exp (P.exponent U):ℂ)*(∑ i∈Pack.clears (flags P.p.threshold U), ∏ j∈i,(C (incumbent P U j)+D j))

omit [Fintype I] [DecidableEq I] in
lemma chip_eval (P : Rep G n) (U : Config G n) (D : Pack n → Wave I) (z : I → ℂ) :
    eval z (chip P U D)=baseJoint P U (fun x => eval z (D x)) := by simp [chip,baseJoint]

lemma patch (P : Rep G n) (U : Config G n) (D : Pack n → Wave I) (b : Wave I) (R : Census I)
    {N : ℕ} (h : Fintype.card I ≤ N) (hh : coeff 0 b=0) :
    print R (vapor N b * chip P U D)=composeAt P U (print R b) (fun i => print R (D i)) := by
  rw [map_mul,vapor_print R _ h hh]; simp only [chip,map_sum,map_mul,map_add,map_prod,print_C,composeAt]
  rw [Algebra.smul_def]; change _=Poly.send _ _*_ ; ac_rfl

private lemma site_sums (V : ℕ→Support n) (f : ℕ → ℝ) (L : Finset ℕ) (C : ℝ) (P : BudgetPoint)
    (h : ∀ i,(V i).Nonempty) (hf : ∀ i,0 ≤ f i)
    (hp : ∀ x : Site n,SumBudget (fun i => if x∈V i then burn P 2 (V i)*f i else 0) C) :
    ∑ i∈L,f i ≤ Fintype.card (Site n) * C := by
  let F (i) (x) := if x∈V i then burn P 2 (V i)*f i else 0
  have he i : f i ≤ ∑ x,F i x := by
    obtain ⟨x,hx⟩:=h i
    apply le_trans _ (single_le_sum (f:=F i) (fun y _ => (hp y).1 i) (mem_univ x))
    unfold F; rw [if_pos hx]; exact le_mul_of_one_le_left (hf i) (burn_ge _ (by norm_num) _)
  apply (sum_le_sum (fun i _ => he i)).trans
  rw [sum_comm]; simpa using sum_le_sum (s:=univ) (fun x _ => ((hp x).2.1.sum_le_tsum L (fun i _ => (hp x).1 i)).trans (hp x).2.2)

variable {P : Rep G n} (T : Reservoir P I)

section
variable {p r : ℝ} {K : Set (I→ℂ)} (H : T.Tested p K)
include H
omit [Fintype I] [DecidableEq I] in
lemma several_H (U : Config G n) (z) (hz : z∈K) (L : Finset ℕ) :
    (∑ i∈L, ‖eval z (T.keeps i U)‖) ≤ Fintype.card (Site n) := by
  obtain ⟨f,hf,H'⟩ := H.bulk z hz
  refine le_trans (b:=∑ i∈L,f i) (sum_le_sum ?_) (by simpa using site_sums _ f L 1 _ H.nonempty (fun i => (hf i).1) H')
  intro i _; by_cases he : Healthy P.p.threshold (T.support i) U
  · unfold Reservoir.keeps; rw [masked_eq _ _ _ _ he]; obtain ⟨x,hx⟩ := H.nonempty i
    exact ((hf i).2 _ hx).2 U he [] (by simp) (by simp)
  unfold Reservoir.keeps; rw [masked_ne _ _ _ _ he]; simpa using (hf i).1
omit [Fintype I] [DecidableEq I] in
lemma several_K (U : Config G n) (q : Pack n) (z) (hz : z∈K) (L : Finset ℕ) :
    (∑ i∈L, ‖eval z (T.records q i U)‖) ≤ Fintype.card (Site n) * p := by
  obtain ⟨f,hf,H'⟩ := H.titles z hz
  refine le_trans (b:=∑ i∈L,f i) (sum_le_sum ?_) (site_sums _ f L p _ (fun i =>
      (T.k i).property.1.mono (T.k i).property.2) (fun i => (hf i).1) H')
  intro i _; unfold Reservoir.records; split; exact (hf i).2 U; rw [map_zero,norm_zero]; exact (hf i).1

omit H [Fintype I] [DecidableEq I] in
lemma dye {q : Type*} (F : ℕ → q → ℂ) (S : Set q) {b : ℝ}
    (h : ∀ x ∈ S, ∀ L : Finset ℕ, (∑ i∈L, ‖F i x‖) ≤ b) : Tint S (fun x => ∑' i,F i x) := by
  refine ⟨b,fun x hx => ?_⟩
  have he := summable_of_sum_le (fun i => norm_nonneg (F i x)) (h x hx)
  exact (norm_tsum_le_tsum_norm he).trans (he.tsum_le_of_sum_le (h x hx))

omit [DecidableEq I] in
lemma dyed_E {r : ℝ} (hp : boxes r ⊆ K) (U : Config G n) : Tint (boxes r) fun z => T.tasteE z U := by
  refine tint_add ?_ (dye _ (boxes r) fun _ hz => several_H T H U _ (hp hz))
  simp only [staves_eval]
  apply tint_sum; intro i
  refine tint_mul ⟨r, fun z (hz: z∈ boxes r) => ?_⟩ (tint_fix ..)
  exact hz i

omit [Fintype I] [DecidableEq I] in
lemma dyed_K {r : ℝ} (hp : boxes r ⊆ K) (U : Config G n) (q : Pack n) :
    Tint (boxes r) (fun z => T.tasteK q z U) := dye _ _ fun _ hz => several_K T H U q _ (hp hz)
end
end YM.Multi.Desk
