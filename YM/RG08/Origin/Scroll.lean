import YM.RG08.Peals.Heat
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Series combinators, `tau^n g^e` ordinary powers

Auxiliary algebra, no analytic evaluation at nonzero coupling. Pure actions
are real series. Real-density expansions at noncentral offsets NOT assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Finset Filter
open scoped Topology ContDiff
variable {R : Type} [CommSemiring R]
section sea
open PowerSeries
-- tau-outer then g

def pairsR (f : Scroll R) := PowerSeries.mk (fun i => PowerSeries.mk (f i))
-- don't leak notation
lemma peek (f : Scroll R) (i j) : (coeff j) (coeff i (pairsR f))= f i j := by simp [pairsR]
lemma pairs_inj : Injective (pairsR (R:=R)) := fun f g h => funext fun i => funext fun j => by rw [← peek f i j, h, peek]
lemma peered {F H : PowerSeries (PowerSeries R)} (he : ∀ i j, (coeff j) (coeff i F)=(coeff j) (coeff i H)) : F=H := PowerSeries.ext fun i=> PowerSeries.ext (he i)

def dancing (f g : Scroll R) : Scroll R := fun n e => ∑ b∈wheel n,∑ a∈wheel e, f b.1 a.1 * g b.2 a.2
lemma pair_mul (f g : Scroll R) : pairsR (dancing f g)=pairsR f*pairsR g := by
  apply peered; intro i j; rw [peek,coeff_mul,map_sum]; simp_rw [coeff_mul,peek]; rfl
lemma pair_add (f g : Scroll R) : pairsR (f+g)=pairsR f+pairsR g := by apply peered; intro i j; rw [peek,map_add,map_add,peek,peek]; rfl

lemma dance_rotate (f g h : Scroll R) : dancing (dancing f g) h=dancing f (dancing g h) := pairs_inj (by simp_rw [pair_mul,mul_assoc])
lemma dance_sym (f g : Scroll R) : dancing f g=dancing g f := pairs_inj (by rw [pair_mul,pair_mul,mul_comm])
lemma dance_add (f g h : Scroll R) : dancing f (g+h)=dancing f g+dancing f h := pairs_inj (by rw [pair_mul,pair_add,pair_add,mul_add,pair_mul,pair_mul])

-- nsmul operators deflect ambiguity

def countG (f : Scroll R) : Scroll R := fun i e=> e • f i e
def countT (f : Scroll R) : Scroll R := fun n e=> (n+1) • f (n+1) e
lemma counters (f : Scroll R) : countG (countT f)=countT (countG f) := funext fun i=> funext fun j=> smul_comm j (i+1) _
lemma countGn (f g : Scroll R) : countG (dancing f g)=dancing (countG f) g+dancing f (countG g) := by
  funext n e; simp_rw [Pi.add_apply,countG,dancing,smul_sum, ← sum_add_distrib];
  apply sum_congr rfl; intro p _; apply sum_congr rfl; intro a ha
  unfold countG; rw [← mem_antidiagonal.mp ha,add_smul]; simp only [nsmul_eq_mul]; ring
lemma countT_pairs (f : Scroll R) : pairsR (countT f)= (PowerSeries.derivative (PowerSeries R)) (pairsR f) := by
  apply peered; intro n e; rw [peek,countT,PowerSeries.coeff_derivative]
  rw [mul_comm,show (↑n+1:PowerSeries R)=↑(n+1:ℕ) from (Nat.cast_add_one _).symm,← nsmul_eq_mul]; rw [map_nsmul,peek]
private lemma tally_mul (a b : PowerSeries R) :
    PowerSeries.derivative R (a*b)= PowerSeries.derivative R a*b+a* PowerSeries.derivative R b := by
  have hx := (PowerSeries.derivative R).leibniz a b; rw [hx]; rw [smul_eq_mul,smul_eq_mul]; ring
lemma countTn (f g : Scroll R) : countT (dancing f g)=dancing (countT f) g+dancing f (countT g) := by
  apply pairs_inj; rw [countT_pairs,pair_mul,tally_mul,pair_add,pair_mul,pair_mul,countT_pairs,countT_pairs]
lemma dance_crown (f g : Scroll R) (e) : dancing f g 0 e=∑ a∈wheel e,f 0 a.1*g 0 a.2 := by simp [dancing,wheel]
lemma muted_counts (f : Scroll R) : Muted _ (countG f) := by simp [Muted,countG]
lemma dance_left_muted (f g : Scroll R) (h : Muted _ f) : Muted _ (dancing f g) := by unfold Muted at *; simp [dancing,wheel,h]
lemma dance_quiet (f x y : Scroll R) (h : Muted _ f) {k : ℕ} (hx : ∀ j<k, ∀ i,x i j=y i j) (n : ℕ) : dancing f x n k=dancing f y n k := by
  apply sum_congr rfl; intro p hp; apply sum_congr rfl; intro a ha; by_cases he:a.1=0
  · rw [he,h p.1,zero_mul,zero_mul]
  rw [hx a.2 (by have ht := mem_antidiagonal.mp ha; omega) p.2]
lemma dance_sum (s : Finset ℕ) (f : ℕ→Scroll R) (g : Scroll R) : dancing g (∑ i∈s,f i)=∑ i∈s,dancing g (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; ext i j; simp [dancing]
  | insert i s hi ih => rw [sum_insert hi,sum_insert hi,dance_add,ih]
-- later need general sums.
end sea
end YM.RG08
