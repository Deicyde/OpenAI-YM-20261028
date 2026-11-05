import YM.Next.RANK.Flux.Radius

/-!
# Anchor budget theorem on Log of NILPOTENT activities

Then carry moments through any restricted subset. Estimates are per real parent or
coordinate, independent of Fintype card. Norm sums retain support charges. For step
through many marks the pre-L constant here is important. Use `monetized`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG
open scoped BigOperators Classical

variable {V W ι : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
variable {n : Side} (X : V → Support n) (b : V→ℝ) (M : ℕ) (a : ℝ)

def alarm (j : V) := b j*Real.exp (a * coverNumber M (X j))
def honey (s : Finset V):= ‖majesty X s‖ * ∏ i∈s,alarm X b M a i
def hailst (s : Finset V)(i : V):= s.powerset.filter fun t=> i∈t
lemma gold (A : Prop) [Decidable A] (v : ℂ) : ‖(if A then v else 0)‖= if A then ‖v‖ else 0:=by split<;>simp
omit [Fintype V] [DecidableEq V] in
lemma alarm_pos (h : ∀ i,0≤ b i) j : 0≤alarm X b M a j := mul_nonneg (h _) (Real.exp_pos _).le
lemma honey_pos (h : ∀ i,0≤ b i) j : 0≤ honey X b M a j := mul_nonneg (norm_nonneg _) (prod_nonneg fun i _=> alarm_pos X b M a h i)
lemma any_root (A : Finset V) {v : V} (he : ∀ i,0 ≤ b i) : (∑ s∈hailst A v,honey X b M a s)≤
    alarm X b M a v * Real.exp (∑ s∈omitX X A v,honey X b M a s) := by
  let D:= alarm X b M a; let F:=honey X b M a; let u:=D v; let P:= omitX X A v; let C:=hailst A v
  have ht s (hv : s∈C): F s ≤ u*(∑ x∈P.powerset,if charges x (s.erase v) then ∏ i∈x,F i else 0) := by
    obtain ⟨hk,hz⟩:=mem_filter.mp hv
    unfold F honey; rw [pivot X (mem_powerset.mp hk) v hz]; try rfl
    refine le_trans (mul_le_mul_of_nonneg_right (norm_sum_le ..) (prod_nonneg fun i _=> alarm_pos X b M a he i)) (le_of_eq ?_)
    rw [sum_mul, mul_sum]; apply sum_congr rfl; intro i _; rw [gold]; split
    · rename_i h
      unfold u D
      rw [norm_prod,← sum_boost h hz]; try rfl
    rw [zero_mul,mul_zero]
  calc
    _ ≤ _ := sum_le_sum ht
    _ = u*∑ x∈P.powerset,∑ s∈C,if charges x (s.erase v) then ∏ i∈x,F i else 0 := by rw [← Finset.mul_sum, sum_comm]
    _ ≤ u*∑ x∈P.powerset,∏ i∈x,F i:= by
      apply mul_le_mul_of_nonneg_left _ (alarm_pos X b M a he _)
      apply sum_le_sum; intro x _
      by_cases hh:∃ s∈C,charges x (s.erase v)
      · obtain ⟨s,hs,h⟩:=hh; rw [Finset.sum_eq_single s,if_pos h]
        · intro i hi hn; split
          · rename_i he; exact False.elim (hn (by rw [← insert_erase (mem_filter.mp hs).2,← he.1.symm.trans h.1,insert_erase (mem_filter.mp hi).2]))
          rfl
        simp [hs]
      rw [Finset.sum_eq_zero (fun i hi=> if_neg fun h=> hh ⟨i,hi,h⟩)]; exact prod_nonneg fun i _=> honey_pos X b M a he i
    _ ≤ _:= by
      apply mul_le_mul_of_nonneg_left _ (alarm_pos X b M a he _)
      rw [← show ∏ i∈P,(F i+1) = ∑ x∈P.powerset,∏ i∈x,F i from (Finset.prod_add F (fun _=>1) P).trans (Finset.sum_congr rfl fun i _=> by rw [prod_const_one,mul_one]),Real.exp_sum];exact prod_le_prod (fun i _=> add_nonneg (honey_pos X b M a he i) zero_le_one) (fun i _=> Real.add_one_le_exp _)
where
  sum_boost {x s} (h : charges x (Finset.erase s v)) (hz : v∈s) : alarm X b M a v*(∏ i∈x,honey X b M a i)= (∏ i∈x,‖-majesty X i‖)*(∏ i∈s,alarm X b M a i):= by
    let T:= alarm X b M a
    unfold honey; rw [prod_mul_distrib]
    have hf : ∏ i∈x,∏ j∈i,T j=∏ i∈s.erase v,T i:= h.1 ▸ Eq.symm (prod_biUnion (s:=x) h.2)
    rw [hf]; simp only [norm_neg]; change T v*(_*_)=_; rw [mul_left_comm,Finset.mul_prod_erase _ T hz]
lemma all_marks {γ : ℝ} (D : Finset V) (i : V) (h : ∀ i,0 ≤ b i) (H : Ac.Hit X M b (a+1) γ) (he : ((M+M+1:ℕ):ℝ)^4 * γ ≤ 1) (hh : 0 ≤ γ) :
    (∑ s∈hailst D i,honey X b M a s)≤ alarm X b M (a+1) i := by
  induction D using Finset.strongInduction generalizing i with
  | H s ih =>
  let T:=hailst s i; let P:= omitX X s i; let F:=honey X b M a; let g:=alarm X b M (a+1)
  by_cases hz:i∈s
  · have ht : ∑ p∈P,F p ≤ coverNumber M (X i) := by
      calc
        _ ≤ ∑ p∈P, ∑ j∈ X i, if j∈p.biUnion X then F p else 0 := by
          apply sum_le_sum; intro q hq; obtain ⟨j,hj⟩ := plural X hq
          rw [mem_inter] at hj
          apply le_trans _ (single_le_sum (f:=fun j=>if j∈q.biUnion X then F q else 0) (fun v hv=>by split; exact honey_pos X b M a h q; exact le_rfl) hj.2); rw [if_pos hj.1]
        _ ≤ (X i).card*γ := by
          rw [sum_comm, ← show ∑ _∈X i,γ = (X i).card*γ by simp]; apply sum_le_sum; intro v hv
          have hx : ∑ p∈P, (if v∈p.biUnion X then F p else 0) ≤ ∑ p∈P, ∑ j, if j∈p ∧ v∈ X j then F p else 0 := by
            apply sum_le_sum; intro k hk; split
            · rename_i hf; obtain ⟨j,hg,hp⟩:= mem_biUnion.mp hf
              apply le_trans _ (single_le_sum (f:=fun j=> if j∈k ∧ v∈ X j then F k else 0) (fun _ _ => by split; exact honey_pos X b M a h _; exact le_rfl) (mem_univ j)); rw [if_pos ⟨hg,hp⟩]
            exact sum_nonneg fun j _=> by split; exact honey_pos X b M a h _; exact le_rfl
          apply hx.trans; rw [sum_comm]; apply le_trans _ (le_trans (a:=∑ j,if v∈X j then g j else 0) (tsum_fintype ..).ge (H v|>.2.2))
          apply sum_le_sum; intro j _; by_cases he : v∈X j
          · simp_rw [he,and_true,if_true]
            rw [← sum_filter]; have hh : P.filter (fun p=>j∈p)⊆hailst (s.erase i) j:=fun k hk=> mem_filter.mpr ⟨(mem_sdiff.mp (mem_filter.mp hk).1).1,(mem_filter.mp hk).2⟩
            exact (sum_le_sum_of_subset_of_nonneg hh (fun k _ _=> honey_pos X b M a h _)).trans (ih _ (erase_ssubset hz) _)
          simp [he]
        _ ≤ _ := by
          have hi:( (X i).card:ℝ) ≤ coverNumber M (X i) * ((M+M+1:ℕ):ℝ)^4:= by exact_mod_cast Corona.pays (X i) M
          apply (mul_le_mul_of_nonneg_right hi hh).trans; rw [mul_assoc];exact mul_le_of_le_one_right (by positivity) he
    apply (any_root X b M a s h).trans
    apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ht) (alarm_pos X b M a h _))
    unfold alarm; rw [add_mul,one_mul,Real.exp_add,mul_assoc]
  rw [show hailst s i=∅ from ?_,sum_empty]; exact alarm_pos X b _ _ h _
  apply eq_empty_iff_forall_notMem.mpr; intro j hj; exact hz (mem_powerset.mp (mem_filter.mp hj).1 (mem_filter.mp hj).2)

lemma flattened (P : BudgetPoint) (X : V → Support n) (s : Finset V) (f : V→ℝ) (h : ∀ i,0 ≤ f i) (ha : 0≤a) :
    ‖majesty X s‖ * (∏ i∈s,f i) * Value.charge P a (s.biUnion X) ≤ honey X f P.B a s:= by
  by_cases he: majesty X s=0
  · simp [honey,he]
  unfold honey alarm; rw [prod_mul_distrib,←Real.exp_sum,← sum_boost']
  unfold Value.charge; rw [← Finset.mul_sum]; gcongr
  · exact mul_nonneg (norm_nonneg _) (prod_nonneg fun i _=> h i)
  exact_mod_cast cover X P.B (majesty_spark X he)
where
  sum_boost' (u v w : ℝ): u*v*w=u*(v*w):= mul_assoc ..
end YM.Next.Rank.Flux
