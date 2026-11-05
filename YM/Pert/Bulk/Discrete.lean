import YM.Pert.Bulk.Coin

/-! Fine translation losses for the same-rank affine-null curvature packet, relative to the first face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function Precision
open scoped ENNReal Topology Classical BigOperators
variable {L:Side}

lemma hop (x z : Cover) (h:0<Laurent.size (z-x)) : ∃ w d, Laurent.size (w-x)+1≤Laurent.size (z-x) ∧ (z=w+step d ∨ w=z+step d) := by
  obtain ⟨i,hi⟩ : ∃ i,z i≠x i := by contrapose! h; have he := funext h; rw [he,sub_self,Laurent.size]; simp
  obtain hi|hi:= hi.lt_or_gt
  · refine ⟨z+step i,i,?_ ,Or.inr rfl⟩
    suffices Laurent.size (z+step i-x)<Laurent.size (z-x) by omega
    unfold Laurent.size; refine Finset.sum_lt_sum (fun j _=> ?_) ⟨i,Finset.mem_univ _,?_⟩
    · by_cases hj : j=i; · subst hj; specialize hi; simp; omega
      simp [hj]
    simp; omega
  · refine ⟨z-step i,i,?_ ,Or.inl (sub_add_cancel ..).symm⟩
    suffices Laurent.size (z-step i-x)<Laurent.size (z-x) by omega
    unfold Laurent.size; refine Finset.sum_lt_sum (fun j _=> ?_) ⟨i,Finset.mem_univ _,?_⟩
    · by_cases hj : j=i; · subst hj; specialize hi; simp; omega
      simp [hj]
    simp; omega
lemma sep_zero_eq {x y : Cover} (h:Laurent.size (y-x)=0) : y=x := by
  ext i
  have hy : ((y-x) i).natAbs ≤ 0 := le_trans (Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>((y-x) i).natAbs) (by simp) (Finset.mem_univ i)) h.le
  replace hy := Int.natAbs_eq_zero.mp (le_antisymm hy (Nat.zero_le _))
  exact sub_eq_zero.mp hy

def diffScale (L:Side) (m:ℕ) (σ C : ℝ) (x z:Cover) := Real.exp (σ*(sep z x/(L.val:ℝ))) * (C/(L.val:ℝ)^(m+1))
lemma diffScale_nonneg {σ C:ℝ} {d:ℕ}(x z : Cover) (h:0≤C):0≤ diffScale L d σ C x z:=by unfold diffScale; positivity
lemma diffScale_mono {σ C:ℝ}{d:ℕ}{x w z:Cover} (h:sep w x≤sep z x) (hσ:0≤σ)(hC:0≤C): diffScale L d σ C x w≤diffScale L d σ C x z := by unfold diffScale; gcongr

variable {α β : Type}
lemma step_far {σ p : ℝ} {T: Kernel α β} {m : ℕ} (h: Atlas σ L m T p)
       (i j k) (v x z : Cover) (hL : sep v x ≤ sep z x) : ∑' y,bill (foot k T (v,i) (y,j)) (σ*delta L x y) ≤ ENNReal.ofReal (diffScale L m σ p x z) := by
  have hs y := (delta_fine L x v y)
  have hg y : σ * delta L x y ≤ σ * delta L v y + σ * sep z x / (L.val:ℝ) := by
    have hσ := h.width
    calc _ ≤ σ*(sep x v / L.val + delta L v y) := mul_le_mul_of_nonneg_left (hs y) hσ
         _ ≤ σ*(sep z x / L.val + delta L v y) := by rw [sep_comm x v]; gcongr
         _ = _ := by ring
  calc _ ≤ ∑' y,bill (foot k T (v,i) (y,j)) (σ*delta L v y + σ*sep z x/(L.val:ℝ)) := ENNReal.tsum_le_tsum (fun y=>bill_mono le_rfl (hg y))
       _ = ENNReal.ofReal (Real.exp (σ*sep z x/(L.val:ℝ))) * ∑' y,bill (foot k T (v,i) (y,j)) (σ*delta L v y) := by simp_rw [bill_add,ENNReal.tsum_mul_right, mul_comm]
       _ ≤ _ := by rw [diffScale,ENNReal.ofReal_mul (by positivity:0≤Real.exp (σ*(sep z x/(L.val:ℝ)))), mul_div_assoc]; exact mul_le_mul_right (h.step k (v,i) j) _

lemma atlas_difference {σ p : ℝ} {T: Kernel α β} {d : ℕ} (h: Atlas σ L d T p) (i:α) (j:β) (x z:Cover):
  ∑' y, bill (T (z,i) (y,j)-T (x,i) (y,j)) (σ*delta L x y) ≤ ENNReal.ofReal (Laurent.size (z-x)*diffScale L d σ p x z):=by
   have H (n:ℕ)(z:Cover) (hz:Laurent.size (z-x)=n): ∑' y, bill (T (z,i) (y,j)-T (x,i) (y,j)) (σ*delta L x y) ≤ ENNReal.ofReal (n*diffScale L d σ p x z) := by
     induction n using Nat.strongRecOn generalizing z with
     | ind n ih =>
       subst n
       rcases eq_zero_or_pos (Laurent.size (z-x)) with hl | hz
       · have he := sep_zero_eq hl; subst z
         simp [bill]
       obtain ⟨w,k,ha,hk⟩ := hop x z hz
       let m := Laurent.size (w-x); let n := Laurent.size (z-x); let c := diffScale L d σ p x z
       have hL : sep w x≤sep z x := by unfold sep;exact_mod_cast (Nat.le_trans (Nat.le_add_right _ _) ha)
       have hw := ih m (Nat.lt_of_succ_le ha) w rfl
       have hs' := diffScale_nonneg (L:=L) (σ:=σ) x w (d:=d) h.nonneg
       have he' := diffScale_nonneg (L:=L) (σ:=σ) x z (d:=d) h.nonneg
       calc _ ≤ ∑' y,(bill (T (w,i) (y,j)-T (x,i) (y,j)) (σ*delta L x y) + bill (T (z,i) (y,j)-T (w,i) (y,j)) (σ*delta L x y)) := by
                apply ENNReal.tsum_le_tsum; intro y
                convert bill_sub (T (w,i) (y,j)-T (x,i) (y,j)) (T (w,i) (y,j)-T (z,i) (y,j)) (σ*delta L x y) using 1
                · abel
                unfold bill; rw [abs_sub_comm (T (z,i) ..)]
            _ ≤ ENNReal.ofReal (m*diffScale L d σ p x w+c) := by
                rw [ENNReal.tsum_add,ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hs') he']
                apply add_le_add (show _ ≤ ENNReal.ofReal (m*diffScale L d σ p x w) from hw)
                rcases hk with hz|hz
                · simpa only [foot,← hz] using step_far h i j k w x z hL
                exact le_trans (tsum_congr (f:=fun y=>bill (T (z,i) (y,j)-T (w,i) (y,j)) (σ*delta L x y)) (g:=fun y=>bill (foot k T (z,i) (y,j)) (σ*delta L x y)) (fun y=>by rw [bill,foot,bill,abs_sub_comm,hz])).le (step_far h i j k z x z (le_refl _))
            _ ≤ _ := by
                apply ENNReal.ofReal_le_ofReal
                trans (m+1 :ℝ)*c
                · rw [add_mul,one_mul]; gcongr; exact diffScale_mono hL h.width h.nonneg
                gcongr; exact_mod_cast ha
   exact H _ z rfl
end YM.Pert.Bulk
