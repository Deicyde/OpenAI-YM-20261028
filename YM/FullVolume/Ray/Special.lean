import YM.FullVolume.Ray.Glimpse
/-! Scout exponential of a small germ.
 Lean budget kept as *Weigh* with pointwise normalized d.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Finset
open scoped Topology BigOperators NNReal ContDiff
variable {E: Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {v a b p:ℝ} {k i n:ℕ} {f:ℝ→ E→ℝ} {x:E}
-- dimension free (stage constants). Keep power of b on derivatives but not repeated powers of a if a≤1. need one small amplitude
lemma imprint (n:ℕ) : ∃ C:ℝ,0<C ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (p a b:ℝ) (f:ℝ→E→ℝ), a≤1 → Weigh n x p a b f →
    Weigh n x p (C*a) b (fun i x=> Real.exp (f i x)-1):=by
  induction n with
  | zero=> refine ⟨2,by norm_num,?_⟩; intro E _ _ x p a b f ha hf
           refine ⟨hf.slope,fun i hi=> (hf.smooth i hi).exp.sub contDiffAt_const,fun u hu j hj=>?_⟩; obtain rfl:j=0:=by omega
           have he:=hf.probes u hu _ hj; simp only [marked,iteratedDeriv_zero,pow_zero,mul_one] at he ⊢
           exact he.burn.enlarged ((le_abs_self _).trans ((Real.abs_exp_sub_one_le (show |a|≤1 by rw [abs_of_nonneg hf.nonneg]; exact ha)).trans (by rw [abs_of_nonneg hf.nonneg])))
  | succ n ih=>
    obtain ⟨C,hC,h⟩:= ih; let d i:= ((n.choose i:ℝ)*(C+1)); let B:=∑ i ∈ range (n+1),d i
    have hp : 0≤ B:=sum_nonneg fun _ _=> by unfold d; positivity
    refine ⟨C+B,add_pos_of_pos_of_nonneg hC hp,?_⟩; intro E _ _ x p a b f ha hf
    let g i:= Real.exp ∘ f i
    have hc:= h _ x p a b f ha ⟨hf.slope,fun i hi=> (hf.smooth i hi).of_le (Nat.cast_le.mpr (Nat.le_succ _)),fun u hu j hj=> hf.probes u hu j (hj.trans (Nat.le_succ _))⟩
    have hh := hf.nonneg; let z i j u:= marked j (g i) x u
    have hF (i:ℝ) (hi:i∈sun): ContDiffAt ℝ (↑(n+1)) (g i) x:= (hf.smooth i hi).exp
    let J:ℕ:=n+1; have hb:=hf.slope
    have hK (i:ℝ) (ht:i∈sun) (u:E) (j:ℕ) (hj:j≤n+1) (ho : j≠0): z i j u= marked j (fun v=>g i v -1) x u:=by
      symm; unfold marked; rw [show ((fun v=>g i v-1) ∘ tintM x u)=(fun s=>g i (tintM x u s)-1) from rfl]
      exact (iteratedDeriv_fun_sub (sheen ((hF _ (by assumption)).of_le (Nat.cast_le.mpr hj)) u) contDiffAt_const).trans (by rw [iteratedDeriv_const,if_neg ho,sub_zero]; rfl)
    refine ⟨hf.slope,fun i hi=> (hf.smooth i hi).exp.sub contDiffAt_const, fun u hu j hj=>?_⟩
    rcases eq_or_lt_of_le hj with hj|hz; swap
    · refine (hc.probes u hu _ (by omega)).enlarged (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hp) hh) (pow_nonneg hb _))
    subst j
    have hz (i:ℕ) (hi:i≤n) : Scout p (fun t=> z t i u) ((C*a+1)*b^i):= by
      have he:= hc.probes u hu i hi
      rcases eq_or_ne i 0 with rfl|h'
      · have hg (t): z t 0 u= marked 0 (fun y=> Real.exp (f t y)-1) x u+(fun _:ℝ=> (1:ℝ)) t:= by unfold marked z g; simp [marked]
        simp_rw [hg]; have ht':= he.pair (Scout.still he.ray (1:ℝ)); simp only [norm_one,pow_zero,mul_one] at *; exact ht'
      exact ((he.enlarged (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num: (0:ℝ)≤1)) (pow_nonneg hb i)))).replace (fun t ht=> (hK _ ht _ _ (by omega) h').symm)
    let v i t:= (n.choose i:ℝ)*z t i u*marked (n-i+1) (f t) x u; let S:= range (n+1)
    have hv (i) (hi:i∈S): Scout p (v i) ((d i)*a*b^J):=by
      have hi := mem_range.mp hi
      have hp: i≤n:= by omega
      let k:= n-i+1; have hk:k≤J:=by unfold k J; omega
      refine (((hz i hp).scale (n.choose i:ℝ)).multiplies (hf.probes _ hu k hk)).enlarged ?_
      rw [Real.norm_natCast]; unfold d; calc
        _ ≤ (↑(n.choose i)*( (C+1)*b^i))*(a*b^k):= by gcongr; apply mul_le_of_le_one_right hC.le ha
        _ = _ := by rw [show J=i+k from (by unfold J k; omega),pow_add]; ring
    refine ((Scout.pieces S v _ hf.ray hv).enlarged ?_).replace (fun i hi=>?_)
    · change ∑ i∈S,d i*a*b^J≤_
      rw [← sum_mul,← sum_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hh) (pow_nonneg hb _)
    suffices he : ∑ j∈S,v j i=z i (n+1) u by exact he.trans (hK i hi u _ (by omega) (by omega))
    exact (spiral (sheen (hf.smooth i hi) u)).symm
end YM.FullVolume.Ray
