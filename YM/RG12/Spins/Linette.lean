import YM.RG12.Spins.Louis
import YM.Planned.ATOM_REGULAR_ESTIMATE.Faa
/-! Sample sym odd/even at a smooth argument. U built from launch; positive
-order pricing must retain a threshold per derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Metric YM.AnalyticBridge.SectorAffine.Offset Finset
open scoped ContDiff
variable {E F K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup K][NormedSpace ℝ K]
variable {C B R t r M:ℝ}
-- bound through mixed U jet
lemma drift_skin {f:E→F}{n j:ℕ}(hj:j+2 ≤ n)(h:∀ x,‖x‖ ≤ R→Through n f x C){y:E}(hy:‖y‖ ≤ R)
   (H:K→E)(hs:ContDiffAt ℝ j H 0) (hH:H 0=0)(ht:0 ≤ t)(hM:1 ≤ M)(hb:∀ i:ℕ,1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i H 0‖  ≤  M*t^i)
   (v:Fin j → K)(hv:∀ i,‖v i‖ ≤ 1):
    let S (b:E):= f ∘ (fun i=> H i+b)
    let V(s):=iteratedFDeriv ℝ j s 0 v
    ‖V (S y)+ V (S (-y))-(2:ℝ) • V (S 0)‖  ≤  2*C*(Fintype.card (OrderedFinpartition j):ℝ)*M^j*‖y‖^2*t^j := by
   intro S V
   let T (b:E): K→E:= fun i=>H i + b
   let L (c: OrderedFinpartition j)(i:Fin c.length):E:=iteratedFDeriv ℝ (c.partSize i) H 0 (v ∘ c.emb i)
   have hT(b:E)(hb':‖b‖ ≤ R): V (S b)=∑ c : OrderedFinpartition j,iteratedFDeriv ℝ c.length f b (L c):=by
      have he : ContDiffAt ℝ j f (T b 0) :=by simpa only [T,hH,zero_add] using! (h b hb').smooth.of_le (m:=(j:ℕ∞ω)) (Nat.cast_le.mpr (Nat.le_trans (Nat.le_add_right ..) hj))
      unfold V S; rw [iteratedFDeriv_comp (g:=f) (f:=T b) he (hs.add contDiffAt_const) (n:=(j:ℕ∞ω)) le_rfl,FormalMultilinearSeries.taylorComp, _root_.sum_apply]; apply Finset.sum_congr rfl
      intro c _; change iteratedFDeriv ℝ c.length f (H 0 + b) (fun i=> iteratedFDeriv ℝ (c.partSize i) (H+(fun _:K=>b)) 0 (v ∘ c.emb i))=_
      rw [hH,zero_add]; apply congr_arg; ext1 i
      rw [iteratedFDeriv_add_apply (hs.of_le (Nat.cast_le.mpr (c.partSize_le i))) contDiffAt_const,iteratedFDeriv_const_of_ne (Nat.ne_zero_of_lt (c.partSize_pos i))]; simp only [Pi.zero_apply,add_zero] -- err
      rfl
   have h0:0 ≤ R:=(norm_nonneg _).trans hy; rw [hT y hy,hT (-y) (norm_neg y ▸ hy), hT 0 (by simpa), ← Finset.sum_add_distrib,Finset.smul_sum,←Finset.sum_sub_distrib]
   let K₀:=2*C*M^j*‖y‖^2*t^j
   apply (norm_sum_le ..).trans; calc
    (∑ i:OrderedFinpartition j, _) ≤  ∑ i:OrderedFinpartition j,K₀:=Finset.sum_le_sum fun a _=>?_
    _ = _:=by simp [K₀]; ring
   let z:=(iteratedFDeriv ℝ a.length f y + iteratedFDeriv ℝ a.length f (-y) - (2:ℝ) • iteratedFDeriv ℝ a.length f 0)
   change ‖z (L a)‖  ≤  K₀
   have hB : ‖z‖ ≤  _:= drift (j:=a.length) (Nat.le_trans (Nat.add_le_add_right a.length_le 2) hj) h hy
   have he(i):‖L a i‖ ≤  M*t^a.partSize i:= by simpa using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hb (a.partSize i) (a.partSize_pos i) (a.partSize_le i)) (show ∀ k,‖(v ∘ a.emb i) k‖ ≤ 1 from fun _=> hv _)
   calc
    _  ≤  (2*C*‖y‖^2)*∏i:Fin a.length,(M*t^a.partSize i):= (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul hB (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>he _)) (Finset.prod_nonneg fun _ _=>norm_nonneg _) (by positivity [h y hy |>.nonneg]))
    _ = (2*C*‖y‖^2)*(M^a.length*t^j):=by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Finset.prod_pow_eq_pow_sum,show ∑ i, a.partSize i = j by simpa using (a.sum_sigma_eq_sum (fun (_:Fin j)=>(1:ℕ)))]; simp
    _  ≤  K₀:= by unfold K₀; have hC:=(h y hy).nonneg; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM a.length_le) (by positivity)) (by positivity)).trans_eq (by ring)
end YM.RG12.Spins
