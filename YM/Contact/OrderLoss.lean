import YM.Contact.Order
import YM.Euclid.Differential

/-! Finite derivative costs for the ordinary (integer degree, real multivariate) Taylor
subtraction before introducing annular splittings. Exponents here are independent of any
perturbative-order index. -/

noncomputable section
set_option autoImplicit false
open Set Function Filter ContinuousLinearMap
open scoped Topology BigOperators ContDiff
namespace YM.Contacts
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
lemma polynomial_smooth (m:ℕ)(φ:E→ℂ)(x:E):ContDiff ℝ ⊤ (polynomial m φ x):=ContDiff.sum fun _ _=>jet_smooth ..
lemma jet_t_pow (j:ℕ)(φ:E→ℂ)(x y : E)(t:ℝ) : jet j φ x (x+t • y) = (t^j) • jet j φ x (x+y):=by
   simp only [jet,add_sub_cancel_left,ContinuousMultilinearMap.map_smul_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin];rw [smul_comm]
private lemma along_ray (φ:E→ℂ) (x v:E)(i:ℕ) (hf:ContDiff ℝ i φ):
    iteratedDeriv i (fun t:ℝ=> φ (x+t • v)) 0 =  Tensor.diagonal (iteratedFDeriv ℝ i φ x) v :=by
  let f(y:E):=φ (x+y); let L:ℝ→L[ℝ] E:= (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hl:ContDiff ℝ i f:= hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]; change iteratedFDeriv ℝ i (f∘⇑L) 0 _ = _
  rw [L.iteratedFDeriv_comp_right hl 0 (le_refl _),show iteratedFDeriv ℝ i f (L 0)=_ from iteratedFDeriv_comp_add_left ..,map_zero,add_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; congr 1;ext1 j; change (1:ℝ) • v= v; exact one_smul ..

lemma flat_of_sub (m j : ℕ) (φ:E→ℂ)(hf:ContDiff ℝ ∞ φ)(x:E)(hj:j ≤ m):
   iteratedFDeriv ℝ j (fun y=> φ y-polynomial m φ x y) x=0:=by
  let f(y):= φ y - polynomial m φ x y
  have hz:ContDiff ℝ ∞ f:= hf.sub ((polynomial_smooth ..).of_le le_top)
  refine Tensor.ext_diag _ _ (Analysis.sym_Jet (hz.of_le (WithTop.coe_le_coe.mpr (show (j:ℕ∞)≤⊤ from le_top))|>.contDiffAt)) (fun _ _=>rfl) (funext fun v=>?_) -- field local
  change Tensor.diagonal (iteratedFDeriv ℝ j f x) v=(0: YM.Tensor.T E ℂ j) (fun _=>v)
  rw [← along_ray f x v j]
  · change iteratedDeriv j (fun t:ℝ=> φ (x+t•v)-_) 0=0
    let g(t:ℝ):=x+t • v; have hg: ContDiff ℝ ∞ g:=contDiff_const.add (contDiff_id.smul_const ..)
    -- Taylor along a ray polynomial
    rw [show (fun t:ℝ=> φ (x+t•v)-polynomial m φ x (x+t • v))=(fun t=>φ (g t))- (∑ i∈Finset.range (m+1),(fun t:ℝ=>(t^i) • jet i φ x (x+v))) from funext (fun t=>by change _ = _ - (∑ i∈Finset.range (m+1),fun t:ℝ=>t^i • jet i φ x (x+v)) t; rw [Finset.sum_apply]; change _ - ∑ i∈_, jet .. = _ - _;simp_rw [jet_t_pow];rfl),
       iteratedDeriv_sub (f:=fun t=>φ (g t)) (n:=j) ((hf.comp hg).of_le (WithTop.coe_le_coe.mpr (show (j:ℕ∞)≤⊤ from le_top))|>.contDiffAt) ?_,sub_eq_zero]
    · have hb(i): iteratedDeriv j (fun t:ℝ=>t^i • jet i φ x (x+v)) 0=if j=i then (j.factorial:ℝ) • jet j φ x (x+v) else 0:=by
         rw [iteratedDeriv_smul_const ((contDiffAt_id.pow _).of_le le_top), iteratedDeriv_pow]; by_cases ht:j=i
         · subst i; rw [tsub_self,pow_zero,mul_one,if_pos rfl,Nat.descFactorial_self]
         rw [if_neg ht]; rcases lt_or_gt_of_ne ht with hv|hv
         · rw [zero_pow (Nat.sub_ne_zero_iff_lt.mpr hv),mul_zero,zero_smul]
         rw [Nat.descFactorial_of_lt hv,Nat.cast_zero,zero_mul,zero_smul]
      rw [iteratedDeriv_sum (fun i _=>(contDiffAt_id.pow ..).smul contDiffAt_const)]; simp_rw [hb]; rw [Finset.sum_eq_single_of_mem j (Finset.mem_range_succ_iff.mpr hj) (fun i _ hi=>by rw [if_neg (Ne.symm hi)]),if_pos rfl]
      change iteratedDeriv j (fun t:ℝ=>φ (x+t • v)) 0=(j.factorial:ℝ) • _
      rw [along_ray φ x v j (hf.of_le (WithTop.coe_le_coe.mpr (show (j:ℕ∞)≤⊤ from le_top))), jet, add_sub_cancel_left,← mul_smul, mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos j|>.ne')),one_smul]; rfl
    · rw [show (∑ i∈Finset.range (m+1),_)= (fun t:ℝ=>∑ i∈Finset.range (m+1), t^i • jet i φ x (x+v)) from funext fun t:ℝ=>Finset.sum_apply ..]
      exact (ContDiff.sum (n:=⊤) (𝕜:=ℝ) (f:=fun i t=> (t:ℝ)^i • jet i φ x (x+v)) (s:=Finset.range (m+1)) (fun _ _=> contDiff_id.pow ..|>.smul contDiff_const)).of_le le_top|>.contDiffAt
  exact hz.of_le (WithTop.coe_le_coe.mpr le_top)

/-- Taylor jet zero at the origin plus a bound on highest derivative gives all the weighted
lower bounds *on the entire segment* of approach. -/
theorem norm_deriv_from_zero (j l:ℕ){f:E→F} (hf:ContDiff ℝ (↑(j+l+1:ℕ)) f)
       (ht:∀ i ≤ j,iteratedFDeriv ℝ (l+i) f 0=0){x:E}{B:ℝ}(hb:0≤B)
       (h:∀ y,‖y‖≤‖x‖ → ‖iteratedFDeriv ℝ (j+l+1) f y‖≤ B) :
       ‖iteratedFDeriv ℝ l f x‖ ≤ ‖x‖^(j+1)*B:=by
  have he:∀ i:ℕ,i≤j→∀ y:E,‖y‖≤‖x‖ → ‖iteratedFDeriv ℝ (l+j-i) f y‖ ≤ ‖x‖^(i+1)*B:=by
    intro i hi; induction i with
    | zero=>
       intro y hy; rw [Nat.sub_zero,pow_one]
       have hz:= convex_closedBall (E:=E) (0:E) ‖x‖ |>.norm_image_sub_le_of_norm_fderiv_le
                (f:=iteratedFDeriv ℝ (l+j) f) (C:=B) (x:=0) (y:=y)
                (fun y _=> hf.differentiable_iteratedFDeriv (mod_cast (by omega : l+j<j+l+1)) y)
                (fun z hz=> norm_fderiv_iteratedFDeriv (f:=f)|>.trans_le (by rw [Nat.add_comm l]; exact h z (mem_closedBall_zero_iff.mp hz)))
                (by simp) (mem_closedBall_zero_iff.mpr hy)
       rw [ht _ le_rfl,sub_zero,sub_zero] at hz; exact hz.trans ((mul_le_mul_of_nonneg_left hy hb).trans_eq (mul_comm ..))
    | succ i ih=>
       intro y hy; have hzi:i+1≤j:=hi; have hq:= ht (j-(i+1)) (by omega); rw [← Nat.add_sub_assoc hzi] at hq
       have hz:= convex_closedBall (E:=E) (0:E) ‖x‖ |>.norm_image_sub_le_of_norm_fderiv_le
                (f:=iteratedFDeriv ℝ (l+j-(i+1)) f) (C:=‖x‖^(i+1)*B) (x:=0) (y:=y)
                (fun y _=> hf.differentiable_iteratedFDeriv (mod_cast (by omega : l+j-(i+1)<j+l+1)) y)
                (fun z hz=> norm_fderiv_iteratedFDeriv (f:=f)|>.trans_le (by rw [show l+j-(i+1)+1=l+j-i by omega];exact ih (by omega) z (mem_closedBall_zero_iff.mp hz)))
                (by simp) (mem_closedBall_zero_iff.mpr hy)
       rw [hq,sub_zero,sub_zero] at hz; apply hz.trans ((mul_le_mul_of_nonneg_left hy (mul_nonneg (pow_nonneg (norm_nonneg _) _) hb)).trans_eq (by rw [pow_succ (‖x‖)]; ring))
  have hg:=he j le_rfl x le_rfl; rw [show l+j-j=l by omega] at hg; exact hg

-- Linear map from the top derivative at the center into any local derivative of a Taylor term.
def diagMap (j:ℕ)(a:E)(v:Tensor.T E ℂ j)(x:E):= ((j.factorial:ℝ)⁻¹ :ℝ) • v (fun _=>x-a)
lemma diagMap_smooth (j:ℕ)(a:E)(v:Tensor.T E ℂ j): ContDiff ℝ ⊤ (diagMap _ a v):=
  (contDiff_const (c:=(j.factorial:ℝ)⁻¹)).smul (ContinuousMultilinearMap.contDiff v |>.comp (contDiff_pi.mpr (fun _=> contDiff_id.sub (contDiff_const (c:=a)))))
def termOperator (i j:ℕ)(a:E)(x:E): Tensor.T E ℂ j →ₗ[ℝ] Tensor.T E ℂ i where
  toFun v:=iteratedFDeriv ℝ i (diagMap j a v) x
  map_add' f g:=by rw [show diagMap j a (f+g)=diagMap j a f+diagMap j a g from funext fun y=>smul_add _ (f (fun _=> y-a)) (g (fun _=> y-a)),iteratedFDeriv_add ((diagMap_smooth ..)|>.of_le le_top) ((diagMap_smooth ..)|>.of_le le_top),Pi.add_apply] -- exact transparent?
  map_smul' c f:=by rw [show diagMap j a (c • f)= c • (diagMap j a f) from funext fun y=> smul_comm _ c (f fun _=> y-a),iteratedFDeriv_const_smul_apply ((diagMap_smooth ..).of_le le_top|>.contDiffAt)]; rfl

lemma poly_deriv_bound [FiniteDimensional ℝ E] (k j:ℕ)(R:ℝ):∃ C≥0,∀ {φ:E→ℂ}{B}, (∀ i≤j, ‖iteratedFDeriv ℝ i φ 0‖≤B) →∀ l≤k,∀ x:E,‖x‖≤R→
     ‖iteratedFDeriv ℝ l (polynomial j φ 0) x‖ ≤ C*B:=by
  classical
  let ι(i:ℕ):=Module.Free.ChooseBasisIndex ℝ (Tensor.T E ℂ i); letI (i:ℕ):Fintype (ι i):= inferInstanceAs (Fintype (Module.Free.ChooseBasisIndex ..))
  let b (i:ℕ): Module.Basis (ι i) ℝ _:=Module.Free.chooseBasis ℝ (Tensor.T E ℂ i)
  let w (i:ℕ)(p:ι i):ℝ:=‖LinearMap.toContinuousLinearMap ((b i).coord p)‖
  let K:= Metric.closedBall (0:E) R; have hf:= isCompact_closedBall (0:E) R
  choose f₀ h₀ using (show ∀ i l (t:ι i),∃ D:ℝ,∀ x∈K, ‖iteratedFDeriv ℝ (l:ℕ) (diagMap i 0 (b i t)) x‖≤ D from fun i l t =>
    let ht:= hf.bddAbove_image (f:= fun x=> ‖iteratedFDeriv ℝ (l:ℕ) (diagMap i 0 (b i t)) x‖) ((diagMap_smooth ..).continuous_iteratedFDeriv le_top|>.norm.continuousOn)
    ⟨ht.choose,fun x hx=>ht.choose_spec (Set.mem_image_of_mem _ hx)⟩)
  let f(i l:ℕ)(p:ι i):= max 1 (f₀ i l p)
  let c(φ:E→ℂ)(i:ℕ)(p:ι i):=(b i).coord p (iteratedFDeriv ℝ i φ 0)
  let g(l i:ℕ)(p:ι i)(x:E):=termOperator l i (0:E) x (b i p)
  have hl l i x (φ):iteratedFDeriv ℝ l (jet i φ 0) x= ∑ p,c φ i p • g l i p x:=by
     change termOperator l i _ _ _=_
     have ht(v:Tensor.T E ℂ i):v=∑ p:ι i,(b i).coord p v • b i p:= ((b i).sum_repr v).symm
     conv_lhs=> rw [ht (iteratedFDeriv ℝ i φ 0), map_sum]; simp only [map_smul]
  let cost(l:ℕ):= ∑ i∈Finset.range (j+1),∑ p:ι i,w i p*f i l p
  have hm(l):0≤cost l:= Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun p _=> mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap ((b i).coord p))) (le_trans zero_le_one (le_max_left ..))
  refine ⟨∑ l∈Finset.range (k+1),cost l,Finset.sum_nonneg (fun l _=> hm l),fun {φ B} H l hl' x hx=>?_⟩
  have hB:0≤B:= (norm_nonneg _).trans (H _ (Nat.zero_le _))
  have he i (hi:i∈Finset.range (j+1)): ‖iteratedFDeriv ℝ l (jet i φ 0) x‖ ≤ (∑ p:ι i,w i p*f i l p) * B:=by
    rw [hl,Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum (fun p _=>?_))
    have hV : ‖c φ i p‖≤w i p * B:= ((LinearMap.toContinuousLinearMap ((b i).coord p)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (H _ (Finset.mem_range_succ_iff.mp hi)) (norm_nonneg _))
    rw [norm_smul]; calc
     _ ≤ (w i p*B) * ‖g l i p x‖:= mul_le_mul_of_nonneg_right hV (norm_nonneg (g l i p x))
     _ ≤ (w i p*B)*f i l p:= mul_le_mul_of_nonneg_left ((h₀ i l p x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_right ..)) (mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap ((b i).coord p))) hB)
     _ = _:=by ring
  rw [show polynomial j φ (0:E) = (fun y=>∑ i∈Finset.range (j+1), jet i φ 0 y) from rfl, iteratedFDeriv_sum (f:=fun i (y:E)=>jet i φ 0 y) (u:=Finset.range (j+1)) (h:=fun i _=>(jet_smooth ..|>.of_le le_top)),Finset.sum_apply]
  calc ‖_‖ ≤ cost l * B := (norm_sum_le ..).trans ((Finset.sum_le_sum he).trans_eq (Finset.sum_mul ..).symm)
       _ ≤ _:= mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun l _=>hm l) (Finset.mem_range_succ_iff.mpr hl')) hB
end YM.Contacts
