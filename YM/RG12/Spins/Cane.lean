import YM.RG12.Spins.Linette
import YM.Next.STATIONARY.Joint.Completion
/-! D2 payment where first outer derivative kills by design.Norm Hessian comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Metric Real YM.AnalyticBridge.SectorAffine.Offset Matrix
open scoped ContDiff Topology
variable {E F K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup K][NormedSpace ℝ K]
variable {C B R t r M:ℝ}
lemma pair_price (f:E→F)(H:K→E)(h:ContDiffAt ℝ 2 f 0)(he:fderiv ℝ f 0=0)(hT:ContDiffAt ℝ 2 H 0)(hk:H 0=0)(a b:K):
    iteratedFDeriv ℝ 2 (f ∘ H) 0 ![a,b]=iteratedFDeriv ℝ 2 f 0 ![fderiv ℝ H 0 a,fderiv ℝ H 0 b] :=by
  simp_rw [iteratedFDeriv_two_apply,cons_val_zero,cons_val_one]
  let g:=fderiv ℝ f ∘ H; let V:=fderiv ℝ H
  have hz:ContDiffAt ℝ 2 f (H 0):=hk ▸ h
  have hp: fderiv ℝ (f∘H) =ᶠ[𝓝 0] fun y=> (g y).comp (V y):=by
    filter_upwards [hT.continuousAt.tendsto.eventually (hz.eventually (by norm_num)),hT.eventually (by norm_num)] with y hv hw; exact fderiv_comp _ (hv.differentiableAt (by norm_num)) (hw.differentiableAt (by norm_num)) --
  have hv:=(hz.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  have he':=(hT.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  rw [hp.fderiv_eq,fderiv_clm_comp (c:=g) (d:=V) (hv.comp _ (hT.differentiableAt (by norm_num))) he',show fderiv ℝ g 0= _ from fderiv_comp 0 hv (hT.differentiableAt (by norm_num))]; change g 0 _ + fderiv ℝ (fderiv ℝ f) (H 0) _ _= _; unfold g; rw [Function.comp_apply, hk,he,_root_.zero_apply,zero_add]; rfl

lemma torque (f:E→F)(U V:E)(W Z:E)(X K A:ℝ)(hb:‖iteratedFDeriv ℝ 2 f 0‖ ≤ X)(hU:‖U‖≤K)(hZ:‖Z‖≤K)(h:‖U-W‖ ≤ A)(he:‖V-Z‖ ≤ A):
    ‖iteratedFDeriv ℝ 2 f 0 ![U,V] - iteratedFDeriv ℝ 2 f 0 ![W,Z]‖ ≤ 2*X*K*A :=by
  let F:= iteratedFDeriv ℝ 2 f 0
  let S:= fderiv ℝ (fderiv ℝ f) 0
  have H(x y:E):F ![x,y]= S x y:=by simp [F,S,iteratedFDeriv_two_apply]
  have hx := (norm_nonneg _).trans hb; have hh:0≤K:=(norm_nonneg _).trans hU; have ha:0≤A:=(norm_nonneg _).trans h
  change ‖F _ - F _‖ ≤ _; rw [show F ![U,V] - F ![W,Z] = S U (V-Z)+ S (U-W) Z from (by rw [_root_.map_sub,_root_.map_sub,_root_.sub_apply,H,H]; abel)]
  have hp(x y:E):‖S x y‖ ≤ X*‖x‖*‖y‖:=by
     rw [← H]; apply (ContinuousMultilinearMap.le_opNorm ..).trans; simp only [Fin.prod_univ_succ,cons_val_zero,cons_val_succ,Fin.prod_univ_zero,Fin.isValue, mul_one]; rw [mul_assoc]; gcongr
  apply (norm_add_le ..).trans
  calc
   _ ≤  X*K*A+X*A*K:= add_le_add ((hp ..).trans (mul_le_mul (mul_le_mul_of_nonneg_left hU hx) he (norm_nonneg _) (mul_nonneg hx hh))) ((hp ..).trans (mul_le_mul (mul_le_mul_of_nonneg_left h hx) hZ (norm_nonneg _) (mul_nonneg hx ha)))
   _=_:=by ring
end YM.RG12.Spins
