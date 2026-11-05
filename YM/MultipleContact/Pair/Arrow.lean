import YM.MultipleContact.Pair.Extract

/-! Actual derivatives along a displacement as physical-label operators, before Taylor projection. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.MultipleContact.Two
open Function Filter Set Metric Table
open scoped ContDiff BigOperators Filter Topology Classical
variable {G:Gauge}{L:Register G}{S:Table L}(P:DiffPlan S){n:ℕ}

open WithLp
-- first-coordinate path. All smuls by real vectors, converted to complex scalars for labels.
def tangent (n:ℕ)(u:E4) : Points (n+1):=Points.cons u 0
lemma tangent_basis (n:ℕ)(u:E4): tangent n u=∑ i:Axis,u i • Points.direction (0:Fin (n+1)) i:=by
   ext1 j; rw [withLp_sum]; refine Fin.cases ?_ ?_ j
   · change u=∑ i,u i • (basis i)
     ext1 t;rw [withLp_sum']; simp [basis,EuclideanSpace.single, PiLp.single_apply, PiLp.smul_apply]
   intro j; change (0:E4)=_; simp [Points.direction,PiLp.single_apply]
where
 withLp_sum {f:Axis →Points (n+1)}(i:Fin (n+1)): (∑ j:Axis,f j) i=∑ j:Axis, f j i:=by simp [WithLp.ofLp_sum,Finset.sum_apply]
 withLp_sum' {f:Axis →E4}(i:Axis): (∑ j:Axis,f j) i=∑j, f j i:=by simp [WithLp.ofLp_sum,Finset.sum_apply]
lemma tangent_eq (z:Points n)(u:E4)(t:ℝ): Points.cons (t•u) z=Points.cons (0:E4) z + t • tangent n u:=by
  ext1 i; exact Fin.cases (zero_add _).symm (fun k=>by simp [Points.cons,tangent]) i
lemma derivative_tangent (z:Points n)(u:E4)(t:ℝ):HasDerivAt (fun b:ℝ=>Points.cons (b • u) z) (tangent n u) t:=by
  simp_rw [tangent_eq]
  simpa only [Pi.smul_apply,id_eq,one_smul] using ((hasDerivAt_id t).smul_const (tangent n u)).const_add (Points.cons 0 z)
lemma contdiff_tangent (z:Points n)(u:E4):ContDiff ℝ ∞ (fun t:ℝ=>Points.cons (t • u) z):=by
  simp_rw [tangent_eq]; exact contDiff_const.add (contDiff_id.smul contDiff_const)

def axisStep (P:DiffPlan S)(w:ℕ)(u:E4): S.Field w →ₗ[ℂ] S.Field (w+1) := ∑ i:Axis,(u i:ℂ) • P.deriv w i
private lemma field_step (w:ℕ)(u:E4)(v:S.Field w)(f:S.Field (w+1)→ₗ[ℂ] ℂ):
   f (axisStep P w u v)= ∑ i, (u i:ℂ)* f ((P.deriv w i) v):=by unfold axisStep;rw [LinearMap.sum_apply,map_sum]; congr 1; funext i;rw [LinearMap.smul_apply,map_smul];rfl
lemma step_deriv {z:Points n}{t:ℝ}(w:ℕ)(v:S.Field w)(q:Fin n→L.Token) {u:E4}(hS:S.Smooth)(hP:P.Derivatives S)(hz:Safe (t • u) z):
    HasDerivAt (fun b:ℝ=>siteValue S q w v (b • u) z) (siteValue S q (w+1) (axisStep P w u v) (t • u) z) t:=by
   let f(x) := S.useAt S x (Fin.cons ⟨w,v⟩ (S.classTokens ∘ q))
   let g(y:ℝ):=Points.cons (y•u) z
   let F:= fderiv ℝ f (g t)
   have he:DifferentiableAt ℝ f (g t) := ((S.class_smooth S hS _ _ hz |>.contDiffAt ((conf_open _).mem_nhds hz)).differentiableAt (by simp))
   have hh:HasDerivAt (f ∘ g) (F (tangent n u)) t := he.hasFDerivAt.comp_hasDerivAt t (derivative_tangent z u t)
   change HasDerivAt (f ∘ g) _ _
   rw [siteValue,fixedValue,← Work.A01.front_eval,field_step]
   rw [show F (tangent n u)=∑i, u i • F (Points.direction 0 i) from by rw [tangent_basis,map_sum];exact Finset.sum_congr rfl fun i _=>by simp only [map_smul]] at hh
   refine Eq.mp (congr_arg (fun v:ℂ=>HasDerivAt (f ∘ g) v t) (Finset.sum_congr rfl fun i _=>?_)) hh
   rw [Work.A01.front_eval,hP.kernels _ _ _ hz,Complex.real_smul]
   rfl

def arrow (P:DiffPlan S)(w:ℕ)(u:E4):(i:ℕ)→ S.Field w →ₗ[ℂ] S.Field (w+i)
 | 0=> LinearMap.id -- not defeq?
 | n+1 => (axisStep P (w+n) u).comp (arrow P w u n)

lemma step_bound (w:ℕ):∃c:ℝ,0≤c∧∀u:E4,∀v:S.Field w,‖axisStep P w u v‖ ≤c*‖v‖*‖u‖:=by
    let A(i):=‖LinearMap.toContinuousLinearMap (P.deriv w i)‖
    refine ⟨∑ i:Axis,A i,Finset.sum_nonneg (fun a _=>norm_nonneg (LinearMap.toContinuousLinearMap (P.deriv w a))),fun u v=>?_⟩
    unfold axisStep;rw [LinearMap.sum_apply,Finset.sum_mul,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
    erw [LinearMap.smul_apply,norm_smul,Complex.norm_real]
    exact (mul_le_mul (PiLp.norm_apply_le u i) ((LinearMap.toContinuousLinearMap (P.deriv w i)).le_opNorm v) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm ..)
lemma arrow_bound (w j:ℕ):∃c:ℝ,0≤ c∧∀u:E4,∀v:S.Field w,‖arrow P w u j v‖ ≤ c*‖v‖*‖u‖^j:=by
    induction j with
    | zero => exact ⟨1,zero_le_one,fun _ z=>by simp [arrow]⟩
    | succ n ih=>
        obtain ⟨c,hc,hv⟩:=ih; obtain ⟨d,hd,hW⟩:=step_bound P (w+n)
        exact ⟨d*c,mul_nonneg hd hc,fun u v=> (hW u (arrow P w u n v)).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv u v) hd) (norm_nonneg u)).trans_eq (by rw [pow_succ];ring))⟩
-- Taylor jets along a physical shift
private def pathFn (q:Fin n→L.Token)(w:ℕ)(z:Points n)(v:S.Field w)(u:E4)(i:ℕ) : ℝ→ℂ:= fun t=>siteValue S q (w+i) (arrow P w u i v) (t • u) z

lemma mixJet (q:Fin n→L.Token)(w:ℕ)(z:Points n)(v:S.Field w)(u:E4)(m:ℕ)(hP:P.Derivatives S)(hS:S.Smooth)(he:∀t∈Set.Icc (0:ℝ) 1,Safe (t • u) z){t:ℝ}(ht:t∈Set.Icc (0:ℝ) 1):iteratedDerivWithin m (pathFn P q w z v u 0) (Set.Icc (0:ℝ) 1) t=pathFn P q w z v u m t:=by
    let f:=pathFn P q w z v u; induction m generalizing t with
    | zero => simp
    | succ j ih=>
      have hx:=step_deriv P (w+j) (arrow P w u j v) q hS hP (he t ht)
      change _=f (j+1) t
      rw [iteratedDerivWithin_succ]
      refine Eq.trans (derivWithin_congr (f:=f j) (fun _ h=>ih h) (ih ht)) (hx.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc (show (0:ℝ) < 1 from zero_lt_one)) t ht))

lemma taylorMix (q:Fin n→L.Token)(w:ℕ)(m:ℕ)(z:Points n)(v:S.Field w)(u:E4)(hP:P.Derivatives S)(hS:S.Smooth)(he:∀t∈Set.Icc (0:ℝ) 1,Safe (t • u) z)(a:ℝ)(h:∀t∈Icc (0:ℝ) 1,‖siteValue S q (w+(m+1)) (arrow P w u (m+1) v) (t•u) z‖≤a):
   ‖siteValue S q w v u z - ∑ i:Fin (m+1), (↑(i.val.factorial:ℕ):ℝ)⁻¹ • siteValue S q (w+i) (arrow P w u i v) 0 z‖ ≤ a:=by
   let f:=pathFn P q w z v u; let I:=Icc (0:ℝ) 1; have hI:(0:ℝ)∈I∧(1:ℝ)∈I:=⟨⟨by rfl,zero_le_one⟩,by constructor <;> norm_num⟩
   have hK(i) (t)(ht:t∈I): iteratedDerivWithin i (f 0) I t =f i t:=mixJet P q w z v u i hP hS he ht
   have f0 : f 0 1=siteValue S q w v u z:=by change siteValue S q w v ((1:ℝ) • u) z=_;rw [one_smul]
   have he0 i:f i 0=siteValue S q (w+i) (arrow P w u i v) 0 z:=by simp only [f,pathFn,zero_smul]
   have f1 : taylorWithinEval (f 0) m I 0 1= ∑ i:Fin (m+1), (↑(i.val.factorial:ℕ):ℝ)⁻¹ • siteValue S q (w+i.val) (arrow P w u i v) 0 z:=by
      rw [taylor_within_apply]; simp only [sub_zero,one_pow,mul_one,hK _ _ hI.1,he0];exact (Fin.sum_univ_eq_sum_range _ _).symm
   have hf:ContDiffOn ℝ (↑m+1) (f 0) I:=by
      let g(t:ℝ) := Points.cons (t•u) z
      have hf:=contdiff_tangent z u
      have hz:= S.class_smooth S hS (Fin.cons (⟨w,v⟩:S.Tag) (S.classTokens ∘ q))
      exact ((hz.comp hf.contDiffOn (he:MapsTo g I (conf (n+1)))).of_le (show (↑m+1:WithTop ℕ∞)≤ ∞ from by exact mod_cast le_top))
   have hh:=taylor_mean_remainder_bound zero_le_one hf hI.2 fun t ht=> by rw [hK _ _ ht];exact h t ht
   rw [sub_zero,one_pow,mul_one,f0,f1] at hh
   exact hh.trans (div_le_self ((norm_nonneg _).trans (h (0:ℝ) hI.1)) (by exact_mod_cast (show (1:ℕ)≤m.factorial from Nat.factorial_pos m)))
end YM.MultipleContact.Two
