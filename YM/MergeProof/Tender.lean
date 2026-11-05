import YM.MergeProof.Buys

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Bid Local
open Planned.GuardedAtom  Menu PhysicalNext.Repeat.Lotus Motion Extra.Multi Vac.Numbers
open Progress Supply Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}
def winter (G:Gauge) (d:ℕ):ℕ:= Extra.Histories.degree ((Labels.frames G).level d)+4
def fog (G:Gauge)(d:ℕ)(x:ℝ):= (x^winter G d)⁻¹
def sap (x:ℝ):ℝ:= x⁻¹
def stub (x:ℝ):ℝ:= Hat x/4
local notation "Θ"=> Labels.frames G
local notation "B"=> radiusB
lemma dew (p:ℕ) : ∀ᶠ x in atTop,
    let t:=Doors.stain x + p*siteFactor (radiusB x)*stub x
    ((radiusB x+radiusB x+1:ℕ):ℝ)^4*t ≤ 3 ∧ Real.exp t - 1 ≤ 1:=by
   filter_upwards [Extra.Multi.site_affords p, Extra.Multi.hat_affords 4 0,vacuum_affords, show ∀ᶠ x in atTop,8 ≤ radiusB x from Extra.Multi.scaleB_large 8, eventually_gt_atTop (0:ℝ)] with x hp he hm hv hx -- edit
   intro t; let P:=Hat x; have ht:0<P:=inv_pos.mpr (Real.sqrt_pos.mpr hx); let d:=B x; change (1+p*siteFactor d)*((d+d+1:ℕ):ℝ)^4*P ≤ 1 at hp
   let s:ℝ:=((d+d+1:ℕ):ℝ)^4; have hh:Doors.stain x= smallK x^2:= (Real.sq_sqrt (by unfold Doors.stain; positivity)).symm -- inference
   have hP:P ≤ 1/4:=by simp only [pow_zero,mul_one] at he; change 4*P≤1 at he; linarith only [he]
   have hz: smallK x^2≤P:= (pow_le_pow_left₀ (Real.sqrt_nonneg _) hm 2).trans (by rw [← pow_mul]; exact (pow_le_pow_of_le_one ht.le (by linarith only [hP]) (by norm_num : (1:ℕ)≤6*2)).trans_eq (pow_one _)) -- inspect
   have h₁:s*t ≤ 1:=by
      have hu:t≤(1+p*siteFactor d)*P:=by
         unfold t stub; rw [add_mul,one_mul,hh]; exact add_le_add hz (mul_le_mul_of_nonneg_left (show P/4≤ P from by linarith only [ht]) (mul_nonneg (Nat.cast_nonneg _) (show 0 ≤ siteFactor d by unfold siteFactor; positivity)))
      exact (mul_le_mul_of_nonneg_left hu (show 0 ≤ s by unfold s; positivity)).trans (le_trans (le_of_eq (by ring : s*((1+p*siteFactor d)*P)=(1+p*siteFactor d)*s*P)) hp)
   refine ⟨le_trans h₁ (by norm_num),?_⟩
   have hs : 2 ≤ s:=by
      have ht : (2:ℝ) ≤ (d:ℝ)+d+1:=by
         have he:(8:ℝ)≤d:= by exact_mod_cast hv
         linarith only [he]
      unfold s; push_cast; exact le_trans (by norm_num : (2:ℝ)≤2^4) (pow_le_pow_left₀ zero_le_two ht _)

   have h₂ : t ≤ Real.log 2 := by
      have hh:(1/2:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9] -- name
      apply le_trans _ hh; by_cases hp:0 ≤ t
      · have hx:= (mul_le_mul_of_nonneg_right hs hp).trans h₁; linarith
      push_neg at hp; linarith only [hp]
   have hz := Real.exp_monotone h₂|>.trans_eq (Real.exp_log (by norm_num)); linarith only [hz]
lemma polestar (C : ℝ) (hC:0 ≤ C)(k : ℕ) (b : ℝ) : ∀ᶠ x in atTop,C*(x+b)^k ≤ Real.exp ((radiusB x:ℝ)/128) := by
   filter_upwards [eventually_ge_atTop (C*(2:ℝ)^k),eventually_ge_atTop |b|,eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (128*(k+1:ℕ))] with x ha hx hx' hv
   calc
    _ ≤ C*(2*x)^k := by gcongr <;> grind
    _ = (C*(2:ℝ)^k)*x^k := by rw [mul_pow,← mul_assoc]
    _ ≤ x^(k+1) := by rw [pow_succ,mul_comm (x^k)]; gcongr
    _ = Real.exp ((k+1:ℕ)*Real.log x) := by rw [Real.exp_nat_mul,Real.exp_log hx']
    _ ≤ _ := by
      refine Real.exp_monotone ((le_div_iff₀ (by norm_num)).mpr (le_trans ?_ (show (Real.log x)^2 ≤ (radiusB x:ℝ) from Nat.le_ceil _)))
      have ht : 0 ≤ Real.log x:= le_trans (by positivity) hv
      nlinarith only [hv,ht,mul_le_mul_of_nonneg_right hv ht]
lemma rind (G:Gauge) (d:ℕ) (Y:Stage)(L:Side)(b:ℝ)(Ys:Stage)(t:ℝ): ∀ᶠ x in atTop,
     let y:=x+b; let F:Labels.Frame G d := (Labels.frames G).level d
     fog G d x*Y.columns ≤ 1 ∧ 2*orbitCost F*(t+2*Ys.columns)*fog G d y ≤ 1 ∧
       Real.exp (Y.supportExponent+2)*(Doors.cameras G d* x^Extra.Histories.degree F)*fog G d x ≤ stub x ∧
       sap y ≤ 1 ∧ sap y*((L.val:ℝ)^d* Ys.columns)*fog G d x ≤ fog G d y:=by
   let C:= ((L.val:ℝ)^d * Ys.columns); let k:=winter G d; let a:=orbitCost ((Labels.frames G).level d); let q:= Real.exp (Y.supportExponent+2)*Doors.cameras G d
   have hq:0 ≤ q:=mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Doors.cameras_ge G d)); have hk:1≤k:= by unfold k winter; omega -- edit
   have hY : Tendsto (fun x:ℝ=>x+b) atTop atTop:= tendsto_id.atTop_add (tendsto_const_nhds (x:=b)) -- edit
   filter_upwards [eventually_ge_atTop Y.columns,hY.eventually_ge_atTop (max (C*2^k) 1),hY.eventually_ge_atTop (2*a*(t+2*Ys.columns)),eventually_ge_atTop b,eventually_ge_atTop (4*q)] with x hx hs hv he hw
   intro y F  -- edit
   have h' := max_le_iff.mp hs; have hZ: 1 ≤ x:=Y.columns_ge.trans hx; have hp:0<x:= zero_lt_one.trans_le hZ; have hy:0<y:= zero_lt_one.trans_le h'.2
   have he':∀ z:ℝ,1 ≤ z→ z≤ z^k:= fun z h => by nth_rw 1 [← pow_one z]; exact pow_le_pow_right₀ h hk
   refine ⟨?_,?_,?_,(inv_le_one₀ hy).mpr h'.2,?_⟩
   · unfold fog; rw [mul_comm,← div_eq_mul_inv]; exact (div_le_one (by positivity)).mpr (hx.trans (he' x hZ))
   · unfold fog; rw [← div_eq_mul_inv]; exact (div_le_one (by positivity)).mpr (hv.trans (he' y h'.2))
   · change _*(Doors.cameras G d*x^Extra.Histories.degree F)*(x^k)⁻¹ ≤ _; change _≤ (Real.sqrt x)⁻¹/4
     have hs : Real.sqrt x ≤ x:= (Real.sqrt_le_left hp.le).mpr (by nlinarith); apply le_trans _ (div_le_div_of_nonneg_right (inv_anti₀ (Real.sqrt_pos.mpr hp) hs) (by norm_num))
     rw [← mul_assoc (Real.exp _), ← div_eq_mul_inv,div_le_iff₀ (pow_pos hp k)]; change q*x^Extra.Histories.degree F ≤ _
     have hh:4*q ≤ x^3:=hw.trans (by exact ((pow_one x).symm.trans_le (pow_le_pow_right₀ hZ (by norm_num))))
     have he : x^k=x^(Extra.Histories.degree F)*x^4:=pow_add ..; rw [he]; field_simp; linarith only [hh]
   change y⁻¹*C*(x^k)⁻¹ ≤ (y^k)⁻¹
   have hp: y≤2*x:=by unfold y;linarith only [he]
   have h₁ : C*y^k ≤ C*(2*x)^k:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy.le hp _) (mul_nonneg (by positivity) (zero_le_one.trans Ys.columns_ge))
   rw [mul_pow,← mul_assoc] at h₁; have h₂: C*y^k ≤ y*x^k:= h₁.trans (mul_le_mul_of_nonneg_right h'.1 (pow_nonneg (by linarith only [hZ]) _))
   field_simp; nlinarith only [h₂]
end YM.MergeProof
