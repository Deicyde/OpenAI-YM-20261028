import YM.FullVolume.Amp.Fish
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Instances.RealVectorSpace
/-! Homogeneous polynomial along the coupon shell. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type*} [DecidableEq I][SeminormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {s:Finset I}{f:X→Y}{x:X}{c p r k:ℝ}{n j:ℕ}
variable (L : Often p f x r c)
abbrev fee (p r:ℝ):= 2*Real.exp 1/(r*p)
namespace Often
variable (n) (u: Fin n→ X)
def anchor :Y:= ((Nat.factorial n:ℕ):ℝ)⁻¹ • block univ u (L.bank n) 0
lemma labels (k:ℝ) (he:0≤k)(hp:∀ i,‖u i‖≤k): ‖L.anchor n u‖ ≤ (k*fee p r)^n*c:=by
    let F:= ((Nat.factorial n:ℕ):ℝ); let Ω:= (univ:Finset (Fin n)); have hb:= L.width; have h₀:= zero_lt_one.trans_le L.pays.1
    have hz T (ht:T∈Ω.powerset): ‖signed Ω T • L.bank n (0+∑ i∈T,u i)‖≤ ((n*k/r)/p)^n*c:=by
       rw [norm_smul,signed,norm_pow,norm_neg,norm_one,one_pow,one_mul,zero_add]
       apply lend'; apply le_trans (norm_sum_le ..); refine (sum_le_sum (fun i _=>hp i)).trans ?_; rw [sum_const,nsmul_eq_mul]; rw [mul_div_cancel₀ _ hb.ne']; apply mul_le_mul_of_nonneg_right _ he; exact Nat.cast_le.mpr (by simpa [Ω] using card_le_card (mem_powerset.mp ht))
    have hc:↑(Ω.powerset.card)=(2:ℝ)^n:=by simp [Ω]
    unfold anchor; rw [norm_smul,norm_inv,Real.norm_of_nonneg (by positivity)]
    have hE: (n:ℝ)^n/F ≤ (Real.exp 1)^n:= by
       rw [← Real.exp_nat_mul,mul_one]; exact le_trans (by apply single_le_sum (f:=fun i:ℕ=>(n:ℝ)^i/i.factorial) (fun _ _=>by positivity) (mem_range.mpr n.lt_succ_self)) (Real.sum_le_exp_of_nonneg (by positivity) (n+1))
    calc
      _ ≤ F⁻¹*((2:ℝ)^n*(((n*k/r)/p)^n*c)):= mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ((sum_le_sum hz).trans_eq (by rw [sum_const,nsmul_eq_mul,hc]))) (by positivity)
      _ = (n^n/F:ℝ) * ((2*k/(r*p))^n*c) := by
         push_cast; simp only [div_pow,mul_pow]; ring
      _ ≤ _ := by
        change _ ≤ (k*(2*Real.exp 1/(r*p)))^n*c; push_cast
        apply (mul_le_mul_of_nonneg_right hE (show 0≤(2*k/(r*p))^n*c from mul_nonneg (by positivity) L.pays.2)).trans_eq
        simp [div_pow,mul_pow]; ring
lemma coast (i:Fin n)(y:X)(v:X): L.anchor n (Function.update u i (y+v))=L.anchor n (Function.update u i y)+L.anchor n (Function.update u i v):=by
    let Ω := univ.erase i
    let U:= L.bank n
    have hh(p x:X): block univ (Function.update u i p) U x= block Ω u U (x+p)-block Ω u U x:=by
       rw [show (univ:Finset (Fin n))=insert i Ω from (insert_erase (mem_univ _)).symm, cons Ω _ _ _ (notMem_erase i Finset.univ), Function.update_self, same Ω (Function.update u i p) (v:=u) (h:=fun j hj=> Function.update_of_ne (ne_of_mem_erase hj) ..),same Ω (Function.update u i p) (v:=u) (h:=fun j hj=>Function.update_of_ne (ne_of_mem_erase hj) ..)]
    unfold anchor; rw [← smul_add]; congr 1; change block _ _ U _ =block _ _ U _+block _ _ U _
    rw [L.clone univ (Function.update u i v) 0 y _ (by simp),hh,hh,hh]; simp
-- local bounded => continuous
lemma coastS (i:Fin n)(y:X)(a:ℝ): L.anchor n (Function.update u i (a • y))= a • L.anchor n (Function.update u i y):=by
   let P:X→+Y:= { toFun := fun t=> L.anchor n (Function.update u i t), map_zero' := by have h:=L.coast n u i 0 0; simp only [zero_add] at h; exact (add_right_cancel (Eq.trans (zero_add _) h)).symm, map_add' := L.coast n u i }
   apply (map_real_smul P ?_ _ _)
   apply continuous_of_continuousAt_zero P
   apply Metric.continuousAt_iff.mpr
   intro ε he
   let e:=‖u‖+1; let c':= (e*fee p r)^n*c
   obtain ⟨m,hM⟩:=exists_nat_gt (c'/ε)
   have hE:1≤ e := le_add_of_nonneg_left (norm_nonneg _)
   have hp:0≤fee p r:= by unfold fee; have hh:=L.width; have hg:=zero_lt_one.trans_le L.pays.1; positivity
   have h:c'≥0:= mul_nonneg (pow_nonneg (mul_nonneg (zero_le_one.trans hE) hp) _) L.pays.2
   have h₀:0<(m:ℝ):= (div_nonneg h he.le).trans_lt hM
   refine ⟨m⁻¹, by positivity,fun z hz=>?_⟩ -- Nat notation
   simp only [map_zero,dist_zero_right] at *; apply lt_of_mul_lt_mul_left _ h₀.le
   rw [← Real.norm_of_nonneg h₀.le,← norm_smul, Real.norm_of_nonneg h₀.le,Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul]
   refine (L.labels n _ e (zero_le_one.trans hE) ?_).trans_lt ((div_lt_iff₀ he).1 hM)
   intro j; by_cases hk:j=i
   · subst j; rw [Function.update_self,← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_of_nonneg h₀.le]; exact (by apply le_trans _ hE; nlinarith [mul_inv_cancel₀ h₀.ne'])
   rw [Function.update_of_ne hk]; exact (norm_le_pi_norm _ j).trans (le_add_of_nonneg_right (by norm_num))
def garden : MultilinearMap ℝ (fun _ : Fin n => X) Y:=
   { toFun:=L.anchor n, map_update_add' := by intro v; cases Subsingleton.elim v (instDecidableEqFin n); exact L.coast n, map_update_smul' :=by intro v; cases Subsingleton.elim v (instDecidableEqFin n); exact fun f i a y=> L.coastS n f i y a }
-- use t↓ if seminull
lemma fruit : ‖L.garden n u‖ ≤ (fee p r)^n*c*∏ i, ‖u i‖:=by
   let b : ℝ:=fee p r^n*c
   let f:=fun t:ℝ=> b*∏ i, (‖u i‖+t)
   have hp: Tendsto f (𝓝[>] 0) (𝓝 (b*∏ i,‖u i‖)):= by
      simpa [f] using (Continuous.tendsto (show Continuous f by unfold f; fun_prop) 0).mono_left (show 𝓝[>] 0 ≤ _ from nhdsWithin_le_nhds)
   refine ge_of_tendsto hp ?_
   filter_upwards [self_mem_nhdsWithin] with t ht; let a i:=‖u i‖+t; have hA(i):0<a i:= add_pos_of_nonneg_of_pos (norm_nonneg _) (show 0<t from ht)
   let w(i):= (a i)⁻¹ • u i
   have hh: L.garden n u=(∏ i,a i) • L.garden n w:=by rw [← MultilinearMap.map_smul_univ]; congr; ext i; exact (smul_inv_smul₀ (hA i|>.ne') _).symm
   rw [hh,norm_smul, Real.norm_of_nonneg (prod_nonneg fun i _=> (hA i).le), show f t=(∏ i,a i)* ( (1*fee p r)^n*c) from (by unfold f; rw [one_mul,mul_comm b] -- f unfold
                                                                             )]
   apply mul_le_mul_of_nonneg_left (L.labels n _ _ zero_le_one ?_) (prod_nonneg fun i _=> (hA i).le)
   intro i; unfold w; rw [norm_smul,norm_inv,Real.norm_of_nonneg (hA i).le,inv_mul_le_iff₀ (hA i)]; rw [mul_one]; exact le_add_of_nonneg_right (le_of_lt (show 0<t from ht))
def gardenL : X [×n]→L[ℝ] Y:= MultilinearMap.mkContinuous (L.garden n) ((fee p r)^n*c) (L.fruit n)
lemma course: ‖L.gardenL n‖≤ fee p r^n*c:= MultilinearMap.mkContinuous_norm_le _ (mul_nonneg (by unfold fee; have hh:=L.width; have hp:=zero_lt_one.trans_le L.pays.1; positivity) L.pays.2) _
lemma seeds (z:X): L.gardenL n (fun _=>z)=L.bank n z:=by
  have hp:= L.draw (univ:Finset (Fin n)) z; simp only [Finset.card_univ,Fintype.card_fin] at hp
  change L.anchor n (fun _=>z)=_; rw [anchor,hp,inv_smul_smul₀ (by positivity)]
-- continuation after extending.Multilinear. previous.Coordinates bound q.
lemma party (z:X)(hz:‖z‖ ≤r) : HasSum (fun n=>L.gardenL n (fun _=>z)) (f (x+z)):= by simp_rw [seeds]; exact L.gift z hz
end Often
end YM.FullVolume.Amp
