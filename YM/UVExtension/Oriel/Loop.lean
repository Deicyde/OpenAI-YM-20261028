import YM.UVExtension.Oriel.Flute

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Oriel
open Function Filter Set Metric Lamppost Complex
open scoped BigOperators Topology ContDiff Classical
variable {X Y R : Type} [AddCommGroup R] [Module ℝ R]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (L:R→ₗ[ℝ] X){f : R→Y}{M:ℝ}(P:Firm L)(h:Charted L f M)
include h P
namespace Charted
private def round (z:ℂ):Plot₀:=![ (rim:ℂ), I*rim,z,z*I]
omit P h in
private lemma ballot (a:ℝ)(hz:‖(rim:ℂ)‖≤a)(z:ℂ)(h:‖z‖≤a)(i): ‖round z i‖≤a:= by fin_cases i <;> simp [round] at hz ⊢ <;> assumption

private lemma bill {x y:X}(he:‖x‖ < rim)(hp:paint L x)(hv:‖y‖≤1)(hx:paint L y):∃ H:ℂ→Y, DifferentiableOn ℂ H (ball 0 3)∧(∀ z∈ ball (0:ℂ) 3,‖H z‖≤M)∧ ∀ z:ℂ,‖z‖≤ traceB → H z=fill L f M (x+z • y):= by
  obtain ⟨a,b,rfl⟩:= hp; obtain ⟨u,v,rfl⟩:=hx
  let w:= ![rim⁻¹ • a, rim⁻¹ • b,u,v]
  have he' := P.ink a b; have hA:= he'.1.trans_lt he; have hB:= he'.2.trans_lt he; have hx:= P.ink u v
  have hW(i:Fin 4):‖L (w i)‖≤1:= by
    fin_cases i <;> simp [w,norm_smul]
    · unfold rim at hA; linarith
    · unfold rim at hB; linarith
    · exact hx.1.trans hv
    exact hx.2.trans hv
  obtain ⟨F⟩:= h.spins w hW
  have hT:MapsTo round (ball 0 3) shieldB:=by intro z hz; apply within.mpr; intro i; fin_cases i <;> norm_num [round,rim,mem_ball_zero_iff,norm_mul,I_mul_I] at * <;> assumption
  refine ⟨fun z=> F.F (round z), F.score _ _ isOpen_ball hT (differentiable_pi.mpr (fun i=>by fin_cases i <;> simp [round])|>.differentiableOn), fun z hz=>F.bound _ (hT hz),fun z hz=>?_⟩
  have hp:tock L w (round z)=L a + I • L b+z • (L u+I • L v):=by
    have hh (v:R): (↑rim:ℂ) • L (rim⁻¹ • v)= L v:= by rw [map_smul,rsmul, smul_inv_smul₀ (by norm_num [rim])]
    unfold tock
    rw [Fin.sum_univ_four]
    change (rim:ℂ) • L (rim⁻¹ • a)+(I*(rim:ℂ)) • L (rim⁻¹ • b)+z • L u+ (z*I) • L v=_
    rw [mul_smul I,hh,hh,mul_smul,smul_add]; abel
  rw [← hp, thins L P h w hW F (round z) (ballot _ (by norm_num [rim,traceB]) _ hz)]

variable {L}
def Grip: Set X:= ball 0 rim
variable (L) {x y:X}(hx:x∈ Grip) (hp:paint L x)
omit P h

def well := (Grip∩ {v:X|paint L v})

section work
omit [IsScalarTower ℝ ℂ X] in
lemma inkwell (x:R): paint L (L x):=⟨x,0,by simp⟩
def undertone : Submodule ℂ X where
   carrier:= {x| paint L x}
   add_mem':= by
     rintro _ _ ⟨a,b,rfl⟩ ⟨u,v,rfl⟩; exact ⟨a+u,b+v,by simp only [map_add,smul_add]; abel⟩
   zero_mem' := map_zero L ▸ inkwell L 0
   smul_mem' := by
      rintro z _ ⟨a,b,rfl⟩
      refine ⟨z.re • a - z.im • b, z.im • a+z.re • b,?_⟩
      rw [smul_add,smul_smul,tone z (L a), tone (z*I)]
      simp only [Complex.mul_I_re,Complex.mul_I_im,map_sub,map_add,map_smul,neg_smul,smul_add]; abel
end work
include P h hx hp
lemma canvas :‖fill L f M x‖≤M:= by
  obtain ⟨H,h,hQ,hF⟩:= bill L P h (mem_ball_zero_iff.mp hx) hp (x:=x) (y:=0) (by simp) (show (0:X)∈undertone L from (undertone L).zero_mem)
  simpa only [hF 0 (by norm_num [traceB]),zero_smul,add_zero] using hQ 0 (mem_ball_self (by norm_num))
lemma slides (ht:y∈ Grip)(he:paint L y): ‖fill L f M y-fill L f M x‖≤M*‖y-x‖:=by
  by_cases hA:x=y
  · rw [hA]; simp
  let d:= ‖y-x‖; have hd:0<d:= norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hA))
  have hv : d < traceB:=(norm_sub_le y x).trans_lt (lt_trans (add_lt_add (mem_ball_zero_iff.mp ht) (mem_ball_zero_iff.mp hx)) (by norm_num [traceB,rim]))
  let v: X:= d⁻¹ • (y-x)
  obtain ⟨H,hP,hQ,hF⟩:= bill L P h (mem_ball_zero_iff.mp hx) hp (y:=v) (by rw [show ‖v‖=d⁻¹*d from (norm_smul ..).trans (by rw [Real.norm_of_nonneg (inv_pos.mpr hd).le]), inv_mul_cancel₀ hd.ne']) (show v∈undertone L from (by unfold v; rw [← rsmul X]; exact (undertone L).smul_mem _ ((undertone L).sub_mem he hp)))
  have hs:‖(d:ℂ)‖=d:= (norm_real d).trans (Real.norm_of_nonneg hd.le)
  have hJ:= diary H hP hQ (x:= (d:ℂ)) (hs.trans_lt (hv.trans (by norm_num [traceB])))
  rw [hF _ (hs.trans_le hv.le), hF 0 (by norm_num [traceB]),zero_smul,add_zero,hs, rsmul,show d • v=y-x from smul_inv_smul₀ hd.ne' _,add_sub_cancel] at hJ; exact hJ

lemma gate (hz:paint L y): DifferentiableAt ℂ (fun z:ℂ=> fill L f M (x+z • y)) 0:=by
  let d:= Complex.ofReal (‖y‖+1); let v:= d⁻¹ • y; have hd:0<d.re:=by dsimp [d]; positivity
  have hs: ‖d‖=‖y‖+1:= (norm_real _).trans (Real.norm_of_nonneg (by positivity))
  have hu:d≠0:= norm_pos_iff.mp (hs.trans_gt hd)
  obtain ⟨H,hP,hQ,hJ⟩:= bill L P h (mem_ball_zero_iff.mp hx) hp (y:=v) (by unfold v; rw [norm_smul,norm_inv,hs]; exact inv_mul_le_one_of_le₀ (by linarith) (by positivity)) ((undertone L).smul_mem d⁻¹ hz)
  let g (z:ℂ):=z*d
  have hg:g 0∈ ball (0:ℂ) 3:= by simp [g]
  apply ((hP.differentiableAt (isOpen_ball.mem_nhds hg)).comp 0 (show DifferentiableAt ℂ g 0 from differentiableAt_id.mul_const _)).congr_of_eventuallyEq
  have hV: Continuous g:= continuous_id.mul continuous_const
  filter_upwards [hV.continuousAt.preimage_mem_nhds (x:=0) (show ball (0:ℂ) traceB∈𝓝 (g 0) by rw [show g 0=0 from zero_mul _]; exact ball_mem_nhds _ (by norm_num [traceB]))] with z ht; change _=H (g z); rw [hJ _ (mem_ball_zero_iff.mp ht|>.le)]; unfold g v; rw [mul_smul, smul_inv_smul₀ hu];
end Charted
end YM.UVExtension.Oriel
