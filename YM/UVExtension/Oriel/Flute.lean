import YM.UVExtension.Oriel.Gate

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
private lemma matchY (v w : Fin 4→R) (hv : ∀ i,‖L (v i)‖≤1) (_hw : ∀ i,‖L (w i)‖≤1) (B:Reel f M v)(A:Reel f M w) (z z':Plot₀)(he:∀ i,‖z i‖≤ traceB)(hx:∀ i,‖z' i‖≤traceB)(hk:tock L v z=tock L w z'): B.F z=A.F z':= by
  let g (z: Plot₀) (x:ℂ)(i:Fin 4):= (↑(z i).re:ℂ)+x* (↑(z i).im:ℂ)
  let a(z:Plot₀)(x:ℝ) (i:Fin 4):= (z i).re+x*(z i).im
  have hg (z:Plot₀) (x:ℝ): g z x= Lamppost.hoist (a z x):= by funext i; simp [g,a,hoist]
  have hr(z:Plot₀): g z I=z:= by funext i; unfold g; rw [mul_comm I,re_add_im]
  have hu(z:Plot₀)(hz:∀ i,‖z i‖ ≤ traceB) (x:ℂ) (hp:‖x‖≤2) i: ‖g z x i‖≤ 3*traceB:=by
    apply (norm_add_le ..).trans; rw [norm_mul,norm_real,norm_real,Real.norm_eq_abs,Real.norm_eq_abs]; linarith only [(abs_re_le_norm (z i)).trans (hz i), mul_le_mul hp ((abs_im_le_norm (z i)).trans (hz i)) (abs_nonneg (z i).im) (by norm_num : (0:ℝ)≤ 2)]
  let s:= ball (0:ℂ) 2
  have hM(z:Plot₀)(hz:∀ i,‖z i‖≤ traceB):MapsTo (g z) s shieldB:= fun x (hp:x∈s)=> Lamppost.within.mpr (fun i=> mem_ball_zero_iff.mpr ((hu _ hz _ (mem_ball_zero_iff.mp hp|>.le) i).trans_lt (by norm_num [traceB])))
  obtain ⟨ht,ht'⟩:= splits L P v w z z' hk
  have hh(z:Plot₀)(w:Fin 4→R)(x:ℝ): L (tick w (a z x))= L (tick w (fun i=> (z i).re))+x • L (tick w (fun i=> (z i).im)):= by simp_rw [tick,a,map_sum,map_smul, Finset.smul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [add_smul,smul_smul]
  have hF (t:ℝ)(hp:‖t‖<2): B.F (g z t)= A.F (g z' t):= by
    have hW (z:Plot₀)(hz:∀ i,‖z i‖≤traceB) (i:Fin 4) : |a z t i| ≤3*traceB:=by
      have h:=hu z hz (↑t) ((norm_real _).trans_lt hp|>.le) i; rw [hg] at h; simpa only [hoist,norm_real,Real.norm_eq_abs] using h
    rw [hg,hg,B.ear (a z t) (fun i=> (hW z he i).trans_lt (by norm_num [traceB,radiusU])),A.ear (a z' t) (fun i=> (hW z' hx i).trans_lt (by norm_num [traceB,radiusU]))]; apply blank L h
    · unfold tick; rw [map_sum]; apply (norm_sum_le ..).trans
      refine le_trans (Finset.sum_le_sum (g:=fun i=> 3*traceB) (fun i _=>?_)) (by norm_num [traceB,pocket])
      rw [map_smul,norm_smul]; exact (mul_le_mul (hW z he i) (hv i) (norm_nonneg _) (by norm_num [traceB])).trans_eq (mul_one _)
    rw [hh,hh,ht,ht']
  let t(x:ℂ) (i:Bool) := if i=true then B.F (g z x) else A.F (g z' x)
  have hc(z) :DifferentiableOn ℂ (g z) s:= (differentiable_pi.mpr fun i=> by unfold g; fun_prop).differentiableOn
  have hT (i:Bool):DifferentiableOn ℂ (fun x=> t x i) s:=by cases i; exact A.score _ _ isOpen_ball (hM z' hx) (hc z'); exact B.score _ _ isOpen_ball (hM z he) (hc z)
  rw [← hr z, ← show g z' I=z' from hr z']
  refine Husk.poppet (F:=t) (Husk.audit true false) (by norm_num : (0:ℝ)<2) hT ⟨1,one_ne_zero,?_⟩ (mem_ball_zero_iff.mpr (by simp))
  filter_upwards [ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<2)] with q h
  simpa only [mul_one,zero_add] using! hF q (mem_ball_zero_iff.mp h)

namespace Charted
omit h P
def tender (L:R→ₗ[ℝ] X)(f:R→Y)(M:ℝ)(x:X)(y:Y): Prop:= ∃ v:Fin 4→R,(∀ i,‖L (v i)‖≤1)∧ ∃ B: Reel f M v,∃ z:Plot₀,(∀ i,‖z i‖≤traceB)∧ x=tock L v z ∧ y=B.F z
def fill (f:R→Y) (M:ℝ) (x:X):= if h:∃ y,tender L f M x y then h.choose else 0
include P h
lemma thins (v:Fin 4→R)(hv :∀ i,‖L (v i)‖≤1)(B:Reel f M v)(z:Plot₀)(he:∀ i,‖z i‖≤ traceB): fill L f M (tock L v z)=B.F z:=by
  unfold fill; split
  next hb=> obtain ⟨v',h',V,z',hz,hh,hY⟩:= hb.choose_spec; rw [hY]; exact matchY L P h _ _ h' hv V B z' z hz he hh.symm
  next h'=> exact False.elim (h' ⟨_, v,hv,B,z,he,rfl,rfl⟩)

lemma meets (x:R)(hz:‖L x‖ < rim): fill L f M (L x)= f x:=by
  let v:=![rim⁻¹ • x, (0:R),0,0]; let a:= ![rim,0,0,0]; let z:= hoist a
  have he(i:Fin 4): ‖L (v i)‖≤1:= by fin_cases i <;> simp [v,norm_smul]; unfold rim at hz; linarith
  have ha: tick v a=x:= by unfold tick; simp [Fin.sum_univ_succ,v,a]
  obtain ⟨B⟩:= h.spins v he; have hp:tock L v z=L x:=by unfold tock; simp_rw [z,hoist,rsmul X,← map_smul, ← map_sum]; exact congr_arg L ha
  rw [← hp,thins L P h v he B z (by intro i; fin_cases i <;> norm_num [z,hoist,rim,traceB,a,norm_real]), B.ear a (by intro i; fin_cases i <;> norm_num [rim,radiusU,a]),ha]
end Charted
end YM.UVExtension.Oriel
