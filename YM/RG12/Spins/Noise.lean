import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Dolphin
import YM.Pert.Parity.Cloud
/-!
# Sharp gaussian sym price on true V9 Cloud plus centred guard cut. Card colors
NOT number of keys in exponent: charge tail per large link, not against whole
energy density ratio. The bound applies at exact V=1 and the cut guard size t/u≫.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Noise
open Push.SectorMeasure Function Filter Set Lattice Wilson Pressure RG
open PhysicalNext.JointLoad.Heir Next Next.SectorChange AnalyticBridge.LocalGaussian
open Finset MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{C:Gaussian.Table (I × G.ColorIndex)}{K B u t:ℝ}{n:Side}
local notation "μ" C => Gaussian.cloud C
local notation "Z" => Prices G I
local notation "carG" => Fintype.card G.ColorIndex
section tails
variable (χ:Chi)
omit [DecidableEq I] in
lemma even_guard (u t:ℝ)(z:Z): PhysicalNext.JointLoad.Heir.guard χ G I u t (-z)=PhysicalNext.JointLoad.Heir.guard χ G I u t z:=by
   have hh : tape (-z)=(-(tape z):LogArray G I):= (map_neg gaugeCount z)
   simp only [PhysicalNext.JointLoad.Heir.guard,hh]; unfold doors broad; simp
-- indicator exponent for one link.C color card fixed
private def chunk (i:I) : Finset (I × G.ColorIndex) := Finset.univ.map ⟨fun j=> (i,j),fun _ _ h=> (Prod.mk_inj.mp h).2⟩
omit [DecidableEq I] in
private lemma onlink (i:I)(z:Z) : load (chunk i) z = ‖tape z i‖^2:= by
   simp_rw [load,chunk,Finset.sum_map]; rw [EuclideanSpace.real_norm_sq_eq]; rfl
-- Post cost polynomial in all dimensions, exp cut factor charged once per link.
protected def fade (t u K:ℝ):ℝ:= Real.exp (-(K⁻¹/4)*(t/(8*u))^2)
-- E currency exp integral cutoff tail.Period card of active I remains in front, pay Museum.heads.
lemma erode (hu : 0<u)(ht:0<t)(h:C.PosDef)(hh:0<K)(hC:Peak C K) :
   (∫ z:Z, ‖PhysicalNext.JointLoad.Heir.guard χ G I u t z-1‖ ∂(μ C)) ≤ 2*Noise.fade t u K*(Fintype.card I:ℝ)*2^(Fintype.card G.ColorIndex):=by
    let Γ:= PhysicalNext.JointLoad.Heir.guard χ G I u t
    let e (i:I)(z:Z):= Real.exp (K⁻¹/4*load (chunk i) z)
    have he(i:I): Integrable (e i) (μ C) ∧ (∫ z,e i z ∂(μ C)) ≤ (2:ℝ)^carG:=by
       simpa only [chunk,Finset.card_map,Finset.card_univ] using! corner_room (chunk (G:=G) i) h hh hC
    let F:= 2*Noise.fade t u K; have hF:0≤F:=by unfold F Noise.fade; positivity
    have hv:= guard_silent χ (G:=G) (I:=I) hu ht (n:=2)
    have hx : ∀ z:Z, ‖Γ z-1‖ ≤ F*∑ i:I,e i z:=by
       intro z; by_cases h : ∀ i,u*‖tape z i‖ ≤ t/8
       · rw [show Γ z=1 from guard_open χ hu ht h]; rw [sub_self,norm_zero]; exact mul_nonneg hF (sum_nonneg fun j _=> (Real.exp_pos _).le)
       push Not at h
       obtain ⟨i,hi⟩ :=h
       have hp : (t/(8*u))^2 ≤ load (chunk i) z := by
          rw [onlink]; gcongr; apply (div_le_iff₀ (mul_pos (by norm_num) hu)).mpr; linarith [hi.le]
       have hl : 1≤ Noise.fade t u K * e i z := by
          unfold e Noise.fade; rw [←Real.exp_add]; apply Real.one_le_exp; have he:=mul_le_mul_of_nonneg_left hp (show 0≤K⁻¹/4 by positivity); linarith
       refine (norm_sub_le ..).trans ?_
       have hz:=hv.little z; rw [Real.norm_eq_abs,norm_one]; apply le_trans (add_le_add_left hz _); dsimp [F]; apply le_trans _ (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=> (Real.exp_pos _).le) (Finset.mem_univ i)) hF); linarith only [hl]
    have hi:Integrable (fun z=>F*∑ i,e i z) (μ C):=(integrable_finsetSum Finset.univ (f:=e) (fun i _=> (he i).1)).const_mul _
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _) hi (Eventually.of_forall hx)).trans ?_
    rw [integral_const_mul,integral_finsetSum Finset.univ (fun i _=> (he i).1),mul_assoc (2*_:ℝ) (↑(Fintype.card I))]; apply mul_le_mul_of_nonneg_left _ hF; apply le_trans (sum_le_sum (s:=Finset.univ) (g:=fun _i:I=>(2:ℝ)^Fintype.card G.ColorIndex) (fun i _=> (he i).2)) ?_; exact le_of_eq (by simp)
-- eventual flat in x when t/u legal.
end tails
end YM.RG12.Noise
