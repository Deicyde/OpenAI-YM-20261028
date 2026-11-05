import YM.AnalyticNext.QUARTIC_MATCH.Range
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Peg

/-!
# Stationary quadratic integral extension (at real b)

χset measure allows differentiation on open purchased window. Explicit bc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory
open ConnectedActivityE6 Blaze Brush
open scoped Topology ContDiff BigOperators Classical Interval ENNReal
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {j k : ℕ} {u d v a D s A : ℝ}
variable (ϕ : E×F→ℝ) (ρ : E→F)
def visit (z : F) (t : ℝ) (x : ℝ×E) := (x.2,ρ x.2 + t • x.1 • z)
def offer (z : F) (x : ℝ×E) (t : ℝ) := (1-t)*scratch ((0:E),z) ϕ (visit ρ z t x)
def vote (z : F) (x : ℝ×E) := ∫ t in (0:ℝ)..1, offer ϕ ρ z x t
lemma roll (z : F) (x : E) : vote ϕ ρ z (0,x)=(1/2)* scratch (0,z) ϕ (x,ρ x) := by
  unfold vote offer visit; simp only [zero_smul, smul_zero, add_zero]; rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub] <;>  norm_num
lemma pivot (z : F) (b : ℝ) (x : E) : vote ϕ ρ z (b,x)=vote ϕ ρ (-z) (-b,x) := by
  unfold vote; apply intervalIntegral.integral_congr; intro s hs; unfold offer visit; simp only [neg_smul,smul_neg, neg_neg]; unfold scratch
  change _=_ * fderiv ℝ (fderiv ℝ ϕ) (x, ρ x+s•b •z) (0,-z) (0,-z)
  rw [show ((0:E),-z)= -(0,z) by simp, map_neg,map_neg]; simp

lemma funds (z : F) (b : ℝ) (x : E) (hp : fderiv ℝ ϕ (x,ρ x) (0,z)=0) (hq : ∀ t∈Icc (0:ℝ) 1, ContDiffAt ℝ 2 ϕ (visit ρ z t (b,x))) :
    ϕ (x,ρ x+b•z)-ϕ (x,ρ x)=b^2*vote ϕ ρ z (b,x) := by
  have he t : (x,ρ x)+t • b • (0,z)=visit ρ z t (b,x):=by change (x+t • b • (0:E), ρ x+t • b • z)=_; simp [visit]
  have h := residue ϕ (x,ρ x) (b • ((0:E),z)) (by simp_rw [he]; exact hq)
  rw [show (x,ρ x)+b • (0,z)= (x,ρ x+b • z)  from (by simp),map_smul,hp,smul_zero,sub_zero] at h
  rw [h,vote, ← intervalIntegral.integral_const_mul]; apply intervalIntegral.integral_congr; intro i _
  unfold inflect; change _=b^2*Lantern.offer _ _ _ _ _; unfold Lantern.offer scratch; rw [he,map_smul,map_smul]; change (1-i)*(b*(b*scratch ((0:E),z) ϕ (visit ρ z i (b,x))))=b^2*((1-i)*scratch ((0:E),z) ϕ (visit ρ z i (b,x))); ring -- normalization
section ira
variable {z : F} {t : ℝ} {x : ℝ×E}
def spanE (C D : ℝ) := (1+C+D)+(1+C+D)
def acrossE (j : ℕ) (C D : ℝ) := D*(D*clump j (spanE C D) C)
lemma camp (ht : t∈ Icc (0:ℝ) 1) (hp : ‖x‖ ≤ 1) (h : Brush j u 1 ρ x.2) (hz : ‖z‖ ≤ D) : Brush j (spanE u D) 1 (visit ρ z t) x := by
  -- scalar linear, no domain restriction on x1
  let L:= ContinuousLinearMap.snd ℝ ℝ E; let k:= ContinuousLinearMap.fst ℝ ℝ E
  let Z:= k.smulRight (t • z)
  have hh : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ..
  have hZ: ‖Z‖ ≤ D:= ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans hz) fun x=> by
    have hy : 0 ≤ D := (norm_nonneg _).trans hz
    change ‖x.1 • t • z‖ ≤ D*‖x‖; rw [norm_smul,norm_smul, Real.norm_of_nonneg ht.1,mul_comm D]; exact mul_le_mul (norm_fst_le x) ((mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz) (mul_nonneg ht.1 (norm_nonneg _)) (norm_nonneg _)
  have hx : Brush j D 1 Z x:= Brush.linearB _ ((Z.le_opNorm _).trans (mul_le_mul hZ hp (norm_nonneg x) ((norm_nonneg _).trans hz) |>.trans_eq (mul_one _))) (by rw [mul_one]; exact hZ) zero_le_one
  have hr : Brush j u 1 (ρ ∘ L) x:= by rw [← one_mul (1:ℝ)]; exact Brush.reading L h hh
  have he := hr.gathering hx
  have hL : Brush j 1 1 L x:= Brush.linearB _ ((norm_snd_le _).trans hp) (by simpa using hh) zero_le_one
  have hK:= h.nonneg; have hD := hx.nonneg
  have hc := (hL.climb (show 1≤1+u+D by linarith) le_rfl).pair (he.climb (by linarith) le_rfl)
  apply hc.shimmy; exact Eventually.of_forall fun i=> congr_arg (Prod.mk i.2) (congr_arg _ (smul_comm t i.1 z)) -- edit

lemma emitting (ht : t∈ Icc (0:ℝ) 1) (hp : ‖x‖ ≤ 1) (h : Brush j u 1 ρ x.2) (hz : ‖z‖ ≤ D)
    (hg : Brush (j+2) u 1 ϕ (visit ρ z t x)) : Brush j (acrossE j u D) 1 (fun x=> offer ϕ ρ z x t) x := by
  have hv : ‖((0:E),z)‖ ≤ D := by simpa using hz
  have H:= grade _ hv hg (camp ρ ht hp h hz); refine (H.smul (1-t)).climb (mul_le_of_le_one_left H.nonneg ?_) le_rfl
  change |1-t|≤_; rw [abs_of_nonneg (by linarith only [ht.2])]; linarith only [ht.1]

lemma pundit (h : ∀ t∈ Icc (0:ℝ) 1, Brush (j+2) u 1 ϕ (visit ρ z t x)) : ContinuousOn (offer ϕ ρ z x) (Icc (0:ℝ) 1) := fun i hi=> by
  apply ContinuousAt.continuousWithinAt; apply ContinuousAt.mul (continuousAt_const.sub continuousAt_id)
  unfold scratch
  exact ContinuousAt.clm_apply (ContinuousAt.clm_apply ((norm_F (norm_F (h i hi))).smooth.continuousAt.comp (f:=fun t=>visit ρ z t x) (show ContinuousAt (fun t=>visit ρ z t x) i from by unfold visit; fun_prop)) continuousAt_const) continuousAt_const

variable [FiniteDimensional ℝ E]
lemma election (D : ℝ) (x : ℝ×E) (hs : ∀ᶠ y in 𝓝 x, ‖y‖ ≤ 1) (h : ∀ᶠ y:ℝ×E in 𝓝 x, Brush j u 1 ρ y.2) (hz : ‖z‖ ≤ D)
    (hq : ∀ᶠ y in 𝓝 x,∀ t∈ Icc (0:ℝ) 1,Brush (j+2) u 1 ϕ (visit ρ z t y)) : Brush j (acrossE j u D) 1 (vote ϕ ρ z) x := by
  let P:Set ℝ:= Icc 0 1 -- edit
  let W x:= P.indicator (offer ϕ ρ z x)
  have ht := (emitting ϕ ρ (t:=0) (by simp) hs.self_of_nhds h.self_of_nhds hz (hq.self_of_nhds _ (by simp))).nonneg
  have hf : ∀ᶠ y in 𝓝 x, ∀ i, Brush j (acrossE j u D) 1 (fun y=> W y i) y := by
    filter_upwards [hs,h,hq] with y hy hY hq i
    by_cases he:i∈P
    · refine (emitting ϕ ρ he hy hY hz (hq i he)).shimmy ?_; exact Eventually.of_forall fun _=> Set.indicator_of_mem he _
    exact ((Brush.certified (k:=j) zero_le_one (x:=y) (0:ℝ)).climb (by simpa using ht) le_rfl).shimmy (Eventually.of_forall fun _=> Set.indicator_of_notMem he _)
  let μ:= volume (α:=ℝ) |>.restrict (Ioc 0 1)
  have hh : μ.real Set.univ = 1 := by unfold μ; simp [Measure.real]
  letI:IsFiniteMeasure μ := by unfold μ; infer_instance
  have hp : ∀ᶠ y in 𝓝 x, Measurable (W y) := by
    filter_upwards [hq] with y hy
    apply measurable_of_restrict_of_restrict_compl (s:=P) measurableSet_Icc
    · rw [show P.restrict (W y)= P.restrict (offer ϕ ρ z y) from funext fun i=> indicator_of_mem i.2 _]; exact (continuousOn_iff_continuous_restrict.mp (pundit ϕ ρ hy)).measurable
    rw [show Pᶜ.restrict (W y)=(fun _=> 0) from funext fun i=> indicator_of_notMem i.2 _]; exact measurable_const
  obtain ⟨hc,-⟩:= Meristem.points W μ ⟨fun _=> _,integrable_const _,hf⟩ hp
  refine (hc.buds (fun _ => acrossE j u D) (integrable_const _) zero_le_one (by rw [integral_const,hh,one_smul]) (ae_of_all _ hf.self_of_nhds)).shimmy ?_
  refine Eventually.of_forall fun i=>?_ ; unfold vote; rw [intervalIntegral.integral_of_le zero_le_one]; apply integral_congr_ae; filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioc (0:ℝ) 1) measurableSet_Ioc] with y hy using Eq.symm (Set.indicator_of_mem (Ioc_subset_Icc_self hy) _)
end ira
end YM.PhysicalNext.Repeat.Lantern
