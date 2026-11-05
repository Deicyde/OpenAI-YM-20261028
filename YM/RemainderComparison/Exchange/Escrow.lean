import YM.RemainderComparison.Exchange.Queue

/-!
 # Reexpand logs, inverse and products with uniform actual positivity.
 `plant` sets common real window and cap, *not* under separate coupling
 choices. Applied to models with normalized kernel denominator after slice
 treatment. Model scalar (k=0) fixed. No expansion of vacuum scalar outside
 when onerous.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Exchange
open Function Filter Set Metric MeasureTheory Finset Germ Trace
open Lattice RG Push.AbsoluteSums Pressure Next.Scheduling
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat Lantern
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {j k n : ℕ}
variable {G : Gauge} {L : Side} {q p : ℝ→ℝ} {d v u C : ℝ}
section point
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F:Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ℝ×E→F} {P:E→F} {x:E} (h : Queue U P d x v u j k C)
include h
lemma graduation {z : ℝ×E} (hp:z∈Germ.patch E v u) :
    ‖U z - U (0,z.2)‖ ≤ C*v := by
  let s:= Germ.patch E v u; have hs : Convex ℝ s:= (convex_ball (0:ℝ) v).prod (convex_ball (0:E) u); let i:=((0:ℝ),z.2)
  have hh : ‖z-i‖ ≤ v:= max_le (show ‖z.1-0‖ ≤ v from sub_zero z.1 |>.symm ▸ (((patch_test ..).1 hp).1.le))
    (by change ‖z.2-i.2‖ ≤ _; rw [show z.2-i.2=0 from sub_self z.2,norm_zero]; exact (patch_zero hp).1.le)
  have hg : (1:ℕ)≤j+(k+1):= by omega
  have hy p (hp:p∈s):= (h.scope p hp).smaller hg
  refine (hs.norm_image_sub_le_of_norm_fderiv_le (fun p hp=> (hy p hp).smooth.differentiableAt (by simp))
    (fun p hp=> (norm_iteratedFDeriv_one ..).symm.trans_le (show normJ 1 U p ≤ C from (Brush.offer.mp (hy p hp)).inside 1 le_rfl)) (show i∈s from (patch_test ..).2 ⟨norm_zero.trans_lt (patch_zero hp).1,((patch_test ..).1 hp).2⟩) hp).trans (mul_le_mul_of_nonneg_left hh h.cost)
end point

lemma product_allow (j k:ℕ) (hp:Reserve G L p) (hq: Reserve G L q): Reserve G L fun x=> Queue.productPrice j k (p x) (q x) :=
    (((hp.mul hq).mul (Reserve.const _))).add ((((hp.mul (hq.add hq)).mul (Reserve.const _))).add ((hp.mul hq).mul (Reserve.const _)))

lemma inv_allow (j k:ℕ) (hp:Reserve G L p) (C:ℝ): Reserve G L fun x=> inverse_fee j k (p x) C:= by
  have hx:=Reserve.comp (j+(k+1)) hp (Reserve.const C)
  exact hx.add (((((Reserve.comp j (hp.add hp) (Reserve.const _)).mul hp).mul (Reserve.const _)).mul hx).mul (Reserve.const _))
lemma log_allow (j k :ℕ) (hp:Reserve G L p) (C D m:ℝ): Reserve G L fun x=> lf j k (p x) C D m := by
  have hx:=Reserve.comp (j+(k+1)) hp (Reserve.const D)
  exact hx.add (Reserve.mul (Reserve.const m) ((hp.mul (Reserve.comp _ hp (Reserve.const _))).mul (Reserve.const _)))
lemma plant (j k:ℕ) (hp:Reserve G L p) : ∃ K : ℝ→ℝ, Reserve G L K ∧ ∀ᶠ x in atTop, let v:=Access.apron G L x
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (u:ℝ) (U:ℝ × E → ℝ) (P:E→ℝ) (w:E) (d:ℝ),
      Queue U P d w v u j k (p x) → (∀ x : E, ‖x‖<u → U (0,x)=1) →
        ((P w)∈ Set.Icc (1/4:ℝ) 3) ∧ (∀ z∈Germ.patch E v u,U z∈Set.Icc (1/2:ℝ) 2) ∧
        Queue (Real.log ∘ U) (Real.log ∘ P) d w v u j k (K x) ∧
        Queue (fun y=> (U y)⁻¹) (fun y=> (P y)⁻¹) d w v u j k (K x) := by
  let J:=j+(k+1); obtain ⟨C,hC,hf⟩:=Brush.compact (k:=J) (f:=fun a:ℝ=> a⁻¹) (s:=Set.Icc (1/4:ℝ) 3) isCompact_Icc (fun i hi=> contDiffAt_id.inv (show i≠0 from ne_of_gt (lt_of_lt_of_le (by norm_num) hi.1)))
  obtain ⟨D,hD,hg⟩:=Brush.compact (k:=J) (f:=Real.log) (s:=Set.Icc (1/2:ℝ) 2) isCompact_Icc (fun i hi=> Real.contDiffAt_log.mpr (show i≠0 from ne_of_gt (lt_of_lt_of_le (by norm_num) hi.1)))
  let p' x:= inverse_fee j k (p x) C
  obtain ⟨A⟩:= Prism.anthems j; let q' x:= lf j k (p x) C D A.logE
  have he:= Access.rates_apron (G:=G) (L:=L); have hy := (he.mul hp.rate)
  have hΛ := (Reserve.comp J hp (Reserve.const C)).rate; have hz:=((hy.mul hΛ).mul_right ((3:ℝ)^j))
  refine ⟨fun i=> q' i+p' i, (log_allow j k hp C D A.logE).add (inv_allow j k hp C),?_⟩
  filter_upwards [hz.below (by norm_num) _ (by norm_num : 0 < (1:ℝ)/4),hy.below (by norm_num) _ (by norm_num : 0 < (1:ℝ)/4), he.below (by norm_num) _ zero_lt_one] with x hx hy he v E _ _ b U P w d hp h₀
  have hf' : 0<d:=hp.coupling; have hv : d ≤ v:= (le_abs_self _).trans (((patch_test ..).1 hp.site).1.le)
  have hd:d ≤ 1:= hv.trans ((le_abs_self _).trans he); have hg' : d^(k+1) ≤ v:= ((pow_le_pow_of_le_one hf'.le hd (show 1≤k+1 by omega)).trans (by rw [pow_one])).trans hv
  let v':= d^(k+1)*p x; have hh: v' ≤ 1/4 := (mul_le_mul_of_nonneg_right hg' hp.cost).trans ((le_abs_self _).trans hy)
  have ht: v' * clump J (p x) C *3^j ≤ 1/2 := by
    have h : 0 ≤ clump J (p x) C:= by have h:=hp.cost; unfold clump; positivity
    exact ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg' hp.cost) h) (pow_nonneg (by norm_num) _)).trans ((le_abs_self _).trans hx)).trans (by norm_num)
  have hX (z) (hz:z∈Germ.patch E v b) : U z∈Set.Icc (1/2:ℝ) 2:= by
    have hw:= graduation hp hz; rw [h₀ z.2 ((patch_test ..).1 hz).2, mul_comm (p x)] at hw
    obtain ⟨ha,hb⟩:= abs_le.mp (hw.trans ((le_abs_self _).trans hy)); constructor <;> linarith
  have hL:= logs hp hX hf hh ht A hg hd; have hI:=inverse_at hp hX hf hh hd
  exact ⟨chase hp hX hh,hX,hL.grows (le_add_of_nonneg_right hI.cost),hI.grows (le_add_of_nonneg_left hL.cost)⟩
end YM.RemainderComparison.Exchange
