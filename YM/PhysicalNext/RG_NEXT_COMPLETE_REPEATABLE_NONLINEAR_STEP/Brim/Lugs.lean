import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Pier
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Citrine
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Commission

/-!
# Toll buds on OAuth; issue numeric ceilings separately

Expand ANY labels kept. Use E6 feedback on physical repetition;
 smooth α profile at both ends when cost derivatives of broad factor.
 Ledger supports even mandatory flags kept throughout; no substitutions
from other S readings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n : ℕ} {L : Side}
variable {d A t C' w M N z β W k ε J' L₀ X' : ℝ}

section arc
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E→ Config G c} {x : E} (X : Coat T F)
    {I:Type} [Fintype I] [DecidableEq I] (i : ℕ) (R : Rep G f) (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I)
    (s : Prices G I) (κ q : Chi)

lemma pane6 (hv : (Fintype.card I:ℝ) ≤ N) (hg : 0 ≤ t) (hp : ∀ i, Brush n 1 t (fun y=> X.cone (2*z) (steer X d (worldZ X R.beta (spied X a s)) (Z y)) i) x)
    : Brush n ((1+N*t)^n) 1 (fun y=> coin X i R a d R.beta z (Z y) s) x := by
  have he := Brush.all_prod Finset.univ _ _ _ (fun (i:I) (_:i∈Finset.univ)=> hp (a.address i))
  simp only [Finset.prod_const_one,Finset.sum_const,nsmul_eq_mul, Finset.card_univ] at he
  unfold Coat.cone at he; simp_rw [heard X a s] at he
  exact (he.climb le_rfl (mul_le_mul_of_nonneg_right hv hg)).trim.climb (by rw [one_mul]) le_rfl

omit [DecidableEq I] in
lemma pitch9 (q : Chi) (b : ℝ) (hp : ∀ k, Brush n M 1 (offsetRun X a k q b 1 ∘ Z) x)
    (h : (gStep β)⁻¹ ≤ X') (hg : 0<β) :
    Moves x n (fun z=>reading6 X (Z z) a s d β - reading9 X (Z z) a s q b d β) (X'*M) := by
  let g:=gStep β; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr hg); intro u
  let f:= fun y=> (reading6 X (Z y) a s d β-reading9 X (Z y) a s q b d β) u; let T:= offsetRun X a u.1 q b 1
  have ht (y:E) : f y=g⁻¹*T (Z y) u.2 := by
    unfold f reading6 reading9; rw [sub_add_cancel_left]; unfold distance9; change -(g⁻¹ • (-T (Z y))) u.2 = _ -- edit
    simp
  have hh:= ((colorEvaluated u.2 (hp u.1)).smul g⁻¹)
  refine (hh.climb ?_ le_rfl).shimmy (Eventually.of_forall ht)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hg.le)]; exact mul_le_mul_of_nonneg_right h (hp u.1).nonneg

-- smooth toll metric for Γ
omit [DecidableEq I] in
lemma kiss (hv : ∀ x∈Set.Icc (0:ℝ) 4, Brush n t 1 κ.read x) {w : E → G.Color} (hp : Brush n M 1 w x) (hd : 0<d) (hX : d⁻¹ ≤ X') :
    let u:= X'*M
    Brush n 1 ((1+n.factorial*t)*((1+u*u)*(1+1))) (fun y=> broad κ d (w y)) x := by
  intro u
  by_cases he: ‖w x‖≤ 2*d
  · refine (plateauChi κ hp hv hd he).climb le_rfl ?_; have ht : 0≤t:= (hv _ (Set.left_mem_Icc.mpr (by norm_num))).nonneg; have hA:=hp.nonneg; unfold u; have hu : 0≤ X':= (inv_nonneg.mpr hd.le).trans hX; gcongr
  have ht : 0≤t:= (hv _ (Set.left_mem_Icc.mpr (by norm_num))).nonneg
  refine Brush.zi (?_) zero_le_one (by positivity [mul_self_nonneg u])
  filter_upwards [hp.smooth.continuousAt.norm.eventually (lt_mem_nhds (lt_of_not_ge he))] with y hy
  by_contra ht; exact (broad_span κ hd _ ht).not_gt hy

omit [DecidableEq I] in
lemma pane9 (hv : ∀ x∈Set.Icc (0:ℝ) 4, Brush n t 1 κ.read x) (D' : Record) (b : ℝ) {h₀ : ℝ}
    (ht : 0<R.beta) (hh : Moves x n (fun y=> reading9 X (Z y) a s q b d R.beta) M) (hM : 0≤M) (hn : (Fintype.card I:ℝ) ≤ N)
    (he : (D'.ε*R.p.threshold/gStep R.beta/4)⁻¹ ≤ h₀) :
    let u:= h₀*((Fintype.card G.ColorIndex:ℝ)*M)
    Brush n ((1+N*((1+n.factorial*t)*((1+u*u)*(1+1))))^n) 1 (fun y=> veil X a q κ b D' R.p d R.beta s (Z y)) x := by
  intro u
  let g:=gStep R.beta; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr ht); let f y:= reading9 X (Z y) a s q b d R.beta
  have hk i:Brush n ((Fintype.card G.ColorIndex:ℝ)*M) 1 (fun y=> tape (f y) i) x := tie G _ hM zero_le_one (fun j=> hh (i,j))
  have hs := Brush.all_prod Finset.univ _ _ _ (fun (i:I) (_:i∈Finset.univ)=> kiss κ hv (hk i) (show 0 < D'.ε*R.p.threshold/gStep R.beta/4 from by have he : 0< gStep R.beta:= hg; have hf:=D'.guards; have h:= R.p.threshold_pos; positivity) he)
  simp only [Finset.prod_const_one,Finset.card_univ,Finset.sum_const,nsmul_eq_mul] at hs
  have ht : 0 ≤ t:= (hv _ (Set.left_mem_Icc.mpr (by norm_num))).nonneg
  exact (hs.climb le_rfl (mul_le_mul_of_nonneg_right hn (show 0≤ (1+n.factorial*t)*((1+u*u)*(1+1)) from by positivity [mul_self_nonneg u]))).trim.climb (by rw [one_mul]) le_rfl
end arc
end YM.PhysicalNext.Repeat.Brim
