import YM.AnalyticNext.QUARTIC_MATCH.Exchange
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-!
# Area integral along bulk sign axis

Bound unscaled derivatives when sizes fit inside t horizon. FTC names.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory
open ConnectedActivityE6 Blaze Brush
open scoped Topology ContDiff BigOperators Classical Interval ENNReal
variable {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {j k : ℕ} {u d v a D : ℝ} {f : E→F} {g : F→Y} {x y : E}
lemma norm_F (h : Brush (j+1) v 1 f x) : Brush j v 1 (fderiv ℝ f) x := Brush.offer.2 ⟨h.smooth.fderiv_right (by push_cast; simp), fun i hi=> norm_iteratedFDeriv_fderiv.trans_le ((Brush.offer.1 h).2 _ (by omega))⟩
lemma beam_at (w : E) : ‖(ContinuousLinearMap.apply ℝ F) w‖ ≤ ‖w‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i=> (i.le_opNorm _).trans_eq (mul_comm _ _)
def scratch (z : E) (u : E→ℝ) (x : E) := fderiv ℝ (fderiv ℝ u) x z z -- def edit
def inflect (f : E→ℝ) (x z : E) (r : ℝ) := (1-r)*scratch z f (x+r • z)
lemma residue (f : E→ℝ) (x z : E) (h : ∀ t : ℝ, t∈Icc (0:ℝ) 1→ ContDiffAt ℝ 2 f (x+t • z)) :
    f (x+z)- f x-fderiv ℝ f x z = ∫ t in (0:ℝ)..1, inflect f x z t := by
  let y (t:ℝ):=x+t•z; let W t:= fderiv ℝ f (y t) z; let M t:= (1-t)*W t+f (y t)
  have hy (t:ℝ):HasDerivAt y z t:= by simpa only [one_smul] using (((hasDerivAt_id' t).smul_const z).const_add x)
  have he t (he:t∈uIcc (0:ℝ) 1) : HasDerivAt M (inflect f x z t) t := by
    rw [uIcc_of_le zero_le_one] at he; have hg := h t he
    have hb : DifferentiableAt ℝ (fderiv ℝ f) (y t):= (hg.fderiv_right (m:=1) (by norm_num)).differentiableAt (by simp)
    have hD : HasDerivAt W (scratch z f (y t)) t:= ((ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt).comp_hasDerivAt t (hb.hasFDerivAt.comp_hasDerivAt t (hy t))
    have hx := ((((hasDerivAt_id' t).const_sub 1).mul hD).add ((hg.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hy t)))
    unfold inflect; convert hx using 1 <;> first| rfl| (unfold W y; ring)
  have ht : ContinuousOn (inflect f x z) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]; intro t ht; apply ContinuousAt.continuousWithinAt; apply (continuousAt_const.sub continuousAt_id).mul
    change ContinuousAt (fun i=> (fderiv ℝ (fderiv ℝ f) (y i)) z z) t
    let P:ContinuousAt (fderiv ℝ (fderiv ℝ f)) (y t):= ((h t ht).fderiv_right (m:=1) (by norm_num)|>.fderiv_right (m:=0) (by simp)).continuousAt
    exact ContinuousAt.clm_apply (ContinuousAt.clm_apply (P.comp (hy t).continuousAt) continuousAt_const) continuousAt_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt he (ht.intervalIntegrable)]; dsimp only [M,W,y]; simp; ring

-- variation estimates

def clump (j : ℕ) (p v : ℝ) := j.factorial*v*(1+(1+p)*1)^j
lemma composite (p : Brush j u 1 f x) (t : Brush j v 1 g (f x)) : Brush j (clump j u v) 1 (g ∘ f) x := (p.pine t).trim
lemma utilizes (p : Brush j v 1 f x) (L : F →L[ℝ] Y) (h : ‖L‖ ≤ d) : Brush j (d*v) 1 (L ∘ f) x := p.report _ h
lemma grade (q : F→ℝ) {z : F} (hz : ‖z‖ ≤ D) (ht : Brush (j+2) v 1 q (f x)) (hp : Brush j d 1 f x) : Brush j (D*(D*clump j d v)) 1 (scratch z q ∘ f) x :=
    utilizes (utilizes (composite hp (norm_F (norm_F ht))) (ContinuousLinearMap.apply ℝ _ z) ((beam_at _).trans hz)) (ContinuousLinearMap.apply ℝ _ z) ((beam_at _).trans hz)
end YM.PhysicalNext.Repeat.Lantern
