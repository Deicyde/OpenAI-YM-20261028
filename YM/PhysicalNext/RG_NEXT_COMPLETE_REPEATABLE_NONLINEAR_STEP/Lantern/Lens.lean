import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Blips
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Mesh
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Predict
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Spat

/-! # Rate vote invoice. Post-fineMonitor common film. Tail and parity paid separately.
 Operate for ∥b∥ < btop. C in this recipe not relative to changed schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {G : Gauge} {L : Side} {f g H : ℝ→ℝ}

lemma lumpRate (j : ℕ) (hp : Rate G L 0 f) (hr : Rate G L 0 g) : Rate G L 0 (fun x=> clump j (f x) (g x)) := by
  unfold clump; simp only [mul_one]; exact Brim.bell (hr.mul_left _) (Brim.prep ((Rate.const 1).add ((Rate.const 1).add hp)) j)
lemma fareRate (j : ℕ) (hp : Rate G L 0 f) (hr : Rate G L 0 g) : Rate G L 0 (fun x=> fee j (f x) (g x)) := by
  have hc := ((Rate.const (G:=G) (L:=L) 1).add hp).add hr; have h:= lumpRate j (hc.add hc) hp
  have he:= Brim.bell hr (Brim.bell hr h); exact ((hp.add hp).add (he.add he)).add (h.add h)
lemma hardly {t u : ℝ} (he : t ≤ 1) (h : u≤1/2) (hv : 1-t≤u) : ‖Real.log t‖ ≤ 2*u := by
  have ht:0<t:=by linarith
  rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos ht.le he)]
  have hp: t⁻¹ - 1 ≤ 2*u := by
    have hv' : 1/2 ≤ t := by linarith
    suffices he:t⁻¹ ≤ 2*u+1 by linarith
    apply (inv_le_iff_one_le_mul₀ ht).mpr; nlinarith only [hv',hv,he,mul_le_mul_of_nonneg_right hv' (show 0 ≤ u by linarith)]
  exact (Real.log_inv t) ▸ ((Real.log_le_sub_one_of_pos (inv_pos.mpr ht)).trans hp)

variable {ι : Type} [Fintype ι] [DecidableEq ι]
def cleanLog (ϕ ψ : E× Poll.Body ι→ℝ) (ρ : E→ Poll.Body ι) (M : E→ Matrix ι ι ℝ) (D : ℝ) := Real.log ∘ ratify ϕ ψ ρ M D
omit [FiniteDimensional ℝ E] in
lemma markArc {t p : ℝ} {f:ℝ×E→ℝ} {x : E} {j : ℕ} (h : Brush j p 1 f (t,x)) : Brush j p 1 (f ∘ arc t) x := by
  let P:= hook E; have hx i:arc t i=(t,0)+P i:=by simp [P]
  rw [show f ∘ arc t=(fun i=> f ((t,0)+P i)) from funext fun i=> congr_arg f (hx i)]; exact skim _ ((hx x) ▸ h) n_hook

theorem lookingGlass (G : Gauge) (L : Side) (j : ℕ) (Q f p w : ℝ→ℝ) (c d a m : ℝ) (hm : 0 < m) (hc : 0<c) (hD : 0<d) (ha : a<0)
    (hP : Rate G L 0 p) (hW : Rate G L a w) (hf : Rate G L a f) (h : Bolt G L Q) (e : ℝ) :
    ∃ B : ℝ→ℝ, Rate G L 0 B ∧ ∀ᶠ t in atTop, let z:=betaF G t L; let D:= d*Delay.fineMonitor G L t
       ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
          (ι:Type) [Fintype ι] [DecidableEq ι] (ϕ ψ:E× Poll.Body ι→ℝ) (ρ:E→Poll.Body ι) (M:E→ Matrix ι ι ℝ),
          (Fintype.card ι:ℝ) ≤ Q t → Golf ϕ ψ ρ M (j+2) D (w t) (f t) (p t) →
          (∀ x, ‖x‖ < w t → ∀ z:ι→ℝ,dotProduct z ((M x)⁻¹ *ᵥ z) ≤ c*dotProduct z z) →
          ∀ b x, 0<b → b<f t → ‖x‖+ z^(-m) < w t →
           let Φ := cleanLog ϕ ψ ρ M D; let Y := ratify ϕ ψ ρ M D (b,x)
           Real.exp (-1)*(1/2) ≤ Y ∧ Y ≤ Real.exp 1 ∧ Brush j (B t*b*b+z^e) 1 (Φ ∘ arc b) x := by
  let s := j+2
  have hs:1 ≤ s:=by unfold s; omega
  obtain ⟨C,hC,H⟩:=Brush.compact (f:=Real.exp) (k:=s) (s:=Icc (-1:ℝ) 1) isCompact_Icc fun x _=> Real.contDiff_exp.contDiffAt
  let a₀:=Real.exp (-1)*(1/2); have h₀ : 0 < a₀:=by unfold a₀; positivity
  obtain ⟨Y,hY,hR⟩:=Brush.compact (f:=Real.log) (k:=s) (s:=Icc a₀ (Real.exp 1)) isCompact_Icc fun x hx=> Real.contDiffAt_log.mpr (h₀.trans_le hx.1).ne'
  let D t:= d*Delay.fineMonitor G L t; let B t:=clump s (clump s (fee s (p t) (D t)) C) Y
  have hp := fareRate s hP (Rate.monitor.mul_left d); have he: Rate G L 0 B:= lumpRate s (lumpRate s hp (Rate.const _)) (Rate.const _)
  obtain ⟨q,hq⟩:= iteration G L j (m:=e) (d:=1) hm
  let r:=min (-1) (q-1)
  have hr : r<q:=by unfold r; have h:= min_le_right (-1:ℝ) (q-1); linarith
  have hr':r<0:=by unfold r; linarith [min_le_left (-1:ℝ) (q-1)]
  have hfar:= walls G L h hc hD r
  have hw:= ((Brim.absolut hp).mul (hW.add hf)).below (by linarith) 1 zero_lt_one
  refine ⟨B,he,?_⟩; filter_upwards [hq,hfar,hw, ((Rate.power (G:=G) (L:=L) (a:=r)).mul_left 2) q hr, (Rate.power (G:=G) (L:=L) (a:=r)).below hr' (1/2) (by norm_num), he 1 zero_lt_one, Delay.shift_pos G L] with t hx hh hX hy hd he ht z y E _ _ _ ι _ _ ϕ ψ ρ M hl hu hv b x hb hB ha Φ Z
  let μ i:= sweep (M i)⁻¹
  have hk (i:E) (hi:‖i‖ < w t) :=hh _ (M i)⁻¹ hl (hu.gram _ hi).1.inv (hv _ hi)
  have h₀x: ‖(0:E)‖< w t:=by rw [norm_zero]; exact hu.pos
  have hS (i:E) (hi:‖i‖ < w t): (1/2:ℝ) ≤ (μ i).real (closedBall (0:Poll.Body ι) y) := by
    have he:=hk i hi; change 1 - (μ i).real (closedBall (0:Poll.Body ι) y) ≤ _ at he; linarith only [he,hd,le_abs_self (z^r)]
  have hm : fee s (p t) y*max (w t) (f t)≤1 := by
    apply le_trans (b:=|fee s (p t) y| * (w t+f t))
    · exact mul_le_mul (le_abs_self _) (max_le (le_add_of_nonneg_right hu.pos'.le) (le_add_of_nonneg_left hu.pos.le)) (hu.pos.le.trans (le_max_left ..)) (abs_nonneg _)
    exact (le_abs_self _).trans hX
  let g x':= Φ ∘ arc (A:=E) x'
  have ht₀ t₀ (ht₁:t₀∈closedBall x (z^(-m))): ‖t₀‖ < w t:= by
    have hh : ‖t₀-x‖ ≤ z^(-m):=mem_closedBall_iff_norm.mp ht₁; exact (norm_le_norm_add_norm_sub' _ _).trans_lt ((add_le_add_right hh _).trans_lt ha)
  have ht' (y:E) (l:ℝ) (hl : ‖l‖<f t) (h : ‖y‖ < w t) : Brush s (B t) 1 Φ (l,y):= lifted _ hu h hl hs hm H hC.le hR (hS 0 h₀x)
  have hQ := hx E ℝ (g 0) x (fun i hi=> by
    have he' := markArc (ht' i 0 (by rw [norm_zero]; exact hu.pos') (ht₀ i hi))
    exact (he'.smaller (by unfold s; omega : j+1 ≤ s)).climb ((le_abs_self _).trans he) le_rfl) fun i hi=>by
    change ‖Real.log (ratify ϕ ψ ρ M y (0,i))‖≤_
    rw [coming _ hu i (ht₀ i hi)]
    have hz : z^r≤1/2 := (le_abs_self _).trans hd
    apply (hardly (show (μ i).real (closedBall (0:Poll.Body ι) y)≤1 from (measureReal_mono (subset_univ _) (measure_ne_top (sweep _) _)).trans_eq probReal_univ) hz (hk i (ht₀ _ hi))).trans ((le_abs_self _).trans hy)
  have hZ : 0<z:=ht; have hA : ‖x‖ < w t:= (le_add_of_nonneg_right (by positivity)).trans_lt ha
  have heV := shoots Φ j x b hb (funext fun x=> congr_arg Real.log (congr_fun (rolls_even ϕ ψ ρ M y (hu.gram _ h₀x).1) x)) (fun t' hu=> ht' x _ (hu.trans_lt hB) hA)
  have hβ:‖b‖<f t:=by rwa [Real.norm_of_nonneg hb.le]
  have h:= temperature y (x:=(b,x)) hu hA hβ hs hm (burs y (x:=(b,x)) hu hA hβ hs hm H hC.le|>.2) (hS 0 h₀x)
  exact ⟨h.1,h.2,(heV.gathering hQ).shimmy (Eventually.of_forall fun y=> (sub_add_cancel (g b y) (g 0 y)).symm)⟩
end YM.PhysicalNext.Repeat.Lantern
