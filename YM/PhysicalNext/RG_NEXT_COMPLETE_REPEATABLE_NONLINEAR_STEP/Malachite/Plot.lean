import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Grain

/-!
# Brush transfer on every ordered journey about its *actual* address

Normalize by Beer scale. Needed also for companion jets. Uses θ sharp at
μ difference, aperture. Not guessing Fee for locality/masks around argument.
V open germ through all orders for numerical blocks. Supports size criteria
to bound λ charged later. Here choose λ dominates crop and polyradic A
jets, no tiny markers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Placement
open WardBin.Lies Offset Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {X : Coat T F} {I : Type} {Y : Support c} {E : Support f} {V : Config G c}
variable {ι κ J W Y : Type} [NormedAddCommGroup ι] [NormedSpace ℝ ι] [NormedAddCommGroup κ] [NormedSpace ℝ κ]
variable [NormedAddCommGroup J] [NormedSpace ℝ J]

section temper
variable {n : ℕ} {f : ι → κ} {u : J→ι} {x : J} {a C r t : ℝ}
structure Tracks (u : J → ι) (x : J) (n : ℕ) (r : ℝ) : Prop where
  hp : 0< r
  smooth : ContDiffAt ℝ n u x
  inside : ‖u x‖≤ r
  hops (i : ℕ) : 1 ≤ i → i ≤ n → normJ i u x≤ r^i
-- Normalize λ
abbrev sewn (v M:ℝ) (k:ℕ) := (k.factorial:ℝ)*M*(1+v)^k
lemma funded (h : Tracks u x n r) (ht : Brush n C 1 (fun y : ι=> f (r • y)) (r⁻¹ • u x)) (hr : r ≤ 1) : Brush n (sewn 1 C n) 1 (fun y=> f (u y)) x := by
  let H y:= r⁻¹ • u y
  have hf : u=fun y=> r • H y:= funext fun i=> by unfold H; rw [smul_smul,mul_inv_cancel₀ h.hp.ne',one_smul]
  have hF : ContDiffAt ℝ n H x:= h.smooth.const_smul _
  have hc i (hi : 1 ≤ i) (hp : i ≤ n) : normJ i H x ≤ (1:ℝ)^i := by
    unfold H; change ‖iteratedFDeriv ℝ i (r⁻¹ • u) x‖ ≤ _; rw [iteratedFDeriv_const_smul_apply (h.smooth.of_le (Nat.cast_le.mpr hp)),norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr h.hp.le)]
    apply (mul_le_mul_of_nonneg_left (h.hops i hi hp) (inv_nonneg.mpr h.hp.le)).trans
    rw [one_pow]; exact (mul_le_mul_of_nonneg_left (pow_le_of_le_one h.hp.le hr (by omega)) (inv_nonneg.mpr h.hp.le)).trans_eq (inv_mul_cancel₀ h.hp.ne')
  simpa only [← show (fun y=>r • H y)=u from hf.symm] using (Brush.compound (f:=H) ht (d:=1) hF zero_le_one hc).trim

lemma dimming (h : Tracks u x n r) (B : Portrait f 0 n a r C) (hr : r≤1) (hp : 2 ≤ n) : Brush n (sewn 1 (C*(a+r)*r+C*r^2) n) 1 (fun x=> f (u x)) x := by
  have hx := B.uniform (u x) h.inside
  apply funded h _ hr
  let g := r • ContinuousLinearMap.id ℝ ι
  have he : ‖g‖≤ r := by unfold g; rw [norm_smul, Real.norm_of_nonneg h.hp.le]; exact mul_le_of_le_one_right h.hp.le ContinuousLinearMap.norm_id_le
  have hh : g (r⁻¹ • u x)=u x:= by change r • (r⁻¹ • u x)=_; rw [smul_smul,mul_inv_cancel₀ h.hp.ne',one_smul]
  have hk : ContDiffAt ℝ (n:ℕ∞ω) f (g (r⁻¹ • u x)):= hh.symm ▸ hx.smooth
  change Brush n _ 1 (f ∘ g) (r⁻¹ • u x)
  refine settled.mpr ⟨hk.comp _ g.contDiff.contDiffAt, fun i hi=>?_⟩
  have hC := hx.nonneg
  have hy:= B.zeroth_charge hp h.inside le_rfl; rw [_root_.zero_apply,sub_zero] at hy
  rcases i with _|i
  · rw [norm_iteratedFDeriv_zero,Function.comp_apply,hh]; exact hy.trans (le_add_of_nonneg_right (by positivity))
  rw [Push.Uniform.iter_lin_at (hk.of_le (Nat.cast_le.mpr hi)), hh]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rcases i with _|i
  · rw [norm_iteratedFDeriv_one, pow_one]; have hf := B.first_charge hp h.inside; rw [sub_zero] at hf
    have hf' : ‖fderiv ℝ f (u x)‖ ≤ C*(a+r) := hf.trans (mul_le_mul_of_nonneg_left (add_le_add_right h.inside _) hC)
    exact (mul_le_mul hf' he (norm_nonneg _) ((norm_nonneg _).trans hf')).trans (le_add_of_nonneg_right (by positivity))
  exact (mul_le_mul (hx.pay _ hi) ((pow_le_pow_left₀ (norm_nonneg _) he _).trans (pow_le_pow_of_le_one h.hp.le hr (show 2 ≤ i+2 by omega)))
    (pow_nonneg (norm_nonneg _) _) hC).trans (le_add_of_nonneg_left ((norm_nonneg _).trans hy))
-- covariance difference order 1 only, incl value
lemma inclined (h : Tracks u x n r) (hr : r≤1) (he : ∀ v : ι, ‖v‖ ≤ r → Through n f v C) (hg : ‖f 0‖ ≤ t) (hp : 1≤n) :
    Brush n (sewn 1 (t+C*r) n) 1 (fun x=> f (u x)) x := by
  have hx := he (u x) h.inside; have hz := hx.nonneg; have hv := (norm_nonneg _).trans hg
  apply funded h _ hr
  let g := r • ContinuousLinearMap.id ℝ ι
  have hG : ‖g‖≤ r := by unfold g; rw [norm_smul, Real.norm_of_nonneg h.hp.le]; exact mul_le_of_le_one_right h.hp.le ContinuousLinearMap.norm_id_le
  have hh : g (r⁻¹ • u x)=u x:= by change r • (r⁻¹ • u x)=_; rw [smul_smul,mul_inv_cancel₀ h.hp.ne',one_smul]
  have hk : ContDiffAt ℝ (n:ℕ∞ω) f (g (r⁻¹ • u x)):= hh.symm ▸ hx.smooth
  change Brush n _ 1 (f ∘ g) _
  refine settled.mpr ⟨hk.comp _ g.contDiff.contDiffAt, fun i hi=>?_⟩
  rcases i with _|i
  · rw [norm_iteratedFDeriv_zero,Function.comp_apply,hh]
    have hy := Convex.norm_image_sub_le_of_norm_fderiv_le (f:=f) (s:=closedBall (0:ι) r) (fun v hv=> (he v (mem_closedBall_zero_iff.mp hv)).smooth.differentiableAt (by exact_mod_cast (by omega:n≠0)))
      (fun v hv=> price_one (he v (mem_closedBall_zero_iff.mp hv)) hp) (convex_closedBall _ _) (mem_closedBall_self h.hp.le) (mem_closedBall_zero_iff.mpr h.inside)
    rw [sub_zero] at hy
    calc
      _ ≤ ‖f (u x)-f 0‖ + ‖f 0‖ := by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (f (u x)) (f 0) 0
      _ ≤ _ := (add_le_add (hy.trans (mul_le_mul_of_nonneg_left h.inside hz)) hg).trans_eq (add_comm ..)
  rw [Push.Uniform.iter_lin_at (hk.of_le (Nat.cast_le.mpr hi)),hh]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (mul_le_mul (hx.pay _ hi) ((pow_le_pow_left₀ (norm_nonneg _) hG _).trans (pow_le_of_le_one h.hp.le hr (by omega))) (pow_nonneg (norm_nonneg _) _) hz).trans
    (le_add_of_nonneg_left hv)
end temper

-- tracks purchased regardless of output V; no Measure substitutions from size alone
section canvas
variable {P : BudgetPoint} {n j r : ℕ} {o p : Site c} {g : Site c → G.El} {C K : ℝ} (h : Canvas P o r V g n C) (u : Slab G c j) (hC : 1 ≤ C)
    (hk : loom P r C*spine P.power o p ≤ K)
include h hk hC
lemma onJourney (hp : j≤ n) (he : ∀ i, P.dirBound p (u i)) : Tracks (launch V o r g u) 0 n K := by
  have ht := P.threshold_pos
 
  have he' := spine_pos P.power o p
  have h' := (lt_of_lt_of_le (show 0 < loom P r C*spine P.power o p by unfold loom; positivity) hk)
  refine ⟨h',h.ready _,?_,fun i hi hv=> Planned.AtomRegular.op_le_of_unit (pow_nonneg h'.le i) (fun v hv' => ?_)⟩
  · rw [launch_zero]; exact ((h.paid hC).trans (le_mul_of_one_le_right ((norm_nonneg _).trans (h.paid hC)) (show 1≤ spine P.power o p by unfold spine; exact one_le_pow₀ (by simp)))).trans hk
  refine (h.cost he hC hp hv hi v hv').trans ?_; rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity [show 0≤loom P r C by unfold loom; positivity]) hk _
end canvas
end YM.PhysicalNext.Repeat.Malachite
