import YM.RemainderComparison.Quartz.Clear
/-! # Tick through lifted Wilson jet. Vertical coefficients preserving active field.
   Analytic hypotheses from the exact Aux station. `pending` not projected at b≠0
   until after registration. This lemma foreign-safe derivative convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Trace
open Function Filter Set Metric MeasureTheory Wilson RG WilsonStartup.Change
open ConnectedActivityE6 Blaze Brush Push Push.Uniform PhysicalNext.Repeat
open scoped Topology BigOperators Classical ContDiff Interval
variable {E F X : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F]
variable {f g : ℝ×E→F} {x: E} {j i k m :ℕ}
section algebra
set_option maxHeartbeats 800000 in
lemma sharpen (h: Matches (k+m) f g (0,x)): Matches k (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) (0,x):=by
    induction m generalizing k with
    | zero => simp only [iteratedFDeriv_zero_eq_comp]; exact h.refl_comp (show ContDiffAt ℝ ω ((continuousMultilinearCurryFin0 ℝ (ℝ×E) F).symm) _ from (continuousMultilinearCurryFin0 ℝ (ℝ×E) F).symm.contDiff.contDiffAt)
    | succ m hm =>
        rw [iteratedFDeriv_succ_eq_comp_left,iteratedFDeriv_succ_eq_comp_left]; let L:= continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => ℝ×E) F; exact ((hm (k:=k+1) (by rw [show k+1+m=k+(m+1) by omega]; exact h)).ahead).refl_comp (u:= (L.symm)) (show ContDiffAt ℝ ω (L.symm) _ from (show ContDiff ℝ ω L.symm from by exact (LinearIsometryEquiv.contDiff (𝕜:=ℝ) (E:= ℝ×E →L[ℝ] (ℝ×E) [×m]→L[ℝ] F) (F:= (ℝ×E) [× (m+1)]→L[ℝ] F) L.symm)).contDiffAt)

lemma sharps (h:Matches (k+m) f g (0,x)): Matches k (plain f m) (plain g m) (0,x):=by
    let L:=ContinuousMultilinearMap.apply ℝ (fun _:Fin m=>ℝ×E) F (fun _=> ((1:ℝ),(0:E)))
    exact (sharpen h).refl_comp (u:=L) L.contDiff.contDiffAt
private lemma endured (f:ℝ×E→F) (h:ContDiffAt ℝ (↑ j) f (0,x)):∃ A : ℝ, ∀ᶠ y in 𝓝 ((0:ℝ),x), Brush j A 1 f y:=by
    let m:= ∑ i:Fin (j+1), normJ i.val f ((0:ℝ),x)
    have hp : Brush j m 1 f (0,x):=by
      refine Brush.offer.2 ⟨h,fun i hi=>?_⟩; exact Finset.single_le_sum (f:=fun i:Fin (j+1)=>normJ i.val f ((0:ℝ),x)) (a:=⟨i,Nat.lt_succ_iff.mpr hi⟩) (fun i _=> norm_nonneg _) (Finset.mem_univ _)
    exact ⟨m+1, nearby hp (lt_add_one _)⟩
end algebra
section pulse
variable [FiniteDimensional ℝ E] [SecondCountableTopology F] [CompleteSpace F]
local notation "win" => Icc (0:ℝ) 1
local notation "μo" => Measure.restrict (volume (α:=ℝ)) (Ioc (0:ℝ) 1)

def strolling (f: ℝ×E→F)(m:ℕ)(x:ℝ×E):= (win).indicator (Trace.toll f m x)
omit [CompleteSpace F] in
lemma casting (f:ℝ×E→F)(h:ContDiffAt ℝ (↑(j+(m+1))) f (0,x)): Meristem (strolling f m) ((0:ℝ),x) μo j:=by
    obtain ⟨A,hA⟩:= Trace.endured f h
    have hx : ∀ t:ℝ,crossing t (0,x)=(0,x):=by intro t; unfold crossing; simp
    have hp : ∀ᶠ y in 𝓝 ((0:ℝ),x), ∀ t∈win, Brush (j+(m+1)) A 1 f (crossing t y):=by
      obtain ⟨ε,hε,hB⟩:= Metric.mem_nhds_iff.mp hA; filter_upwards [Metric.ball_mem_nhds ((0:ℝ),x) hε] with y hy t ht
      apply hB; rw [Metric.mem_ball, dist_eq_norm,← hx t, ← map_sub]; exact lt_of_le_of_lt (le_trans ((crossing t (E:=E)).le_opNorm _) (mul_le_of_le_one_left (norm_nonneg _) (fare t ht))) (mem_ball_iff_norm.mp hy)
    letI : IsFiniteMeasure μo:= inferInstance
    refine Relative.test_domination (integrable_const A) ?_ ?_
    · filter_upwards [hp] with y hy t
      by_cases hh:t∈win
      · exact (rotate f m hh (hy t hh)).shimmy (Eventually.of_forall fun i=> indicator_of_mem hh _)
      exact (((Brush.certified zero_le_one (x:=y) (k:=j) (0:F)).climb (by rw [norm_zero]; exact hA.self_of_nhds.nonneg) le_rfl).shimmy (Eventually.of_forall fun _=> indicator_of_notMem hh _))
    borelize F
    filter_upwards [hp] with y hy
    apply Measurable.stronglyMeasurable
    apply measurable_of_restrict_of_restrict_compl (s:=win) measurableSet_Icc
    · rw [show (win).restrict (strolling f m y)=(win).restrict (toll f m y) from funext fun i=> indicator_of_mem i.2 _]
      apply Continuous.measurable; apply continuousOn_iff_continuous_restrict.mp; intro t ht
      apply ContinuousAt.continuousWithinAt; apply (show ContinuousAt (fun i:ℝ=> (1-i)^m) t by fun_prop).smul
      exact (plain_jet (hy t ht)).smooth.continuousAt.comp (f:=fun i:ℝ=> (i*y.1,y.2)) (show ContinuousAt (fun i:ℝ=> (i*y.1,y.2)) t from by fun_prop)
    rw [show ((win)ᶜ : Set ℝ).restrict (strolling f m y)=(fun _=>0) from funext fun i=> indicator_of_notMem i.2 _]
    exact measurable_const
omit [FiniteDimensional ℝ E] [SecondCountableTopology F] [CompleteSpace F] in
lemma explained (f:ℝ×E→F)(m:ℕ) : pending f m=fun x=> (m.factorial:ℝ)⁻¹ • ∫ t,strolling f m x t ∂(μo) :=by
    ext1 x; unfold pending; rw [intervalIntegral.integral_of_le zero_le_one]; apply congr_arg; apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioc (0:ℝ) 1) measurableSet_Ioc] with y hy using Eq.symm (indicator_of_mem (Ioc_subset_Icc_self hy) _)
lemma pContDiffAt (h:ContDiffAt ℝ (↑(j+(m+1))) f (0,x)) : ContDiffAt ℝ (↑j) (pending f m) (0,x):= by
    rw [explained]; exact (casting f h|>.calls).1.const_smul _
lemma balances (h:Matches (k+(m+1)) f g (0,x))(hi:i≤k): Trace.coefficient (pending f m) i x=Trace.coefficient (pending g m) i x:=by
    have hQ (t:ℝ) : Matches k (fun i=> toll f m i t) (fun i=> toll g m i t) ((0:ℝ),x):=by
      have hp:= Trace.sharps h; let L:=crossing (E:=E) t
      have hx:L (0,x)=(0,x):= by unfold L crossing; simp
      rw [← hx] at hp
      exact (hp.comp_refl L.contDiff.contDiffAt).refl_comp (u:=fun i:F=>(1-t)^m • i) (contDiffAt_const.smul contDiffAt_id)
    unfold Trace.coefficient; apply congr_arg; unfold Trace.plain; congr 1
    let W : Meristem (strolling f m) (0,x) μo k:= casting f (h.left.of_le le_top)
    let V : Meristem (strolling g m) (0,x) μo k:= casting g (h.right.of_le le_top)
    rw [explained,explained, iteratedFDeriv_const_smul_apply' (W.calls.1.of_le (Nat.cast_le.mpr hi)),iteratedFDeriv_const_smul_apply' (V.calls.1.of_le (Nat.cast_le.mpr hi)),(W.calls.2 i hi).2,(V.calls.2 i hi).2]; apply congr_arg; apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioc (0:ℝ) 1) measurableSet_Ioc] with t ht
    unfold JetF strolling; simp_rw [indicator_of_mem (Ioc_subset_Icc_self ht)]; exact (hQ t).jets i hi

omit [FiniteDimensional ℝ E] [SecondCountableTopology F] [CompleteSpace F] in
lemma negative (f:ℝ×E→F) (m:ℕ): pending (-f) m= -(pending f m):=by
    funext x; unfold pending toll plain; simp_rw [iteratedFDeriv_neg_apply]; simp
end pulse
section common
variable (h₁ : ContDiffAt ℝ (↑j) f (0,x)) (h₂ : ContDiffAt ℝ (↑j) g (0,x)) (hi:i≤ j)
-- separate - etc
include h₁ h₂ hi
lemma extracts_add : Trace.coefficient (f+g) i x= Trace.coefficient f i x + Trace.coefficient g i x:=by
   unfold Trace.coefficient Trace.plain; rw [iteratedFDeriv_add_apply (h₁.of_le (Nat.cast_le.mpr hi)) (h₂.of_le (Nat.cast_le.mpr hi))]; simp [smul_add]
omit h₁ h₂ hi in
lemma extracts_neg : Trace.coefficient (-f) i x= - Trace.coefficient f i x:=by unfold Trace.coefficient Trace.plain; rw [iteratedFDeriv_neg_apply]; simp
lemma extracts_sub : Trace.coefficient (f-g) i x= Trace.coefficient f i x - Trace.coefficient g i x:= by rw [sub_eq_add_neg,extracts_add (g:=-g) h₁ h₂.neg hi,extracts_neg,sub_eq_add_neg]
end common
end YM.RemainderComparison.Trace
