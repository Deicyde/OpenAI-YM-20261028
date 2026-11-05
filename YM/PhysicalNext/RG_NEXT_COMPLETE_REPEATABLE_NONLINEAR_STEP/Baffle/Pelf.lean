import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Osmote
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Plot
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Line

/-!
# Gate lemmas for parameter-differentiation on compact struts

No joint continuity of payoff owed t(TAG); prove Meristem including arbitrary
 bounded measurable payoff parameter on the closed W neighborhood where test
 may ever fire. Local curtain support; includes integrability proof needed when
 equating two collars on intersecting V charts. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Set MeasureTheory ConnectedActivityE6 ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

section generic
variable {E Z F A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace A]
variable {D : ℝ} {v : E→ A → F} {f : E → Z → F} {S : Set Z} {h : A→ Z} {p : E} {n : ℕ}

lemma caisson (μ : Measure A) [IsFiniteMeasure μ] (hH : Measurable h) (hh : IsCompact S)
    (hf : ∀ y∈S, ContDiffAt ℝ (↑n) (uncurry f) (p,y)) (hg : ∀ᶠ x in 𝓝 p, ∀ y, v x y= S.indicator (f x) (h y)) :
    Meristem v p μ n := by
  have ht : IsOpen {z:E×Z| ContDiffAt ℝ (↑n) (uncurry f) z} := isOpen_iff_mem_nhds.mpr fun z hz=> by exact ContDiffAt.eventually (show ContDiffAt _ _ _ _ from hz) (by simp)
  obtain ⟨U,K,hU,hK,hp,hS,hF⟩:= generalized_tube_lemma (isCompact_singleton (x:=p)) hh ht (show {p}×ˢ S ⊆ _ from by rintro ⟨a,b⟩ ⟨rfl,hb⟩; exact hf b hb) -- edit
  obtain ⟨a,ha,hA⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (Filter.inter_mem (hU.mem_nhds (hp (mem_singleton _))) hg)
  let T:= closedBall p a; let B:= ball p a
  have he (x:E) (hx:x∈T) (y : Z) (hy:y∈S) : ContDiffAt ℝ (↑n) (uncurry f) (x,y) := hF ⟨(hA hx).1, hS hy⟩
  have hz (x:E) (hx:x∈B) (y) : (fun x=>v x y)=ᶠ[𝓝 x] fun x=> S.indicator (f x) (h y) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with b hb; exact (hA (ball_subset_closedBall hb)).2 y
  have he' y x (hx:x∈B):ContDiffAt ℝ (↑n) (fun x=> v x y) x := by
    by_cases hy : h y∈S
    · refine ContDiffAt.congr_of_eventuallyEq ((he x (ball_subset_closedBall hx) (h y) hy).comp (f:=fun x:E=> (x,h y)) x (contDiffAt_id.prodMk contDiffAt_const)) ((hz x hx y).mono (fun x hx => ?_)); rw [hx]; exact indicator_of_mem hy _
    refine (contDiffAt_const (c:=(0:F))).congr_of_eventuallyEq ((hz x hx y).mono fun x hx=> ?_); rw [hx]; exact indicator_of_notMem hy _
  refine ⟨B,ball_mem_nhds _ ha,ae_of_all _ he',fun i hi=>?_⟩
  let W z := ContinuousMultilinearMap.compContinuousLinearMapL (F:=F) (fun _ : Fin i=> ContinuousLinearMap.inl ℝ E Z) (iteratedFDeriv ℝ i (uncurry f) z)
  have hw : ContinuousOn (fun z:E×Z=>JetF f i z.1 z.2) (T×ˢ S) := by
    have hl : ContinuousOn W (T×ˢ S):= fun (x,y) hx=> (ContinuousAt.comp (g:=⇑(ContinuousMultilinearMap.compContinuousLinearMapL (F:=F) (fun _ : Fin i=> ContinuousLinearMap.inl ℝ E Z))) (by fun_prop) ((he x hx.1 y hx.2).continuousAt_iteratedFDeriv (Nat.cast_le.mpr hi))).continuousWithinAt
    exact hl.congr fun (x,y) hx=> sprains ((he x hx.1 y hx.2).of_le (Nat.cast_le.mpr hi))
  obtain ⟨f',hW⟩:= ((isCompact_closedBall p a).prod hh).bddAbove_image hw.norm
  have hd (x:E) (hx:x∈B) y: JetF v i x y=S.indicator (JetF f i x) (h y) := by
    unfold JetF; rw [(hz x hx y |>.iteratedFDeriv ℝ i).eq_of_nhds]
    by_cases hy : h y∈S
    · simp only [indicator_of_mem hy]
    simp only [indicator_of_notMem hy]; cases i with
    | zero=> ext u; simp
    | succ n => rw [iteratedFDeriv_succ_const]; rfl
  refine ⟨fun _=>max f' 0,integrable_const _,fun x hx=> ?_,ae_of_all _ (fun y x hx=>?_)⟩
  · letI := borel (E [×i]→L[ℝ] F); letI : BorelSpace (E [×i]→L[ℝ] F) := ⟨rfl⟩
    have ha : ContinuousOn (JetF f i x) S := hw.comp (f:=fun y:Z=> (x,y)) (continuous_const.prodMk continuous_id).continuousOn (fun y hy=> show (x,y)∈ _ from ⟨ball_subset_closedBall hx,hy⟩)
    rw [funext (hd x hx)]
    exact ((ContinuousOn.measurable_piecewise ha (g:=fun _=>0) continuousOn_const hh.measurableSet).comp hH).aestronglyMeasurable
  rw [hd x hx]; by_cases hy:h y∈S
  · rw [indicator_of_mem hy]; exact (hW (mem_image_of_mem _ (show (x,h y)∈T×ˢ S from ⟨ball_subset_closedBall hx,hy⟩))).trans (le_max_left ..)
  rw [indicator_of_notMem hy,norm_zero]; exact le_max_right ..

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma spent_here [CompleteSpace F] (μ : Measure A) (hf : Meristem v p μ n) : ∀ᶠ x in 𝓝 p, Integrable (v x) μ := by
  obtain ⟨S,hS,hh,hP⟩:= hf.haveSmooth; obtain ⟨B,hB,hb,hU⟩:= hP 0 (Nat.zero_le _)
  filter_upwards [hS] with x hx
  have hp : Integrable (JetF v 0 x) μ := hB.mono' (hb _ hx) (hU.mono fun y hv=> hv _ hx)
  let L : (E [×0]→L[ℝ] F) ≃ₗᵢ[ℝ] F:= continuousMultilinearCurryFin0 ℝ E F
  have he y : L (JetF v 0 x y)=v x y := by rw [JetF, iteratedFDeriv_zero_eq_comp]; exact L.apply_symm_apply _
  rw [← show (L ∘ JetF v 0 x)=v x from funext he]; exact L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hp
end generic
end YM.PhysicalNext.Repeat.Baffle
