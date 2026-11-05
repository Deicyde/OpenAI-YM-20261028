import YM.RG08.Germ.Wilson
import YM.RG08.Arc.Spice

/-! # Ward representatives for each full-loop power (finite jets) on true tori
Local representatives (potential-link chart). Only near germ is fixed. Measurability
standins chosen for auxiliary Ward Laplace proof on shrinking sets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} (S : StepData c f) {G : Gauge} (T : Forest S.ratio)
section reps
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]
lemma linings {f : E→V} {x : E} (h : ContDiffAt ℝ ω f x) : ∃ g : E→V, Measurable g ∧ g=ᶠ[𝓝 x] f := by
  obtain ⟨s,hs,hz,he⟩:= h.contDiffOn' (m:=0) (by simp) (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ ..), Set.univ_inter] at he
  exact ⟨s.piecewise f 0, he.continuousOn.measurable_piecewise continuousOn_const hs.measurableSet, (show ∀ᶠ y in 𝓝 x,y∈s from hs.mem_nhds hz).mono fun a ha=> Set.piecewise_eq_of_mem _ _ _ ha⟩ -- order
end reps
lemma content_real (G : Gauge) (m : Side) : ContinuousAt (@content G m) 1 ∧ ∃ g:Config G m→Link G m, Measurable g ∧ g=ᶠ[𝓝 1] content := by
  let i p (x : Config G m) := G.mat (x ((p:Body 1 m).1,axisEquiv.symm p.2))
  have hx p : Continuous (i p):= G.continuous_mat.comp (continuous_apply _)
  have ht p : i p 1=1:= G.mat_one
  have H p : ∃ g:Config G m→G.Color, Measurable g ∧ g=ᶠ[𝓝 1] (G.plog ∘ i p) := by
    obtain ⟨s,hs,hz,he⟩:= G.plog_diff.contDiffOn' (m:=0) (by simp) (by simp)
    simp only [Set.insert_eq_of_mem (Set.mem_univ ..), Set.univ_inter] at he
    let C := i p ⁻¹' s; have hC : IsOpen C:= hs.preimage (hx p); have hL:(1:Config G m)∈ C := (show i p 1∈s by rw [ht p]; exact hz)
    have hi : ContinuousOn (G.plog ∘ i p) C := he.continuousOn.comp (hx p).continuousOn (fun x hx=>hx)
    exact ⟨C.piecewise (G.plog ∘ i p) 0,hi.measurable_piecewise continuousOn_const hC.measurableSet,(show ∀ᶠ y in 𝓝 1,y∈ C from hC.mem_nhds hL).mono fun y hy=> Set.piecewise_eq_of_mem _ _ _ hy⟩
  choose g hG H using H
  let A (x : Config G m):= fun p=>g p x
  refine ⟨ (ContinuousAt.comp (f:=fun x p=> G.plog (i p x)) (arm G m 1).symm.continuousAt (continuousAt_pi.mpr fun p=> ?_)), (arm G m 1).symm ∘ A,?_, ?_⟩
  · refine ContinuousAt.comp (g:=G.plog) ?_ (hx p).continuousAt
    rw [ht p]; exact G.plog_diff.continuousAt
  · exact (arm G m 1).symm.continuous.measurable.comp (measurable_pi_lambda _ hG)
  filter_upwards [eventually_all.mpr H] with x hx
  unfold content; exact congr_arg ((arm G m 1).symm) (funext hx)

-- constants rank-zero jet fixed to zero. call outputs on unnormalized family x
structure Caper {m : Side} (Q : Pot G 2) (F : Air G) (n : ℕ) (q : ℕ) (v : Config G m→ℝ) : Prop where
  stamp : Measurable v
  word  : Pointwise (v ∘ input G m)
  lyrics : ∀ j ≤ n+2, Tensor.coeff (v ∘ input G m) j 0= recital (sector Q F q j) m

private lemma bendM {m : Side} (F H : Link G m→ ℝ) (h : F=ᶠ[𝓝 0] H) (hp : Pointwise H) : Pointwise F := by
  -- unfold
  refine ⟨hp.analytic.congr h.symm,fun i => ?_, fun i=>?_,?_⟩
  · obtain ht := (orderTurn i (G:=G) (m:=m)).continuous.tendsto 0; rw [map_zero] at ht
    exact (h.comp_tendsto ht).trans ((hp.rotate _).trans h.symm)
  · obtain ht := (stain (m:=m) i).continuous.tendsto 0; rw [map_zero] at ht
    exact (h.comp_tendsto ht).trans ((hp.stained _).trans h.symm)
  exact (h.comp_tendsto (moveField_zero (G:=G) (m:=m) ▸ moveField_analytic.continuousAt.tendsto)).trans (hp.guard.trans (h.symm.comp_tendsto (continuous_snd.tendsto (0:Swatch G m))))
lemma costumed {m : Side} {Q : Pot G 2} {F : Air G} (hF : Faithful Q F m) (n : ℕ) :
    ∃ v : ℕ→Config G m→ℝ, ∀ i,Caper Q F n i (v i) := by
  have hu i : ∃ v : Config G m→ℝ,Caper Q F n i v := by
    obtain ⟨u,h,H⟩:=hF i (n+2); obtain ⟨g,hg,hF⟩:= linings h.analytic.contDiffAt
    obtain ⟨L,hL,hE⟩:=(content_real G m).2
    let V:=g ∘ L
    have ht : Tendsto (input G m) (𝓝 0) (𝓝 1) := by simpa using input_cont.tendsto (0:Link G m)
    have hz : V ∘ (input G m) =ᶠ[𝓝 0] u := by
      filter_upwards [ht.eventually hE,input_encodes,hF] with a hx hp he
      unfold V; simp only [Function.comp_apply]; rw [hx,hp,he]
    exact ⟨V,hg.comp hL, bendM _ _ hz h,fun j hj=> (Tensor.GermCoeff j hz).trans (H j hj)⟩
  choose V hv using hu; exact ⟨V,hv⟩
section actual
variable {κ : S.Choices}

def laboratory (κ : S.Choices) (k : ℕ) (V : ℕ→Config G f→ℝ) (t : ℝ)(x : Config G c) (y : Config G f) := tickets S x (S.prediction y κ)+ ∑ i∈Finset.range (k+2+1), t^(2*i)*V i y
lemma tickets_stance (κ : S.Choices) (hp : S.patch.Branches S.kernel G) (X : Type) [MeasurableSpace X]
    {w : X→Config G c} {v : X→Config G f} (h : Measurable w) (hv : Measurable v) : Measurable fun x=> tickets S (w x) (S.prediction (v x) κ) := by
  unfold tickets; refine measurable_const.mul (Finset.measurable_fun_sum _ (fun i _ => G.continuous_price.measurable.comp ?_))
  exact ((measurable_pi_apply i).comp h).mul ((((measurable_pi_apply i).comp (S.prediction_meas hp κ)).comp hv).inv)
lemma labs_meas {V : ℕ→Config G f→ℝ} (hF : ∀ i,Measurable (V i)) (κ : S.Choices) (h : S.patch.Branches S.kernel G)
    (X : Type) [MeasurableSpace X] {w : X→Config G c} {v : X→Config G f} {t : X→ℝ}
    (hw : Measurable w) (hv : Measurable v) (ht : Measurable t) (n) : Measurable fun x=> laboratory S κ n V (t x) (w x) (v x) := by
  unfold laboratory; exact (tickets_stance S κ h X hw hv).add (Finset.measurable_fun_sum _ (fun i _=> (ht.pow_const _).mul ((hF i).comp hv)))
end actual
end YM.RG08.Reflect
