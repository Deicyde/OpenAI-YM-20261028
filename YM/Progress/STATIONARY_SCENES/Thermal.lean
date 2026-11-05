import YM.Progress.STATIONARY_SCENES.Dispatch

/-!
# Spending RScene at thermal accounting

Proof the ACTUAL graph, normalized log-det minus log-Haar ratio (+loop),
and thermal invoice are usable.

Reduce `FiniteBound` for every p to JUST its
wave comparison on one tree and one arbitrary tag at that p.

Same chart ratio
in that comparison.

NOT deriving the wave comparison or passing meshes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes
open Filter Lattice RG RG.Supply Wilson Precision Bid Tree Function Matrix Exterior
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {c f n : Side}

section thermal
variable {p : Clip} {P : PathData G} {σ C Λ : ℝ}

private lemma channels {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : X → Config G n}
    (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) 0) (s : Signed) (i : Edge (Site n)) :
    ContDiffAt ℝ ω (fun y => G.mat (pull s 0 (A y) i)) 0 := by
  unfold pull Step.read
  split
  · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (ha _)
  exact ha _

lemma loop_smooth {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : X → Config G n}
    (h : P.Bounds p σ C Λ) (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) 0) :
    ContDiffAt ℝ ω (fun y => Precision.loop P (A y)) 0 := by
  unfold Precision.loop Patch.average
  exact contDiffAt_const.mul (ContDiffAt.sum fun s _ =>
    Work.F02.uncut_contDiffAt (A := fun x => pull s 0 (A x)) h.width h.two (channels ha s))



variable {S : StepData c f} {F : Forest S.ratio} {ρ : Dir G c → AxisChart G F}
  {O : ChartRatio G} {η : ℝ}

/-- Partial second derivative on *actual pairs*. -/
lemma entry_smooth (r : S.Choices) (h : Critical F p P ρ) (i j : Key F G) :
    ContDiffAt ℝ ω (fun z : Dir G c × AxisChart G F => hessian F r p P z.1 z.2 i j) 0 := by
  have hh := Work.F05.curve_partial (F := fun x : Dir G c => fderiv ℝ (tested F r p P x))
    (Work.F05.curve_partial (h.2.2 r).1)
  simp_rw [Work.F05.hessian_eq,LinearMap.toMatrix₂_apply,Work.F05.bend,
    ContinuousLinearMap.toLinearMap₁₂_apply]
  exact (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const

/-- Sign & genuine analyticity (fixed period only). Loop is ALSO evaluated on
THIS ρ. Signals may be used before comparing symbols. -/
theorem receipt (r : S.Choices) (hP : P.Bounds p σ C Λ) (h : Critical F p P ρ)
    (hη : 0 < η) (hG : PriceGap F p P η) (ho : LocalRatio O) :
    (∀ᶠ u : Dir G c in 𝓝 0, 0 < (hessian F r p P u (ρ u)).det) ∧
      ContDiffAt ℝ ω (thermal F r p P ρ O) 0 := by
  have hp := Work.F05.hessian_pos hη hG h r
  refine ⟨hp,?_⟩
  let g := fun x => (x,ρ x)
  have hd : g 0 = 0 := Prod.ext rfl h.1
  have hs : ContDiffAt ℝ ω g 0 := contDiffAt_id.prodMk h.2.1
  have he (i j : Key F G) : ContDiffAt ℝ ω (fun x => hessian F r p P x (ρ x) i j) 0 := by
    have hC := entry_smooth r h i j
    rw [← hd] at hC
    exact hC.comp 0 hs
  have hm : ContDiffAt ℝ ω (fun u : Dir G c => (hessian F r p P u (ρ u)).det) 0 := by
    simp_rw [Matrix.det_apply']
    exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (contDiffAt_prod fun j _ => he _ _)
  have hk (i : F.Free) : ContDiffAt ℝ ω (fun x => O.J (ρ x i)) 0 := by
    have hQ : ρ 0 i = 0 := by rw [h.1]; rfl
    apply ContDiffAt.comp (f := fun x => ρ x i) (g := O.J) 0 _
      ((contDiffAt_apply ℝ G.Color i _).comp 0 h.2.1)
    rw [hQ]
    exact ho.germ _ (Metric.mem_ball_self ho.patch)
  have hw : (∏ i : F.Free, O.J (ρ 0 i)) = 1 := by rw [h.1]; simp [ho.anchored]
  have ht : ContDiffAt ℝ ω (fun x => Precision.loop P (lifting F (represent x) (ρ x))) 0 := by
    refine loop_smooth (A := fun x => lifting F (represent x) (ρ x)) hP fun i => ?_
    have hB := Work.F03.live_smooth F (G := G) i
    rw [← hd] at hB
    exact hB.comp 0 hs
  have hL : ContDiffAt ℝ ω (fun x => Real.log (∏ i : F.Free, O.J (ρ x i))) 0 := by
    apply (contDiffAt_prod fun i _ => hk i).log
    rw [hw]; exact one_ne_zero
  exact (ht.add (contDiffAt_const.mul (hm.log (mem_of_mem_nhds hp).ne'))).sub hL


end thermal

namespace Answer
variable {a : Levels G} {H : Horizon a} {N m : ℕ} {P : PathData G} {η : ℝ}




end Answer
end YM.Progress.StationaryScenes
