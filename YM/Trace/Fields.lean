import YM.Trace.Diagonal
import YM.Spec.Closed

/-!
The exact label used here is in the field quotient of the same table, normalized by
its translation-shell laws, not by declaration of any new stress. We keep the freedom
to subtract an arbitrary real vacuum expectation; ordered slices use the chosen contour.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Trace
open Boundary Function Filter MeasureTheory Set Complex Spectral
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
    (Y : Spec.Final C F S)

def oneWave (O : S.Union) : Test4 →L[ℂ] Y.action.operators.H :=
   ⟨{ toFun f := (Y.action.operators.field O f Y.action.operators.omega).val
      map_smul' c f := by simp
      map_add' f g := by simp }, Y.realization.qt.total.temperate O Y.action.operators.omega⟩
lemma wave_eval (O : S.Union) (f : Test4) : oneWave Y O f=Y.action.operators.vector [(O,f)] := rfl

lemma one_transports (O : S.Union) (f : Test4) (p : E4) :
    oneWave Y O (Probe.ahead p f) = Y.action.action.orbit.translation p (oneWave Y O f) := by
  let t := Mink.Poincare.translation p
  have ht : Probe.ahead p f = Joint.push t f := by ext1 x; exact congr_arg f (by simp [t,Mink.Poincare.translation])
    -- maybe backwards satisfies
  have he := Y.realization.qt.covariance.covariance t O f Y.action.operators.omega
  rw [show Joint.push t f = _ from ht.symm] at he
  rw [show (Y.action.spin.rail t.Λ) O = O from Y.realization.qt.letters.identity _] at he
  refine (Eq.trans he ?_).symm
  have hh : ((⟨Y.action.action.V t Y.action.operators.vacuum,
    Y.realization.qt.covariance.domain t Y.action.operators.omega.prop⟩ : Y.action.operators.domain))=
      Y.action.operators.omega := Subtype.ext (Y.realization.qt.covariance.vacuum _)
  erw [hh]; rfl

def withoutMean {T : Table C.book} (J : T.Stress) (e : ℝ) : T.Field 4 := (∑ i : Axis,J i i) -
    (e : ℂ) • T.unit 4
abbrev theta (Y : Spec.Final C F S) (e : ℝ) := withoutMean Y.sector.energy e

omit Y in
lemma without_rotate {R : S.Rotation} (V : DiffPlan S) (h : S.RealSpin) {J : S.Stress}
    (hr : R.Laws V h) (H : Table.Tensorial R J) (g : Ortho) (e:ℝ) :
    R.act 4 g (withoutMean J e) = withoutMean J e := by
  unfold withoutMean; rw [map_sub,map_smul,hr.identity,map_sum]
  have hg := Matrix.mem_unitaryGroup_iff.mp g.property
  unfold Table.Tensorial at H
  have hf (i j : Axis) : (∑ a : Axis, g.val i a * (g.val j a:ℝ)) = if i=j then 1 else 0 := by
      have := congrFun (congrFun hg i) j
      simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply] using this
  simp only [H, sub_left_inj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,← Complex.ofReal_sum,hf]
  classical
  apply (Finset.sum_eq_single i ?_ (by simp)) |>.trans
  · simp
  intro j _ hj; simp [Ne.symm hj]
lemma theta_fixed (e : ℝ) (g : Ortho) : Y.sector.turns.act 4 g (theta Y e) = theta Y e :=
  without_rotate _ _ Y.phase.transport.spots Y.phase.transport.spin ..

lemma theta_real (e : ℝ) : S.conj Y.room.kernel.spin 4 (theta Y e) = theta Y e := by
  unfold theta withoutMean
  rw [map_sub,map_sum,map_smulₛₗ,S.conj_unit]; simp_rw [Y.phase.transport.conserved.real]
  simp
lemma theta_adjoint (e : ℝ) : S.adj Y.room.kernel.spin 4 timeAxis (theta Y e) = theta Y e := by
  change S.mirror Y.room.kernel.spin 4 (Signed.mirror timeAxis) _ = _
  erw [theta_real Y,← Y.phase.transport.spots.signed 4, theta_fixed]
lemma theta_star (e : ℝ) : Y.action.J (S.pin 4 (theta Y e)) = (S.pin 4 (theta Y e)) := by
  rw [show Y.action.J (S.pin 4 _) = _ from Y.realization.qt.induced 4 _, theta_adjoint]

lemma exact_pair (e : ℝ) (u v : Test4) :
    Y.A.world.W 2 (fun _ => S.pin 4 (theta Y e)) (Joint.materialize 2 ![Probe.bar u,v]) = inner ℂ
       (oneWave Y (S.pin 4 (theta Y e)) u) (oneWave Y (S.pin 4 (theta Y e)) v) := by
  rw [wave_eval,wave_eval,Y.action.operators.general _ Y.realization.qt.meets _ Y.realization.qt.adj]
  unfold Surface.kernel; dsimp [Letter.op,Sentence.rev,List.map,List.reverse]
  rw [theta_star]; unfold Surface.expect
  let l := ((S.pin 4) (theta Y e))
  change Y.A.world.W 2 (fun _ => l) (Joint.materialize _ _) =
    Y.A.world.W 2 (fun i : Fin 2 => ([(l,Probe.bar u),(l,v)].get i).1)
      (Joint.materialize 2 (fun i : Fin 2 => ([(l,Probe.bar u),(l,v)].get i).2))
  rw [show (fun i : Fin 2 => ([(l,Probe.bar u),(l,v)].get i).1) = (fun _ => l) from funext
       (by intro i; fin_cases i <;> rfl), show (fun i : Fin 2 => ([(l,Probe.bar u),(l,v)].get i).2) =
        ![Probe.bar u,v] from funext (by intro i; fin_cases i <;> rfl)]

/-- Real subtraction kept as a parameter to include the vacuum centering. -/
theorem theta_measure (e : ℝ) : let v := oneWave Y (S.pin 4 (theta Y e)); ∃ μ : Measure E4,
    Tempered μ ∧ μ Mink.coneᶜ=0 ∧ ∀ f g : Test4, inner ℂ (v f) (v g)=
       ∫ p, star (plus f p) * plus g p ∂μ :=
  orbit_measure Y.action.action.orbit Y.action.momentum Y.realization.qt.spectral _ (fun p f => one_transports Y _ f p)
    Y.realization.qt.forward Mink.closed_cone.measurableSet
end YM.Trace
