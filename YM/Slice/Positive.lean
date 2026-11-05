import YM.Analysis.Projected
import YM.Slice.Mirror
import Mathlib.MeasureTheory.Group.Integral

/-!
# Positivity of actual temporal kernel, no independence of cross-link averages
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set Filter MeasureTheory
open Lattice Wilson Cells Analysis
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder ComplexConjugate
variable {n : Side} {G : Gauge} (a : Axis)

instance : SecondCountableTopology (Leaf G a n) := by unfold Leaf; infer_instance
instance : SecondCountableTopology (Thread G a n) := by unfold Thread; infer_instance

private lemma overlap (G : Gauge) : NNKernel fun (x y : G.El) => (((G.mat x * star (G.mat y)).trace.re : ℝ) : ℂ) := by
  let A (i j : Fin G.repDim) (u : G.El) := (((G.mat u i j).re : ℝ) : ℂ)
  let B (i j : Fin G.repDim) (u : G.El) := (((G.mat u i j).im : ℝ) : ℂ)
  let K (i j : Fin G.repDim) (x y) := star (A i j x) * A i j y + star (B i j x) * B i j y
  have he i j : NNKernel (K i j) := (NNKernel.gram (A i j)).plus (NNKernel.gram (B i j))
  convert NNKernel.adds (fun i x y => ∑ j, K i j x y) Finset.univ (fun i _ => NNKernel.adds (K i) Finset.univ (fun j _ => he i j)) using 1
  ext1 x; ext1 y
  simp [Matrix.trace, Matrix.mul_apply, Matrix.star_eq_conjTranspose,Complex.mul_re,K,A,B]

theorem positive_weight {β : ℝ} (h : 0 ≤ β) : NNKernel fun (X Y : Leaf G a n) =>
    ((weight a β X Y 1 : ℝ) : ℂ) := by
  let c : ℝ := β / G.repDim
  let e (X : Leaf G a n) := ((evenPart a β X : ℝ) : ℂ)
  let v (X Y : Leaf G a n) := ((Real.exp (-β * Fintype.card (Tile a n)) : ℝ) : ℂ)
  let M (X Y : Leaf G a n) := (∑ p : Tile a n, (G.mat (X p) * star (G.mat (Y p))).trace.re)
  have hp : NNKernel fun x y => (M x y : ℂ) := by
    simp_rw [M, Complex.ofReal_sum]
    exact NNKernel.adds (fun (i : Tile a n) (x y : Leaf G a n) => ((G.mat (x i) * star (G.mat (y i))).trace.re : ℂ)) Finset.univ
      fun p _ => (overlap G).titled (fun (x : Leaf G a n) => x p)
  have hs : NNKernel v := by
    have ht := (NNKernel.one (X := Leaf G a n)).scaled (c := ((Real.exp (-β * Fintype.card (Tile a n)) : ℝ):ℂ)) (by positivity)
    simpa only [mul_one, v] using ht
  have hc : 0 ≤ c := div_nonneg h (by positivity)
  have he : NNKernel (fun x y => Complex.exp ((c:ℂ)*(M x y : ℂ))) :=
    (hp.scaled (show 0 ≤ (c : ℂ) by exact_mod_cast hc)).exp
  convert (hs.times (NNKernel.gram e)).times he using 1
  funext x y
  have hm : transition a x y 1 = Fintype.card (Tile a n) - M x y / G.repDim := by
    unfold transition
    simp [connect,Gauge.price,Finset.sum_sub_distrib,M,Finset.sum_div]
  unfold weight
  rw [hm,show -β*_ = -β * Fintype.card (Tile a n) + c * M x y by unfold c; ring,Real.exp_add]
  simp [e,v,Complex.ofReal_exp]; ring

/-- Temporal averaged kernel with both half weights. -/
def heat (β : ℝ) (X Y : Leaf G a n) : ℂ := ∫ u, ((weight a β X Y u : ℝ) : ℂ) ∂(threads n G a)

private lemma heart (β) : Continuous fun z : (Leaf G a n × Leaf G a n) × Thread G a n =>
    ((weight a β z.1.1 z.1.2 z.2 : ℝ) : ℂ) := by
  have h := (weight_cont a β).comp (show Continuous (fun z : (Leaf G a n × Leaf G a n) × Thread G a n => (z.1.1,z.1.2,z.2)) from by fun_prop)
  exact Complex.continuous_ofReal.comp h

theorem heat_cont (β) : Continuous fun p : Leaf G a n × Leaf G a n => heat a β p.1 p.2 := by
  have h := heart a (G := G) (n := n) β
  obtain ⟨c,hc⟩ := h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  refine continuous_iff_continuousAt.mpr fun x => tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => c) (F := fun z : Leaf G a n × Leaf G a n => fun u => ((weight a β z.1 z.2 u : ℝ) : ℂ))
    (Eventually.of_forall fun i => (h.comp (show Continuous (fun p : Thread G a n => (i,p)) from by fun_prop)).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun i => Eventually.of_forall fun u => hc (i,u)
  refine Eventually.of_forall fun u => ?_
  exact (h.comp (show Continuous fun p : Leaf G a n × Leaf G a n => (p, u) from by fun_prop)).continuousAt.tendsto

lemma averaged (β) (X Y : Leaf G a n) : heat a β X Y = ∫ u, ∫ v,
    ((weight a β (repaint a X u) (repaint a Y v) 1 : ℝ) : ℂ) ∂(threads n G a) ∂(threads n G a) := by
  have he (u) : (∫ v, ((weight a β (repaint a X u) (repaint a Y v) 1 : ℝ) : ℂ) ∂(threads n G a)) = heat a β X Y := by
    rw [← integral_mul_left_eq_self (μ := threads n G a) (fun v => ((weight a β (repaint a X u) (repaint a Y v) 1 : ℝ) : ℂ)) u]
    unfold heat
    apply integral_congr_ae; filter_upwards with v
    rw [weight_second a β X Y]; simp only [← repaint_split, together]
  simp_rw [he]; simp

theorem step_positive {β : ℝ} (h : 0 ≤ β) : NNKernel (heat a (G := G) (n := n) β) := by
  rw [show heat a (G := G) (n := n) β = _ from funext fun x => funext fun y => averaged a β x y]
  haveI : @BorelSpace (Thread G a n) (MetricSpace.toPseudoMetricSpace (α := Thread G a n)).toUniformSpace.toTopologicalSpace (inferInstance : MeasurableSpace _) := instBorelSpaceThread _
  haveI : @SecondCountableTopology (Thread G a n) (MetricSpace.toPseudoMetricSpace (α := Thread G a n)).toUniformSpace.toTopologicalSpace := instSecondCountableTopologyThread _
  haveI : @CompactSpace (Thread G a n) (MetricSpace.toPseudoMetricSpace (α := Thread G a n)).toUniformSpace.toTopologicalSpace := (inferInstance : CompactSpace (Thread G a n))
  refine NNKernel.accumulate (X := Thread G a n) (A := Leaf G a n) (B := Leaf G a n) (threads n G a) (g := fun X u => repaint a X u) (positive_weight a h) ?_
  intro b c
  apply (heart a (G := G) (n := n) β).comp (show Continuous (fun p : Thread G a n × Thread G a n =>
    ((repaint a b p.1, repaint a c p.2), (1 : Thread G a n))) from ?_)
  exact (((repaint_cont a (G := G) (n := n)).comp (show Continuous (fun p : Thread G a n × Thread G a n => (b, p.1)) from by fun_prop)).prodMk
    ((repaint_cont a (G := G) (n := n)).comp (show Continuous (fun p : Thread G a n × Thread G a n => (c, p.2)) from by fun_prop))).prodMk continuous_const
end YM.Slice
