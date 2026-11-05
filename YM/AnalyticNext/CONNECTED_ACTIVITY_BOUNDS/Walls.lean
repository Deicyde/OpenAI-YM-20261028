import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Pocket
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Yield

/-!
# Joint-measured windows. Integrability in t not assumed here for
measurability; for actual uses the Safe instances are needed and proved
from the prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Canvas
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains  Mixed 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}
  {P : Teller G} {α : Type} [MeasurableSpace α] {U : α→Config G f} {V : α→Config G c}

section metered
variable {v b : Type} [Fintype v] [Fintype b] (W : Windows v)
omit [Fintype v] in
lemma mixed_wall {M N : α → Tile v b} (h : Meter M) (he : Meter N) (k i j s) :
    Meter fun p => routeF (M p) (N p) k i s j := by
  induction k generalizing i with
  | zero => exact fun _ _ => he _ _
  | succ k ih => simp only [routeF]; exact stage_mul (fun _ _ => h _ _) (ih _ _)

variable [DecidableEq v] {M : α→Matrix v v ℝ} (h : Meter M)
include h
omit [Fintype v] in
lemma tilt_plane {t : α → ℝ} (he : Measurable t) : Meter fun p => flows (M p) (t p) := by
  intro i j; simp only [flows,ResolventVolume.graph,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]
  exact measurable_const.add (he.mul ((h i j).sub measurable_const))
omit [Fintype v] in
lemma co_plane : Meter fun p => W.cov (M p) := by
  intro i j; simp only [Windows.cov,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]; exact measurable_const.mul
    ((measures_within W h _ _).add (measures_within W h _ _))
lemma o_plane : Meter fun p => W.untuned (M p) := by
  intro i j; unfold Windows.untuned; exact (stage_mul h (co_plane W h) _ _).sub measurable_const
lemma page_plane {t : α→ℝ} (he : Measurable t) : Meter fun p => ledger W (M p) 0 (t p) := by
  simp only [ledger,pow_zero,Matrix.mul_one]; exact stage_mul (fun i j => (h i j).sub measurable_const)
    (measures_within W (tilt_plane h he))

end metered

lemma total_over (f : α → ℝ → ℝ) (h : Measurable (Function.uncurry f)) (a b : ℝ) (he : a≤b) :
    Measurable (fun x => ∫ t in a..b,f x t) := by
  simp_rw [intervalIntegral.integral_of_le he]; exact h.stronglyMeasurable.integral_prod_right.measurable

lemma telescope {M : α→Matrix (Vars G f) (Vars G f) ℝ} (h : Meter M) (p : Year S) (x : ℝ) {t : α→ℝ} (ht : Measurable t) :
    Measurable (fun i => confluence S x (M i) p (t i)) ∧ Measurable (fun i => crosses S x (M i) p (t i)) := by
  let W := eyes S G (radiusB x)
  have hv := tilt_plane h ht
  have hu i j : Measurable (fun k => (-(W.error (flows (M k) (t k)))) i j) :=
    ((stage_mul hv (measures_within W hv) i j).sub measurable_const).neg
  have hh := stage_mul (show Meter fun p => M p-1 from (fun i j => (h i j).sub measurable_const))
    (measures_within W hv)
  unfold confluence crosses; split
  next he =>
    refine ⟨?_, Measurable.mul (Measurable.pow_const ht.neg _) ?_⟩
    · exact Finset.measurable_fun_sum _ fun i _ => mixed_wall hu hh _ p.2.1 p.2.2.2 p.2.2.1 i i
    exact Finset.measurable_fun_sum _ fun i _ => mixed_wall (o_plane W h)
      (show Meter (fun _ : α => (1:Matrix (Vars G f) (Vars G f) ℝ)) from fun _ _ => measurable_const) _ _ _ p.2.2.1 i i
  exact ⟨measurable_const,measurable_const⟩

section therm
variable {s : α→ F.Slice G} {r : ℝ} {N : ChartRatio G} {k : S.Choices} {h : Chi}
namespace Bent
variable {Y : α→Mint T F A x} (b : Bent Y r h k)
include b
lemma pair_lab (p : Bond f) : Measurable fun i => paired (Y i) p := by
  let f' (i : α) t := letter S x (flatReference T x F) p t-letter S x (Y i).sheet p t
  have hm : Measurable (Function.uncurry f') := by
    let t := eyes S G (radiusB x)
    have hp {M : α×ℝ→Matrix (Vars G f) (Vars G f) ℝ} (he : Meter M) : Measurable fun u : α×ℝ => letter S x (M u) p u.2 := by
      unfold Aff.letter Matrix.trace; apply Finset.measurable_fun_sum
      exact fun i _ => page_plane t he measurable_snd (p,i) (p,i)
    exact (hp (M:=fun _ => flatReference T x F) (fun i j => measurable_const)).sub
      (hp (M:=fun p => (Y p.1).sheet) (fun i j => (b.sheets.2 i j).comp measurable_fst))
  exact (total_over f' hm 0 1 zero_le_one).div_const _
lemma screen {z : α→ ArrayR G f} (h : Measurable z) (p : Year S) :
    Measurable fun i => Chains.chain (Y i) p (z i) := by
  let f' (i : α) t := (confluence S x (flatReference T x F) p t-confluence S x (Y i).sheet p t+crosses S x (Y i).sheet p t)
  have hm : Measurable (Function.uncurry f') := by
    let H := telescope (M:=fun u : α×ℝ => (Y u.1).sheet) (fun i j => (b.sheets.2 i j).comp measurable_fst) p x measurable_snd
    have hv := telescope (M:=fun _ : α×ℝ => flatReference T x F) (fun i j => measurable_const) p x measurable_snd
    exact (hv.1.sub H.1).add H.2
  have hv : Measurable fun i => excise S x (Y i).sheet p (z i) := by
    unfold excise amount
    let D i := Mint.sheet (Y i)
    have hU := o_plane (eyes S G (radiusB x)) (M:=D) b.sheets.2
    have hb := mixed_wall (M:=fun i => -(eyes S G (radiusB x)).untuned (D i))
      (fun i j => (hU i j).neg) (N:=D) b.sheets.2 _ p.2.1 p.2.2.2 p.2.2.1
    have hr := vector_mul hb (p:=fun i => fun j => z i (p.2.2.2,j)) (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp h)
    unfold dotProduct
    apply Finset.measurable_fun_sum; intro j _; exact ((measurable_pi_apply (p.2.1,j)).comp h).mul ((measurable_pi_apply _).comp hr)
  exact (((((total_over f' hm _ _ zero_le_one).div_const (2:ℝ)).add (hv.div_const (2:ℝ))).exp).sub measurable_const)
end Bent
end therm
end YM.AnalyticNext.ConnectedActivity.Canvas
