import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Breath
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Canvas
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Chromatic
import YM.Push.RELAY_DIFFERENCE.Shuffles

/-!
# Roots and columns in the actual stencil (meas. even before alignment)

V correlations occur already in the measure on the Z's, so keep
parameter α arbitrary (don't settle only for section-wise meas on
individual axes). Packed `Book` also uses this source from the passed V
not a new table.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Canvas
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint  Wages
open Centered Centered.Till Jewels Footprint Paths   Mixed 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}
  {P : Teller G} {α : Type} [MeasurableSpace α] {U : α→Config G f} {V : α→Config G c}

variable {s : α→ F.Slice G} {r : ℝ} {N : ChartRatio G} {k : S.Choices} {h : Chi}

-- issue Y pre certs
structure Bent (Y : α→Mint T F A x) (r : ℝ) (h : Chi) (k : S.Choices) : Prop where
  V : Measurable (fun p => (Y p).V)
  y : Measurable fun p => (Y p).Y
  radius p : (Y p).r = r ∧ (Y p).u=holdSize G S.patch x
  q p : (Y p).q=h ∧ (Y p).k=k

namespace Bent
variable {Y : α→Mint T F A x} (b : Bent Y r h k) (hT : P.Funds S T) (hv : Choice N r)
include b

lemma sheets : Meter (fun p => (Y p).D) ∧ Meter (fun p => (Y p).sheet) := matrix_meas T A F x b.V

include hv in
lemma shard : Measurable fun p => (Y p).sh := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold Mint.sh fixed real
  simp only [show ∀ p,_ from fun p => (b.radius p).1,show ∀ p,_ from fun p => (b.radius p).2,
    show ∀ p, _ from fun p => (b.q p).1]; split
  next ht => exact line_basis i.2 ((holding h _ _ hv).comp (((measurable_pi_apply i.1).comp (F.continuous_drape.measurable.comp b.y)).mul
    (((measurable_pi_apply i.1).comp (escort b.V S.ratio)).inv)))
  exact measurable_const

include hT hv in
lemma rotational : Measurable (fun p => (Y p).origin) ∧ Measurable (fun p => (Y p).source) ∧
    Measurable (fun p => (Y p).μ) := by
  have ht : Meter fun p => scale T x (Y p).V := by
    intro i j; exact measurable_const.mul (line_basis i.2 (d_meas b.V (p:=fun _ => lie (Pi.single j 1)) measurable_const _ _))
  have hP : Measurable (fun p => (Y p).origin) := by
    refine measurable_pi_lambda _ fun i => ?_
    unfold Mint.origin zeroed; simp_rw [show ∀ p, _ from fun p => (b.q p).2]; split
    next H =>
      exact (Measurable.mul measurable_const (line_basis i.2 (target_me hT (escort b.V S.ratio) b.V x k i.1))).add
        ((measurable_pi_apply i).comp (vector_mul ht (b.shard hv)))
    exact measurable_const
  have hm : Measurable (fun p => (Y p).source) := vector_mul (fun i j => b.sheets.1 _ _) hP
  refine ⟨hP,hm,Measurable.neg ?_⟩
  exact vector_mul (M:=fun i => ((eyes S G (radiusB x)).within (Y i).sheet).transpose)
    (fun i j => measures_within _ b.sheets.2 _ _) hm

include hT hv in
lemma pledges {z : α→ ArrayR G f} (β : ℝ) (hz : Measurable z) : Measurable fun p => cashB (Y p) β (z p) :=
    (b.rotational hT hv).2.2.add (hz.const_smul (power β))

lemma buildField {v : α→ ArrayR G f} (hv : Measurable v) : Measurable fun p => (Y p).build (v p) := by
  apply F.continuous_drape.measurable.comp
  apply measurable_pi_lambda
  intro i; split
  next he => exact (G.lieExp_cont.measurable.comp (measure_lds hv i.val)).mul ((measurable_pi_apply i.val).comp
    (escort b.V S.ratio))
  next => exact (measurable_pi_apply _).comp b.y

include hv hT in
lemma enacts {x' : α→ ArrayR G f} (hx : Measurable x') :
    Measurable (fun p => (Y p).road (x' p)) ∧ Measurable (fun p => actions (Y p) (x' p)) := by
  have hp : Measurable (fun p => (Y p).only (x' p)) := by
    refine measurable_pi_lambda _ fun i => ?_
    unfold only; split
    next h => exact (measurable_pi_apply _).comp hx
    exact measurable_const
  refine ⟨measurable_pi_lambda _ fun i => measure_lds ((b.shard hv).add hp) i, ?_⟩
  exact (vector_mul b.sheets.1 hx).add (b.rotational hT hv).1

include hv hT in
lemma shells {v : α→ ArrayR G f} (he : Measurable v) (i : Rack S) : Measurable (fun p => shell (Y p) (v p) i) ∧
    Measurable (fun p => pureBooth (Y p) (v p) i) := by
  have ht := b.buildField he
  let U p := (Y p).build (v p)
  have hX p' : Measurable fun p => (squareOf (descend ((Y p).actions (Y p).μ) p')) :=
    (((measure_lds (b.enacts hT hv (b.rotational hT hv).2.2).2 p').norm.pow_const 2).div_const (2:ℝ))
  let V := fun i => (Y i).V
  have hh (i : Pos S) : Measurable (fun p => sqref T x k i (V p) ((Y p).road (v p))) := by
    let q := target_me hT (escort b.V S.ratio) b.V x k i
    let t := d_meas (T:=T) b.V (b.enacts hT hv he).1 i (till x)
    exact (((q.add t).norm.pow_const 2).div_const (2:ℝ))
  have hc : Measurable fun p => keptBooth T (U p) k (V p) x i := by
    rcases i with ⟨s,j|j⟩
    · have hu : Measurable (fun p => G.chord (faceValue (pull s 0 (U p)) j)) := toll_meas j (pulling_meas _ ht)
      have hq : Measurable (fun p => G.curvature (faceValue (pull s 0 (U p)) j)) :=
        G.continuous_curvature.measurable.comp ((continuous_travel ..).measurable.comp (pulling_meas _ ht))
      unfold keptBooth; apply Measurable.mul measurable_const; unfold Fextend; dsimp only
      apply (Measurable.mul (f:=fun _ : α => T.high.direct/2) measurable_const ((hu.pow_const 2).sub
        (hq.norm.pow_const 2))).add
      exact Finset.measurable_fun_sum _ (fun j _ => (((target_me hT ht b.V x k _).norm.pow_const 2).div_const (2:ℝ)))
    exact booth_meter hT ht b.V x k _
  simp_rw [shell,pureBooth,show ∀ p,_ from fun p => (b.q p).2]
  have hq : Measurable fun p => dash (Y p) i := by
    rcases i with ⟨s,i|i|i|i⟩
    · exact Finset.measurable_fun_sum univ (fun j _ => hX (s,Sum.inl (i,j)))
    · exact hX _
    · exact measurable_const
    exact measurable_const
  have hp : Measurable fun p => backs (Y p) (v p) i := by
    unfold backs bank; simp_rw [show ∀ p,_ from fun p => (b.q p).2]; split
    swap; exact measurable_const
    rcases i with ⟨s,i|i|i|i⟩ <;> simp only [Sum.elim_inl,Sum.elim_inr]
    · apply Measurable.mul measurable_const; unfold crownF; apply Finset.measurable_fun_sum; exact fun j _ => hh _
    · apply Measurable.mul measurable_const; exact hh _
    all_goals exact measurable_const
  exact ⟨((booth_meter hT ht b.V x k i).sub hp).add hq,(hc.sub hp).add hq⟩
end Bent
end YM.AnalyticNext.ConnectedActivity.Canvas
