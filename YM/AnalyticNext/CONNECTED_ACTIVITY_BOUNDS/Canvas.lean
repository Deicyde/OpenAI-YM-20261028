import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount
import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# Joint measurability bills. First, V, angle, masks and precision

Before integrating the WORD we need on the very same product space.
ContinuousOn assertions used only locally here. No uniform analytical
germ estimated from a region's borel currency. Applies through all
V-with-their-actual-files, no presumption of global near-U.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Canvas
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint  
open Centered Centered.Till  Footprint    Mixed 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}
  {P : Teller G} {α : Type*} [MeasurableSpace α]

lemma line_basis {s : α→G.Color} (j : G.ColorIndex) (h : Measurable s) : Measurable (fun a => s a j) :=
    (show Continuous fun x : G.Color => x j by fun_prop).measurable.comp h
lemma measure_lds {i : Type*} {p : α→i × G.ColorIndex→ℝ} (h : Measurable p) (j : i) :
    Measurable fun a => Aff.descend (p a) j := by
  have hi (v : α) : Aff.descend (p v) j = WithLp.toLp 2 (fun k => p v (j,k)) := rfl
  simp_rw [hi]
  apply (show Continuous (WithLp.toLp 2 (V:=G.ColorIndex→ℝ)) from (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.continuous_of_finiteDimensional).measurable.comp
    (measurable_pi_lambda (fun a k => p a (j,k)) fun k => (measurable_pi_apply _).comp h)

lemma holding (q : Chi) (r t : ℝ) {N : ChartRatio G} (h : Choice N r) : Measurable (hold q r t (G:=G)) := by
  let A := G.lieExp '' Metric.ball 0 r
  have hs : ContinuousOn (LocalH.snap G) A := fun x hx => ((h.law.2.2.2.2.2.2 x hx).continuousAt.comp
    G.continuous_mat.continuousAt).continuousWithinAt
  refine ContinuousOn.measurable_piecewise (s:=A) (f:=fun i : G.El => _) ?_ continuousOn_const h.law.1.measurableSet
  exact ((show Continuous (q.innerShare t) from q.smooth.continuous.comp ((continuous_id'.div_const _).pow _)).comp_continuousOn
    hs.norm).smul hs

lemma escort {V : α → Config G c} (h : Measurable V) (g : Ratio c f) : Measurable fun p => replica g (V p) := by
  refine (show Continuous (replica (G:=G) g) by unfold replica; apply continuous_pi; intro i; split <;> fun_prop).measurable.comp h

section matric
variable {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {B : Type*}

def Meter (M : α → Matrix ι n ℝ) := ∀ i j, Measurable (fun a => M a i j)

-- convenience for all the field domains (including ragged off support)
lemma upright {q : α → Matrix n n ℝ} (h : Meter q) : Meter (fun p => (q p)⁻¹) := by
  let f (a) (i j) := q a i j
  have hs : Measurable f := measurable_pi_lambda _ (fun i=> measurable_pi_lambda _ (h i))
  let T := n→n→ℝ
  have ht : Continuous ((fun a : T => Matrix.of a)) := continuous_matrix fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have ht' : Measurable fun p => (q p).det := (ht.matrix_det).measurable.comp hs
  intro i j; simp_rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ht'.inv.mul ((show Continuous fun a : T => (Matrix.of a).adjugate i j from
    (show Continuous fun M : Matrix n n ℝ => M i j by fun_prop).comp ht.matrix_adjugate).measurable.comp hs)

omit [Fintype n] in
lemma measures_within (Y : Windows n) {A : α → Matrix n n ℝ} (h : Meter A) : Meter (fun p => Y.within (A p)) := by
  intro i j; unfold Windows.within; simp only [Matrix.of_apply]
  split
  next y =>
    apply upright (q:=fun p => (A p).submatrix ((↑):Y.panel j→n) ((↑):Y.panel j→n)) _ ⟨i,y⟩ ⟨j,Y.owns _⟩
    intro i k; exact h _ _
  next => exact measurable_const

variable {W : Type} [Fintype W]
omit [Fintype ι] [Fintype W] [DecidableEq n] in
lemma stage_mul {M : α→Matrix ι n ℝ} {N : α→Matrix n W ℝ} (hM : Meter M) (hN : Meter N) : Meter (fun i => M i*N i) :=
  fun i j => Finset.measurable_fun_sum _ (fun k _ => (hM i k).mul (hN k j))
omit [Fintype ι] [DecidableEq n] in
lemma vector_mul {M : α→Matrix ι n ℝ} {p : α→n→ℝ} (hM : Meter M) (hp : Measurable p) : Measurable (fun i => M i*ᵥ p i) :=
    measurable_pi_lambda _ fun j => Finset.measurable_fun_sum _ (fun k _ => (hM j k).mul ((measurable_pi_apply k).comp hp))
end matric

section rotating

-- pull deriv. continuous via compact/color (even signs at links away from 1)
lemma polar {U : α→ G.El} {v : α→ G.Color} (h : Measurable U) (he : Measurable v) :
    Measurable fun a => G.adjoint (U a) (v a) := by
  have hf : Continuous fun p : G.El×G.Color => G.adjoint p.1 p.2 := by
    let t := fun p : G.El×G.Color => G.mat p.1 * G.colorMat p.2 * star (G.mat p.1)
    have hm : Continuous t := by unfold t; have h := G.colorMat.continuous_of_finiteDimensional; fun_prop
    exact G.projectColor.continuous_of_finiteDimensional.comp hm
  change Measurable ((fun p : G.El×G.Color => G.adjoint p.1 p.2) ∘ fun a => (U a,v a)); exact hf.measurable.comp (h.prodMk he)

lemma variations {V : α→Config G c} {X : α→Directions G f} (o : Pos S) (hV : Measurable V) (hX : Measurable X) :
    Measurable (fun i => untwine S o (V i) (X i)) := by
  refine measurable_pi_lambda _ fun j => ?_; unfold untwine rotateG
  apply polar
  · exact (continuous_travel ..).measurable.comp (pulling_meas o.1 hV)
  simp_rw [maps_apply]; have he := (measurable_pi_apply (edgeP o.1 j)).comp hX
  split
  next h =>
    apply Measurable.neg; apply polar _ he
    exact ((measurable_pi_apply _).comp (escort hV S.ratio)).inv
  exact he

lemma d_meas {V : α→Config G c} {p : α→Directions G f} (h : Measurable V) (hv : Measurable p) (i : Pos S) (R : ℕ) :
    Measurable fun a => derivative T R i (V a) (p a) := by
  let q a := untwine S i (V a) (p a); have hp : Measurable q := variations i h hv
  unfold derivative; change Measurable fun a => Sum.elim _ _ i.2
  have hm j : Measurable fun a => (q a j) := (measurable_pi_apply _).comp hp
  have ht j : Measurable fun a => curl j (q a) := by
    simp_rw [curl_chain]; exact ((hm _).sub (hm _)).sub ((hm _).sub (hm _))
  cases i.2 -- dependent rewrite q roads issue
  next i =>
    dsimp only [Sum.elim_inl]; unfold level; split
    next h =>
      apply Measurable.tsum; intro m; dsimp only
      split
      next => exact (ht (slotFace (T.up.row i.1.2 m).2 i.1.1)).const_smul ((T.up.row i.1.2 m).1)
      next => exact measurable_const
    exact (ht i.1).const_smul (Real.sqrt T.high.direct)
  next i =>
    simp_rw [Sum.elim_inr, noise_linear]
    refine Measurable.const_smul (g:=fun a => ∑ j, probe S (pole i) j • Aff.form (q a) j) ?_ (-Real.sqrt S.kernel.penalty)
    apply Finset.measurable_fun_sum; intro k _; exact (hm _).const_smul (probe S (pole i) k)

lemma matrix_meas (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) {V : α → Config G c} (h : Measurable V) :
    let D p := Dmat T F x A (V p)
    Meter D ∧ Meter (fun p => gram T F x A (V p)) := by
  intro D
  have hv : Meter D := by
    intro i j; unfold D Dmat scale; simp only [Matrix.of_apply]; split
    next hh => exact measurable_const.mul (line_basis i.2 (d_meas h (p:=fun _ => lie (Pi.single j 1)) measurable_const _ _))
    exact measurable_const
  exact ⟨hv,fun i j => ((stage_mul (M:=fun p => (D p).transpose) (fun k l => hv l k) hv) i j).add measurable_const⟩
end rotating
end YM.AnalyticNext.ConnectedActivity.Canvas
