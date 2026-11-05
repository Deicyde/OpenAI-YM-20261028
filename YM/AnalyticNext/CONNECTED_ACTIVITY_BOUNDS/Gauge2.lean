import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ReachD

/-!
# Compare D in suitable patch gauges holding the rotation fixed

No global almost-flat V. Whole exponent price of the product later has
to preserve the same-channel means.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Matrix Lattice RG Wilson Pressure Pressure.Stores Precision Tree Exterior Turn
open Push.SectorMeasure Push.SectorMeasure.Oriented Work.F03 Next.Fluctuations
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

private lemma corner_rotate (z : Site n → G.El) (V : Config G n) (i j : Site n) :
    aiming (gauge z V) i j = z i*aiming V i j*(z j)⁻¹ := by unfold aiming; rw [travel_gauge,finish]

-- Lie colors are at the LEFT. Negative orientation conjugates at positive-link right end.
lemma orientation_tangent (s : Signed) (U : Config G n) (v : Directions G n) (u : Site n → G.El) :
    maps s (gauge u U) (rotateG v u)=rotateG (maps s U v) (fun i => u (s.act i)) := by
  funext ⟨a,i⟩
  let I := (posDir i).rotate s
  let b := I.used (s.act a)
  have hb : b=edgeP s (a,i) := by simp only [edgeP,b,I,sendEdge,affine, add_zero]
  simp only [maps_apply,rotateG]; rw [← hb]
  change (if I.neg then _ else _) = (G.adjoint _) (if I.neg then _ else _)
  split
  next h =>
    have he : b.1 + step b.2=s.act a := by unfold b; simp only [Step.used,h,if_true]; simp
    simp only [Lattice.gauge,he,map_neg]
    rw [← G.adjoint_mul,← G.adjoint_mul]
    rw [show (u b.1 * _ * (u _)⁻¹)⁻¹ * u b.1 = u (s.act a)*(U b)⁻¹ by group]
  next h =>
    have he : b.1=s.act a := by unfold b; simp [Step.used,h]
    rw [he]

lemma gauge_pulled (s : Signed) (U : Config G n) (z : Site n→G.El) :
    pull s 0 (gauge z U) = gauge (z ∘ s.act) (pull s 0 U) := by
  funext i
  unfold pull; rw [Step.gauge_read]; simp only [Lattice.gauge, affine,add_zero,Function.comp_apply,s.act_add, Step.vec_rotate, Step.vec_pos]

lemma in_orbit (p : Pos S) (V : Config G c) (x : Directions G f) (z : Site c→G.El) :
    let Z := z ∘ S.ratio.parent
    untwine S p (gauge z V) (rotateG x Z)= rotateG (untwine S p V x) (fun _ => z (base S p)) := by
  intro Z
  unfold untwine
  rw [gauge_pulled, ← copied S.ratio S.patch.odd_side, show Z=constantGauge z S.ratio from rfl,
    orientation_tangent]
  funext i; simp only [rotateG,Function.comp_apply,constantGauge,S.ratio.parent_signed S.patch.odd_side,
    corner_rotate]; simp only [base]
  rw [← G.adjoint_mul,← G.adjoint_mul]; congr 1; group

private lemma level_const (T : Tube G S) (R : ℕ) (i : Twin f) (x : Directions G f) (a : G.El)
    {P : Teller G} (he : P.Funds S T) :
    level T R i (rotateG x (fun _=>a)) = G.adjoint a (level T R i x) := by
  have h (p : Cell f) : curl p (rotateG x (fun _ => a)) = G.adjoint a (curl p x) := by
    simp only [curl_chain,chain,rotateG,map_sub]
  unfold level; split
  next hi =>
    let f := (G.adjoint a).toContinuousLinearMap
    change _ = f (∑' l,bandTerm T R i.1 l x)
    rw [f.map_tsum (band_summable he R i.1 x)]
    refine tsum_congr fun l => ?_
    change bandTerm _ _ _ _ _ = (G.adjoint a) _
    unfold bandTerm; split
    next hl => rw [map_smul,h]
    next hl => rw [map_zero]
  next hi =>
    change Real.sqrt _ • curl _ _ = G.adjoint _ (Real.sqrt _ • curl _ _)
    rw [map_smul,h]

lemma noise_linear (x : Directions G f) (i : Bond c) :
    zLin S (form x) 0 i = -Real.sqrt S.kernel.penalty • ∑ j : Body 1 f, probe S (pole i) j • form x j := by
  ext k
  let L := (LinearMap.proj k).comp (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).toLinearMap
  unfold zLin
  simp only [PiLp.smul_apply, PiLp.sub_apply, Pi.zero_apply, PiLp.zero_apply]
  change _ = -Real.sqrt S.kernel.penalty • L (∑ j,probe S (pole i) j • form x j); rw [map_sum]
  unfold Matrix.mulVec dotProduct
  simp only [map_smul,zero_sub, smul_neg, neg_smul]; rfl

lemma derivative_gauge (T : Tube G S) (R : ℕ) (p : Pos S) (V : Config G c) (x : Directions G f)
    (z : Site c→G.El) {P : Teller G} (hT : P.Funds S T) :
    derivative T R p (gauge z V) (rotateG x (z ∘ S.ratio.parent)) =
      G.adjoint (z (base S p)) (derivative T R p V x) := by
  rcases p with ⟨s,i|i⟩
  · unfold derivative; dsimp only [Sum.elim_inl]; rw [in_orbit, level_const T R i _ _ hT]
  unfold derivative; dsimp only [Sum.elim_inr]; rw [in_orbit,noise_linear,noise_linear]; simp only [map_smul,
    map_sum]; rfl
end YM.AnalyticNext.ConnectedActivity.Aff
