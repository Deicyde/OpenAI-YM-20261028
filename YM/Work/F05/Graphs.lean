import YM.Work.F05.Actions
import YM.Work.F05.Calculus
import YM.Work.F05.Reindex



/-!
# Identifying the stationary graphs (per fixed tag), additive Hessian

The chart change has two purposes: identification of real tested germs,
and calculation of the *additive* Hessian determinant. No measure change
has yet been put into the latter calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {c f : Side} {G : Gauge} {S : StepData c f}
    {B T : Forest S.ratio} {p : Clip} {W : PathData G}
    {ρ : Bid.Dir G c → AxisChart G B} {u : Bid.Dir G c → AxisChart G T}
    {σ C Λ a b : ℝ}

lemma crit_home (hB : Critical B p W ρ) : Tendsto (fun x => (x,ρ x)) (𝓝 0) (𝓝 0) := by
  have hi := hB.2.1.continuousAt.tendsto
  rw [hB.1] at hi
  exact tendsto_id.prodMk_nhds hi

lemma tested_diag (ha : 0<a) (h : PriceGap B p W a) (r : S.Choices)
    (y : AxisChart G B) (hy : y≠0) : 0 < bend (tested B r p W 0) 0 y y := by
  rw [bend_apply]
  refine lt_of_lt_of_le (mul_pos ha ?_) (h r y)
  obtain ⟨i,hi⟩ : ∃ i, y i≠0 := by simpa only [Ne,funext_iff,Pi.zero_apply,not_forall] using hy
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨i,Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) _⟩

lemma graph_switch (hs : S.patch.Branches S.kernel G) (h : W.Bounds p σ C Λ)
    (hB : Critical B p W ρ) (hT : Critical T p W u) (hb : 0<b) (hQ : PriceGap T p W b)
    (r : S.Choices) : (fun x => switch B T x (ρ x)) =ᶠ[𝓝 0] u := by
  let w (x : Bid.Dir G c) := switch B T x (ρ x)
  have hd := (switch_jet B T (G:=G)).continuousAt.tendsto
  change Tendsto (uncurry (switch B T (G:=G))) (𝓝 0) (𝓝 (switch B T (G:=G) 0 0)) at hd
  rw [switch_zero B T] at hd
  have hw : Tendsto w (𝓝 0) (𝓝 0) := by
    change Tendsto ((uncurry (switch B T)) ∘ (fun x => (x,ρ x))) (𝓝 0) (𝓝 0)
    exact hd.comp (crit_home hB)
  have ht : Tendsto (fun x => (x,w x)) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds hw
  obtain ⟨hc,hv⟩ := hT.2.2 r
  have hg (y : AxisChart G T) : bend (tested T r p W 0) 0 y y = 0 → y = 0 :=
    fun hh => by
      by_contra he
      exact (tested_diag hb hQ r y he).ne' hh
  have hu : Tendsto u (𝓝 0) (𝓝 0) := by
    have hi := hT.2.1.continuousAt.tendsto
    rwa [hT.1] at hi
  refine station_unique (F:=tested T r p W) hc hg hw hu ?_ (hv.mono (fun _ hi => hi.fderiv))
  -- For the switched point use the equation of B in a T-coordinate
  -- neighborhood via the inverse switch (holding x fixed).
  filter_upwards [(crit_home hB).eventually (switch_switch B T),
    ht.eventually ((switch_jet T B).eventually (by simp)),
    ht.eventually (eventually_eventually_nhds.mpr (tested_switch T B hs h r)), hB.2.2 r |>.2]
    with x he hJet heq hRate
  have hy : switch T B x (w x) = ρ x := he
  have HE : tested T r p W x =ᶠ[𝓝 (w x)] tested B r p W x ∘ switch T B x := hold_near heq
  have hr : HasFDerivAt (tested B r p W x) 0 (switch T B x (w x)) := hy.symm ▸ hRate
  rw [HE.fderiv_eq, (hr.comp (w x)
    ((hold_jet hJet).differentiableAt (by simp)).hasFDerivAt).fderiv, ContinuousLinearMap.zero_comp]

lemma hessian_eq (B : Forest S.ratio) (r : S.Choices) (p : Clip) (W : PathData G)
    (x : Bid.Dir G c) (y : AxisChart G B) : hessian B r p W x y = LinearMap.toMatrix₂
      (countingBasis B G) (countingBasis B G) (bend (tested B r p W x) y) := by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, countingBasis_apply, bend_apply]; rfl

lemma hessian_pos (ha : 0 < a) (hQ : PriceGap B p W a) (hB : Critical B p W ρ) (r : S.Choices) :
    ∀ᶠ x in 𝓝 0, 0 < (hessian B r p W x (ρ x)).det := by
  simp_rw [hessian_eq]
  exact (crit_home hB).eventually
    (bend_det_pos (countingBasis B G) (hB.2.2 r |>.1) (tested_diag ha hQ r))

private lemma hessian_transition (e : B.Free ≃ T.Free) (r : S.Choices) (p : Clip) (W : PathData G)
    (x : Bid.Dir G c) (y : AxisChart G B)
    (hp : tested B r p W x =ᶠ[𝓝 y] tested T r p W x ∘ switch B T x)
    (hg : ContDiffAt ℝ ω (move e x) y)
    (ht : ContDiffAt ℝ ω (tested T r p W x) (switch B T x y))
    (hs : fderiv ℝ (tested T r p W x) (switch B T x y) = 0) :
    (hessian B r p W x y).det = (fderiv ℝ (move e x) y).det ^ 2 *
      (hessian T r p W x (switch B T x y)).det := by
  let F := tested T r p W x
  let R := move e x
  let L : AxisChart G B ≃L[ℝ] AxisChart G T := index e
  let V := bend F (switch B T x y)
  let P := V.compl₁₂ L.toLinearEquiv.toLinearMap L.toLinearEquiv.toLinearMap
  let D := fderiv ℝ R y
  have hD : fderiv ℝ (switch B T x) y = L.toContinuousLinearMap.comp D := by
    have he : switch B T x = L ∘ R := move_eq e x
    rw [he, (L.hasFDerivAt.comp _ ((hg.differentiableAt (by simp)).hasFDerivAt)).fderiv]
  have hu : ContDiffAt ℝ ω (switch B T x) y := by
    rw [move_eq e x]; exact L.contDiff.contDiffAt.comp _ hg
  have hV : bend (tested B r p W x) y = P.compl₁₂ D.toLinearMap D.toLinearMap := by
    rw [bend_congr hp, bend_comp_stationary ht hu hs, hD]; rfl
  let b := countingBasis B G
  have hw : LinearMap.toMatrix₂ b b P =
      (hessian T r p W x (switch B T x y)).submatrix (onKey e) (onKey e) := by
    ext i j
    simp only [LinearMap.toMatrix₂_apply, submatrix_apply, hessian_eq, b, countingBasis_apply]
    change V (index e (frame B i)) (index e (frame B j)) = _
    rw [index_frame,index_frame]
  rw [hessian_eq, hV, LinearMap.toMatrix₂_compl₁₂ b b]
  rw [Matrix.det_mul, Matrix.det_mul, det_transpose, ← show b=countingBasis B G from rfl,
    LinearMap.det_toMatrix, hw, det_submatrix_equiv_self]
  change D.toLinearMap.det * _ * D.toLinearMap.det = D.toLinearMap.det ^ 2 * _
  ring

/-- Counting determinant relation on shell. In both spaces we use the
prescribed counting matrix, and the Jacobian is of the map with common
additive coordinates (not Haar Jacobian). -/
lemma hessian_ratio (hs : S.patch.Branches S.kernel G) (h : W.Bounds p σ C Λ)
    (hB : Critical B p W ρ) (hT : Critical T p W u) (e : B.Free ≃ T.Free)
    (hx : (fun x => switch B T x (ρ x)) =ᶠ[𝓝 0] u) (r : S.Choices) :
    ∀ᶠ x in 𝓝 0, (hessian B r p W x (ρ x)).det =
      (fderiv ℝ (move e x) (ρ x)).det ^ 2 * (hessian T r p W x (u x)).det := by
  obtain ⟨hp,hu⟩ := hT.2.2 r
  filter_upwards [hx,hu,(crit_home hB).eventually
    (eventually_eventually_nhds.mpr (tested_switch B T hs h r)),
    (crit_home hB).eventually ((move_jet e).eventually (by simp)),
    (crit_home hT).eventually (hp.eventually (by simp))] with x hk hr hj hh hl
  change switch B T x (ρ x)=u x at hk
  rw [← hk]
  exact hessian_transition e r p W x (ρ x) (hold_near hj) (hold_jet hh)
    (hk.symm ▸ hold_jet hl) (hk.symm ▸ hr.fderiv)
end YM.Work.F05
