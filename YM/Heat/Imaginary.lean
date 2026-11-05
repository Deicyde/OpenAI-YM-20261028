import YM.Heat.Extend

/-!
# Edge unitary and ground representative for strict Minkowski time

Parameter `sideways t = -i t` so Wick heat exponent F(duration u-i t),
time translation V(t), orbit sign +i. F agrees in INTERIOR. Extend
separately strongly. No second Wick sign elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis Submodule
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)

lemma whole (t) : DenseRange (S.E t) := by
  have he : ((S.E t).range : Submodule ℂ _).topologicalClosure = ⊤ := by
    rw [← orthogonal_orthogonal_eq_closure,ContinuousLinearMap.orthogonal_range,S.sym]
    exact (orthogonal_eq_top_iff _).mpr ((Submodule.eq_bot_iff _).mpr (fun x hx => S.heat_faithful t x hx))
  have hx (x : H) : x ∈ ((S.E t).range : Submodule ℂ _).topologicalClosure := he ▸ mem_top
  exact hx

def sideways (t : ℝ) := -(t:ℂ)*Complex.I
@[simp] lemma side (t) : (sideways t).re=0 := by simp [sideways]
lemma allow (z) (p : ℝ) : z+sideways p∈ inside ↔ z ∈ inside := by simp [inside]
@[simp] lemma length {p q} : duration p+sideways q∈ inside ↔ 0<p := (allow _ q).trans dur
@[simp] lemma side_add (t s) : sideways (t+s)=sideways t + sideways s := by simp [sideways]; ring
@[simp] lemma side_zero : sideways 0=0 := by simp [sideways]



lemma pillar (t : ℝ) {r : ℝ≥0} (hr : 0<r) (x : H) :
    ‖S.F (duration r+sideways t) x‖=‖S.E r x‖ := by
  let w := duration r+sideways t
  let f := S.F w
  have h : w∈inside := length.mpr hr
  have he : f.adjoint.comp f=(S.E r).adjoint.comp (S.E r) := by
    have hv : star w+w=duration r+duration r := by simp only [w]; apply Complex.ext <;> simp [sideways,duration]
    rw [show f.adjoint=_ from S.flip_row h,show f=S.F w from rfl,← S.pairs (show star w∈inside from h) (show w∈inside from h),S.sym, hv,
      S.pairs (dur.mpr hr) (dur.mpr hr),S.roots_heat hr]
  have hh : inner ℂ (f x) (f x) = inner ℂ (S.E r x) (S.E r x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right f, ← ContinuousLinearMap.comp_apply,he]
    exact ContinuousLinearMap.adjoint_inner_right (S.E r) x (S.E r x)
  exact cong_sq_root hh
where cong_sq_root {x y : H} (he : inner ℂ x x=inner ℂ y y) : ‖x‖=‖y‖ := by rw [@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,he]

/-- Dense E1 extension. -/
def edge (t : ℝ) : H.Op := (S.F (duration 1+sideways t)).toLinearMap.extendOfNorm (S.E 1).toLinearMap

lemma high (t : ℝ) (v : H) : S.edge t (S.E 1 v)= S.F (duration 1+sideways t) v := by
  have hh x : ‖S.F (duration 1+sideways t) x‖ ≤ 1*‖S.E 1 x‖ := by
    rw [S.pillar t (by norm_num : 0<(1:ℝ≥0)) x,one_mul]
  exact LinearMap.extendOfNorm_eq (S.whole 1) ⟨1,hh⟩ v

/-!
 Continuations computed by composition on heated vectors (not on a smaller unlabeled core).
-/

lemma along {z : ℂ} (hz : z∈inside) (t : ℝ) :
    (S.edge t).comp (S.F z) = S.F (z+sideways t) := by
  apply DFunLike.coe_injective
  apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext v
  have hb := dur.mpr (by norm_num : 0 < (1:ℝ≥0))
  have hh : (S.F z).comp (S.E 1)=(S.E 1).comp (S.F z) := by
    rw [← S.roots_heat (dur.mp hb),← S.pairs hz hb,← S.pairs hb hz,add_comm]
  change S.edge t (S.F z (S.E 1 v))=S.F (z+sideways t) (S.E 1 v)
  rw [← ContinuousLinearMap.comp_apply _ _ v,hh,ContinuousLinearMap.comp_apply, S.high, ← ContinuousLinearMap.comp_apply, ← S.pairs (length.mpr (dur.mp hb)) hz, ← S.roots_heat (dur.mp hb)]
  rw [← ContinuousLinearMap.comp_apply,← S.pairs ((allow z t).mpr hz) hb]
  congr! 2
  abel

lemma either {z : ℂ} (hz : z∈inside) (t : ℝ) :
    (S.F z).comp (S.edge t) = S.F (z+sideways t) := by
  apply DFunLike.coe_injective
  apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext v
  have hb := dur.mpr (by norm_num : 0 < (1:ℝ≥0))
  change S.F z (S.edge t (S.E 1 v))=S.F (z+sideways t) (S.E 1 v)
  rw [S.high, ← ContinuousLinearMap.comp_apply, ← S.pairs hz (length.mpr (dur.mp hb)), ← S.roots_heat (dur.mp hb)]
  rw [← ContinuousLinearMap.comp_apply,← S.pairs ((allow z t).mpr hz) hb]
  congr! 2
  abel

lemma life (t : ℝ) (v : H) : ‖S.edge t v‖=‖v‖ := by
  have he := (S.whole 1).equalizer (show Continuous (fun v : H => ‖S.edge t v‖) from (S.edge t).continuous.norm)
    (continuous_norm (E := H.space)) (show _ from funext fun i => by
      change ‖S.edge t (S.E 1 i)‖=‖S.E 1 i‖
      rw [high,S.pillar t (by norm_num : 0 < (1:ℝ≥0))])
  exact congr_fun he v

lemma birth : S.edge 0=ContinuousLinearMap.id ℂ _ := by
  apply DFunLike.coe_injective
  apply (S.whole 1).equalizer (S.edge 0).continuous continuous_id
  funext v
  change S.edge 0 (S.E 1 v)=S.E 1 v
  rw [high,side_zero,add_zero,S.roots_heat (by norm_num : 0 < (1:ℝ≥0))]

lemma send (t s : ℝ) : (S.edge t).comp (S.edge s)=S.edge (t+s) := by
  apply DFunLike.coe_injective
  apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext v
  change S.edge t (S.edge s (S.E 1 v))=S.edge (t+s) (S.E 1 v)
  rw [high,high,← ContinuousLinearMap.comp_apply,S.along (length.mpr (by norm_num : 0<(1:ℝ≥0)))]
  congr! 2
  rw [side_add]; abel

lemma both t (s : Cross a) : (S.edge t).comp (S.U s)=(S.U s).comp (S.edge t) := by
  apply DFunLike.coe_injective
  apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext v
  change S.edge t (S.U s (S.E 1 v))= S.U s (S.edge t (S.E 1 v))
  rw [← ContinuousLinearMap.comp_apply _ _ v,← S.independent 1 s,ContinuousLinearMap.comp_apply,high,high,← ContinuousLinearMap.comp_apply,
    S.stays (length.mpr (by norm_num : 0 < (1:ℝ≥0))) s];rfl

lemma cont (v : H) : Continuous fun t => S.edge t v := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr; intro ε he
  obtain ⟨_,⟨y,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp (S.whole 1 v) (ε/3) (by positivity)
  have ht : Continuous fun t => S.edge t (S.E 1 y) := by
    simp_rw [high]
    let Z (t : ℝ) := duration 1 + sideways t
    have hZ : Continuous Z := continuous_const.add ((continuous_ofReal.neg).mul continuous_const)
    exact (ContinuousLinearMap.apply ℂ H.space y).continuous.comp
      (S.localHeat.continuousOn.comp_continuous hZ (fun t => length.mpr (by norm_num)))
  filter_upwards [Metric.tendsto_nhds.mp (ht.tendsto t) (ε/3) (by positivity)] with p hp
  have hv p : dist (S.edge p v) (S.edge p (S.E 1 y)) < ε/3 := by
    rw [dist_eq_norm,← map_sub,S.life]
    exact (dist_eq_norm v (S.E 1 y)) ▸ hy
  have hq := dist_triangle (S.edge p v) (S.edge p (S.E 1 y)) (S.edge t (S.E 1 y))
  have hm := dist_triangle (S.edge p v) (S.edge t (S.E 1 y)) (S.edge t v)
  have hn := hv t; rw [dist_comm] at hn
  linarith [hv p]
end YM.OS.Semigroup
