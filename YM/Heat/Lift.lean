import YM.Heat.Imaginary
import YM.Paley.Half
import YM.Paley.Icon
import YM.Paley.Mapped
import YM.SNAG.Escape




/-!
# Coordinate spectral conclusions (on any Chamber/semigroup before O)

Unites and energy bound on H_0. Replaced  with SNAG & Air/Laplace,
no spectral gap. PVM packing in E4, Always read positive ℓ inner. `emerges` uses the same S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter MeasureTheory Measure Spectral Complex Analysis Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)

def SEP (a : Axis) : E4 →L[ℝ] Cross a := LinearMap.toContinuousLinearMap {
    toFun x := ⟨x-x a • basis a, by change (x-x a • basis a) a=0;simp⟩
    map_add' x y := by apply Subtype.ext; change x+y-_ • _=_+(_-_);ext i; simp; split_ifs <;> ring
    map_smul' c x := by apply Subtype.ext; change (c•x)-(c•x : E4) a • basis a = c • (x-_); rw [smul_sub, smul_smul];rfl }
lemma cont_cross {T : Type*} [TopologicalSpace T] (F : T → H) (G : T→ Cross a) (hc : Continuous F) (hg : Continuous G) :
    Continuous (fun t => S.U (G t) (F t)) := by
  apply continuous_iff_continuousAt.mpr; intro t
  apply Metric.tendsto_nhds.mpr; intro ε he
  have hp := (S.continuousU (F t)).comp hg
  filter_upwards [Metric.tendsto_nhds.mp (hc.tendsto t) (ε/2) (by positivity),
     Metric.tendsto_nhds.mp (hp.tendsto t) (ε/2) (by positivity)] with i hi hw
  apply lt_of_le_of_lt (dist_triangle _ (S.U (G i) (F t)) _)
  rw [dist_eq_norm, ← map_sub,S.unitary,← dist_eq_norm]
  change dist (S.U (G i) _) _ < _ at hw; simp only [Function.comp_apply] at hw
  linarith
lemma cont_edge {T : Type*} [TopologicalSpace T] (F : T → H) (G : T→ ℝ) (hc : Continuous F) (hg : Continuous G) :
    Continuous (fun t => S.edge (G t) (F t)) := by
  apply continuous_iff_continuousAt.mpr; intro t
  apply Metric.tendsto_nhds.mpr; intro ε he
  have hp := (S.cont (F t)).comp hg
  filter_upwards [Metric.tendsto_nhds.mp (hc.tendsto t) (ε/2) (by positivity),
     Metric.tendsto_nhds.mp (hp.tendsto t) (ε/2) (by positivity)] with i hi hw
  apply lt_of_le_of_lt (dist_triangle _ (S.edge (G i) (F t)) _)
  rw [dist_eq_norm, ← map_sub,S.life,← dist_eq_norm]
  change dist (S.edge (G i) _) _ < _ at hw; simp only [Function.comp_apply] at hw
  linarith

def unit : Orbit H E4 where
  translation x := (S.edge (x a)).comp (S.U (SEP a x))
  origin := by change _=ContinuousLinearMap.id ℂ _; simp only [map_zero,PiLp.zero_apply,S.uZero,S.birth,ContinuousLinearMap.comp_id]
  sends x y := by
    rw [PiLp.add_apply,map_add,S.space, ← send]; ext1 i; simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.comp_apply (S.U (SEP a x)),← both];rfl
  unitary x v := (S.life _ _).trans (S.unitary _ _)
  moves x := cont_edge S (fun p : E4 => S.U (SEP a p) x) (fun v : E4 => v a)
    ((S.continuousU _).comp (SEP a).continuous) (by fun_prop)

def ℚmeasure : PVM H E4 := S.unit.P
lemma joint : S.unit.Spectrum S.ℚmeasure := S.unit.total

/-- side-curtain including shifts at any point E4. -/
def ray (v : H) (z : ℂ) (x : E4) := S.unit.translation x (S.edge z.re (S.E z.im.toNNReal v))
def J (x : E4) (v w : H) (z : ℂ) := inner ℂ v (S.ray w z x)
lemma lift_ray (v : H) {z : ℂ} (hp : 0<z.im) (x : E4) : S.ray v z x = S.unit.translation x (S.F (-I*z) v) := by
  rw [ray,← roots_heat S (Real.toNNReal_pos.mpr hp), ← ContinuousLinearMap.comp_apply (S.edge z.re), S.along (dur.mpr (Real.toNNReal_pos.mpr hp))]
  rw [show duration _+sideways z.re= -I*z from Complex.ext (by simp [duration,hp.le]) (by simp [duration,hp.le,sideways])]
lemma veers (p : ℝ) (x : E4) (v w : H) : S.J x v w p = inner ℂ v (S.unit.translation (x+p • basis a) w) := by
  rw [← S.unit.sends,J, ray, show (p:ℂ).im.toNNReal=0 by simp, S.eZero,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply]
  have ht : SEP a (p • basis a)=0 := Subtype.ext (show (p:ℝ) • basis a-_=_ by simp)
  dsimp only [unit]; simp only [ht,S.uZero]
  simp

lemma altitude (x : E4) (v w : H) : Paley.Air (S.J x v w) (‖v‖*‖w‖) := by
  have hp : Continuous (fun z : ℂ => S.edge z.re (S.E z.im.toNNReal w)) := S.cont_edge _ _
    ((S.continuousE w).comp (continuous_real_toNNReal.comp continuous_im)) continuous_re
  have hv : Continuous (J S x v w) := (innerSL ℂ v).continuous.comp ((S.unit.translation x).continuous.comp hp)
  refine ⟨hv.continuousOn, fun z hz => ?_,fun z hz => ?_⟩
  · apply DifferentiableAt.differentiableWithinAt
    let R := (innerSL ℂ v).comp ((S.unit.translation x).comp (ContinuousLinearMap.apply ℂ _ w)) -- mismatched
    let f (z : ℂ) := R (S.F (-I*z))
    have he : -I*z∈inside := by
      change 0 < (-I*z).re; simpa using (show 0 < z.im from hz)
    have ht : DifferentiableAt ℂ f z := R.differentiableAt.comp z ((S.localHeat (-I*z) he).differentiableAt.comp z (by fun_prop))
    apply ht.congr_of_eventuallyEq
    filter_upwards [Paley.open_loft.mem_nhds hz] with z hz
    rw [J,lift_ray S _ (show 0 < z.im from hz)];rfl
  unfold J ray
  apply (norm_inner_le_norm _ _).trans
  rw [S.unit.unitary,S.life]
  exact mul_le_mul_of_nonneg_left ((S.E _).le_opNorm _ |>.trans (mul_le_of_le_one_left
    (norm_nonneg _) (S.shrinks _))) (norm_nonneg _)

lemma assigned (v : H) (b : ℝ) (x : E4) : S.J x v v b= ∫ y, (plane y x)*Complex.exp (↑(y a*b)*I) ∂S.ℚmeasure.diagonal v := by
  rw [veers, ← S.joint, charFun_apply]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only
  rw [inner_add_right,real_inner_smul_right, real_inner_comm (basis a), basis_inner, ofReal_add,add_mul, Complex.exp_add,mul_comm b]; rfl

/-- all positive-time support before any rotations. -/
lemma nonneg (x : H) : (S.ℚmeasure.diagonal x).support ⊆ {p:E4 | 0 ≤ p a} := by
  apply Paley.supports (S.ℚmeasure.diagonal x) (fun p => p a) (by fun_prop) (altitude S 0 x x)
  intro p; simp [assigned]
lemma bright (x : H) : ∀ᵐ p ∂S.ℚmeasure.diagonal x, 0 ≤ p a := Eventually.mono Measure.support_mem_ae fun _ hp => S.nonneg _ hp

/-- strict mixed displacement represented by damped measure, diag here. -/
lemma heat (x : E4) (v : H) {z : ℂ} (h : z∈ Paley.high) :
    S.J x v v z=(∫ p, plane p x * Complex.exp (↑(p a)*z*I) ∂S.ℚmeasure.diagonal v) := by
  let k := Paley.cell (S.ℚmeasure.diagonal v) (fun p : E4 => p a) (plane · x)
  have hp := Paley.heat _ _ (by fun_prop : Continuous fun p : E4 => p a) (S.bright v) (plane · x) ?_ (fun i => plane_norm _ x)
  · apply Paley.along_edge (S.altitude x v v) hp _ h
    intro i; rw [S.assigned]; unfold Paley.cell Paley.weight; simp only [ofReal_mul]
  unfold plane; fun_prop
end YM.OS.Semigroup
