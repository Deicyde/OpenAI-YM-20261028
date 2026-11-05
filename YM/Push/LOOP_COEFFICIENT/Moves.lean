import YM.Push.LOOP_COEFFICIENT.Carries
import YM.Push.LOOP_COEFFICIENT.Vector
import YM.Work.A15

/-! # Sitewise orthogonal operations in color coordinates -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice Wilson Precision Exterior RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {m : Type} [Fintype m] [DecidableEq m]

def direct (e : m → m) (L : m → G.Color →ₗ[ℝ] G.Color) : Matrix (Point G m) (Point G m) ℝ :=
    LinearMap.toMatrix' ((paint G _).symm.toLinearMap.comp <| LinearMap.pi fun i =>
      (L i).comp <| (LinearMap.proj (e i)).comp (paint G _).toLinearMap)

lemma paint_direct (e : m → m) (L : m → G.Color →ₗ[ℝ] G.Color) (v : Array G m) (i : m) :
    paint G _ (direct e L *ᵥ v) i = L i (paint G _ v (e i)) := by
  rw [direct, LinearMap.toMatrix'_mulVec,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply]; rfl

omit [DecidableEq m] in
lemma paint_dot (v w : Array G m) : v ⬝ᵥ w = ∑ i, ⟪paint G m v i, paint G m w i⟫_ℝ := by
  rw [dotProduct, Fintype.sum_prod_type]; simp only [Work.F03.inner_color,paint_apply]

lemma direct_ortho (e : m → m) (he : Bijective e) (L : m → G.Color →ₗ[ℝ] G.Color) (h : ∀ i v, ‖L i v‖=‖v‖) :
    ortho (direct e L) := ortho_of_dot fun v w => by
  rw [paint_dot,paint_dot]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.ofBijective e he)]
  simp only [paint_direct,real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, h]; rfl

lemma joint_R_motion {φ : Loops.Inputs G c f → Loops.Inputs G c f} {U : Loops.Inputs G c f}
    {A : Matrix (JointKey G c f) (JointKey G c f) ℝ} {B : Matrix (SiteKey G f) (SiteKey G f) ℝ}
    (ha : ∀ v, φ (vary U v) = vary (φ U) (A *ᵥ v))
    (hk : ∀ v, φ (gaugeJoint S (vary 1 v) 1 U) = gaugeJoint S (vary 1 (B *ᵥ v)) 1 (φ U)) :
    Carries A B (R_tot S U) (R_tot S (φ U)) := by
  let g X (v : Nodes G f) := gaugeJoint S (vary 1 v) 1 X
  have h1 X : g X 0 = X := by simp [g]
  have hm X : MatDiffAt (g X) 0 := gaugeJoint_diff (matDiffAt_const _) (matDiffAt_const _) vary_diff
  have hc X := (matDiffAt_const X).displacement (hm X) (h1 X)
  rw [← joint_generator U, ← joint_generator (φ U)]
  apply carries_linear (hc _) (hc _) (Filter.EventuallyEq.symm ?_)
  have hu : Tendsto (g U) (𝓝 0) (𝓝 U) := by simpa only [h1] using (hm U).continuousAt.tendsto
  have ht := ((clm A).contDiff.contDiffAt.comp 0 (hc U)).continuousAt.tendsto; rw [Function.comp_apply,h1,displacement_self,map_zero] at ht
  filter_upwards [ht.eventually (displacement_vary (φ U)), hu.eventually (vary_displacement U)] with v he hv
  change _ = displacement _ (g (φ U) (B *ᵥ v))
  rw [← show φ (g U v) = g (φ U) (B *ᵥ v) from hk v,← hv,ha]; exact he.symm

lemma ghost_motion {n : Side} {U V : Config G n} {A : Matrix (BondKey G n) (BondKey G n) ℝ} {B : Matrix (SiteKey G n) _ ℝ}
    (h : Carries A B (R_g U) (R_g V)) (ha : ortho A) (hb : ortho B) (μ : ℝ) :
    Carries B B (ghost μ U) (ghost μ V) := ((h.adj ha hb).mul h).add (Carries.one.smul (μ^2))

lemma dressing_motion {n : Side} {U V : Config G n} {A : Matrix (BondKey G n) (BondKey G n) ℝ} {B : Matrix (SiteKey G n) _ ℝ}
    (h : Carries A B (R_g U) (R_g V)) (ha : ortho A) (hb : ortho B) (μ : ℝ) :
    Carries B B (dressing μ U) (dressing μ V) := ((ghost_motion h ha hb μ).inv hb).smul (μ^2)

lemma regulation_motion {n : Side} {U V : Config G n} {B : Matrix (SiteKey G n) _ ℝ} {μ : ℝ}
    (h : Carries B B (dressing μ U) (dressing μ V)) : Carries B B (regulation μ U) (regulation μ V) :=
  Carries.sum (Finset.range (depth+1)) (fun i _ => h.pow i)

def portion {G : Gauge} {n : Side} (i : Axis) (v : Loops.Links G n) : Nodes G n := fun j => v ((j.1,i),j.2)

lemma parallel_apply {n : Side} (i : Axis) (M : Matrix (SiteKey G n) (SiteKey G n) ℝ) (v : Loops.Links G n) :
    portion i (parallel M *ᵥ v) = M *ᵥ portion i v := by
  funext j
  simp only [portion, Matrix.mulVec,dotProduct,Fintype.sum_prod_type,parallel,Matrix.of_apply,ite_mul,zero_mul]
  simp only [← Finset.ite_sum_zero,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]

lemma parallel_direct {n : Side} {A : Matrix (BondKey G n) (BondKey G n) ℝ} {B : Matrix (SiteKey G n) _ ℝ}
    {M N : Matrix (SiteKey G n) _ ℝ} (h : Carries B B M N) {e : Axis → Axis} (ha : ∀ i v, portion i (A *ᵥ v) = B *ᵥ portion (e i) v) :
    Carries A A (parallel M) (parallel N) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; funext ⟨x,j⟩
  change portion x.2 (parallel N *ᵥ A *ᵥ v) (x.1,j) = portion x.2 (A *ᵥ parallel M *ᵥ v) (x.1,j)
  rw [parallel_apply, ha,ha,parallel_apply,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec, show _=_ from h]

lemma reference_motion {n : Side} {A : Matrix (BondKey G n) (BondKey G n) ℝ} {B : Matrix (SiteKey G n) _ ℝ}
    {U V : Config G n} {p : Clip} {W : PathData G} (ha : ortho A) (hb : ortho B) (hr : Carries A B (R_g U) (R_g V))
    {e : Axis → Axis} (h : ∀ i v, portion i (A *ᵥ v) = B *ᵥ portion (e i) v)
    (hk : Carries A A (cost (mainTerm p W) U) (cost (mainTerm p W) V)) (μ : ℝ) :
    Carries A A (reference μ p W U) (reference μ p W V) := by
  have he := dressing_motion hr ha hb μ
  exact (hk.add ((hr.mul ((regulation_motion he).pow _)).mul (hr.adj ha hb))).add (((parallel_direct he h).pow depth).smul (μ^2))

end YM.Push.Loops
