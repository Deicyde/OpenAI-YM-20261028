import YM.PCalc.Band

/-!
# Normalize the physical measure, not a tangent-gaussian surrogate

Derive overlap law for true local chart Jacobians.

No LieGroup structure
assumed.

Can shrink radius as needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalH
open Function Filter MeasureTheory Set Metric Precision NormedSpace
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ENNReal

variable (G : Gauge)

def snap (x : G.El) := G.plog (G.mat x)

def Geom (U : Set G.El) (s : Set G.Color) :=
    IsOpen U ∧ IsOpen s ∧
    LeftInvOn (snap G) G.lieExp s ∧ RightInvOn (snap G) G.lieExp U ∧
    MapsTo (snap G) U s ∧ MapsTo G.lieExp s U ∧ ∀ x∈U, ContDiffAt ℝ ω G.plog (G.mat x)

lemma exp_open : ∀ᶠ b : G.Color in nhds 0, ∀ s : Set G.Color, IsOpen s → b ∈ s → G.lieExp '' s ∈ nhds (G.lieExp b) := by
  obtain ⟨V,hV,ho,h1⟩ := _root_.mem_nhds_iff.mp G.plog_right
  have he := G.plog_diff.eventually (by simp)
  filter_upwards [G.plog_left, G.lieExp_cont.continuousAt.preimage_mem_nhds (x:=0) (ho.mem_nhds
    (show G.lieExp 0∈V from by rwa [G.mat_lieExp_zero])), ((G.continuous_mat.comp G.lieExp_cont).tendsto (0:G.Color)).eventually (by simp only [comp_apply,G.mat_lieExp_zero,G.mat_one]; exact he)] with b hb hh hZ
  intro s hs hx
  have hp : G.lieExp b∈V:=hh
  have hr : Tendsto (snap G) (nhds (G.lieExp b)) (nhds b) := by
    have hu : ContDiffAt ℝ ω G.plog (G.mat (G.lieExp b)):=hZ
    simpa only [snap,comp_def,hb] using! hu.continuousAt.tendsto.comp (G.continuous_mat.tendsto (G.lieExp b))
  filter_upwards [ho.mem_nhds hp,hr (hs.mem_nhds hx)] with x h1 h2
  exact ⟨_,(h2 : snap G x ∈ s),(hV h1 : G.lieExp (snap G x)=x)⟩

lemma geom_patch : ∃ R : ℝ,0<R ∧ ∀ r : ℝ, r≤R → Geom G (G.lieExp '' ball 0 r) (ball 0 r) := by
  have he : ∀ᶠ b : G.Color in nhds 0, ContDiffAt ℝ ω G.plog (G.mat (G.lieExp b)) := ((G.continuous_mat.comp G.lieExp_cont).tendsto (0:G.Color)).eventually (by simp only [comp_apply,G.mat_lieExp_zero,G.mat_one]; exact G.plog_diff.eventually (by simp))
  obtain ⟨R,hR,H⟩ := Metric.mem_nhds_iff.mp (he.and (G.plog_left.and (exp_open G)))
  refine ⟨R,hR,fun r hr => ?_⟩
  have hh : ball (0:G.Color) r ⊆ ball 0 R := ball_subset_ball hr
  have hf : LeftInvOn (snap G) G.lieExp (ball 0 r) := fun x hx => (H (hh hx)).2.1
  refine ⟨isOpen_iff_mem_nhds.mpr ?_,isOpen_ball, hf,?_,?_,mapsTo_image _ _,?_⟩
  · rintro v ⟨x,hx,rfl⟩; exact (H (hh hx)).2.2 _ isOpen_ball hx
  · rintro _ ⟨x,hx,rfl⟩; rw [hf hx]
  · rintro _ ⟨x,hx,rfl⟩; rw [hf hx]; exact hx
  rintro _ ⟨x,hx,rfl⟩; exact (H (hh hx)).1

def move (u : G.El) (b : G.Color) := snap G (u*G.lieExp b)

def coat (x : G.Color) := fderiv ℝ (move G (G.lieExp x)⁻¹) x

def spin (x : G.Color) := (coat G x).det

lemma spin_deriv (x : G.Color) : ContDiffAt ℝ ω (spin G) x := by
  have he : ContDiff ℝ ω (fun z : G.Color × G.Color => star (G.mat (G.lieExp z.1)) * G.mat (G.lieExp z.2)) := by
    exact (((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff).comp (G.exp_jet.comp contDiff_fst)).mul (G.exp_jet.comp contDiff_snd)
  have ht : ContDiffAt ℝ ω (fun z : G.Color × G.Color => G.plog (star (G.mat (G.lieExp z.1)) * G.mat (G.lieExp z.2))) (x,x) := by
    refine ContDiffAt.comp (g:=G.plog) _ ?_ he.contDiffAt
    simp only [G.mat_star_mul]
    exact G.plog_diff
  have hw : ContDiffAt ℝ ω (coat G) x :=
    ContDiffAt.fderiv (f:=fun p => move G (G.lieExp p)⁻¹) (g:=id) ht contDiffAt_id (by simp)
  let b := (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
  have hs : spin G = fun v => ((LinearMap.toMatrix b b) ((coat G v) : G.Color →ₗ[ℝ] G.Color)).det := by funext v; rw [LinearMap.det_toMatrix]; rfl
  rw [hs]; simp_rw [Matrix.det_apply]
  refine ContDiffAt.sum fun σ _ => ?_
  have hg : ContDiffAt ℝ ω (fun v => ∏ i, ((LinearMap.toMatrix b b) ((coat G v) : G.Color →ₗ[ℝ] G.Color)) (σ i) i) x := by
    refine contDiffAt_prod fun i _ => ?_
    simp only [LinearMap.toMatrix_apply]
    exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt).comp x (hw.clm_apply (g:=fun _ => b i) contDiffAt_const)
  exact ContDiffAt.const_smul _ hg

lemma coat_zero : coat G 0=ContinuousLinearMap.id ℝ G.Color := by
  unfold coat; rw [G.mat_lieExp_zero,inv_one]
  have he : HasFDerivAt id (ContinuousLinearMap.id ℝ G.Color) 0 := hasFDerivAt_id _
  apply (he.congr_of_eventuallyEq (f₁:=move G 1) ?_).fderiv
  filter_upwards [G.plog_left] with x hx
  simp only [move,one_mul]; exact hx

lemma spin_zero : spin G 0=1 := by rw [spin,coat_zero]; exact map_one LinearMap.det

lemma move_drifts {U : Set G.El} {s} (H : Geom G U s) {u : G.El} {b}
    (h : u*G.lieExp b ∈ U) : HasFDerivAt (move G u) (fderiv ℝ (move G u) b) b := by
  have he : ContDiff ℝ ω (fun a => G.mat (u*G.lieExp a)) := contDiff_const.mul G.exp_jet
  have hp : ContDiffAt ℝ ω (move G u) b := (H.2.2.2.2.2.2 _ h).comp (g:=G.plog) (f:=fun a => G.mat (u * G.lieExp a)) b he.contDiffAt
  exact (hp.differentiableAt (by simp)).hasFDerivAt

def imageHit (U : Set G.El) (g : G.El) := {x | g⁻¹*x∈U}

lemma spins {U : Set G.El} {s : Set G.Color} (H : Geom G U s) (hu : (1:G.El)∈U)
    {u : G.El} (b : G.Color) (h : u*G.lieExp b∈U) : spin G (move G u b)*(fderiv ℝ (move G u) b).det = spin G b := by
  let y := move G u b
  have hy : G.lieExp y=u * G.lieExp b := H.2.2.2.1 h
  let F := move G u
  have hw : move G (G.lieExp b)⁻¹ =ᶠ[nhds b] (move G (G.lieExp y)⁻¹ ∘ F) := by
    have hr : ∀ᶠ z in nhds b,u*G.lieExp z∈U := (continuous_const.mul G.lieExp_cont).continuousAt (H.1.mem_nhds h)
    filter_upwards [hr] with z hz
    have he : G.lieExp (F z)=u*G.lieExp z := H.2.2.2.1 hz
    simp only [comp_apply,move] at *; rw [he,hy]; simp
  have hp := move_drifts G H (u:=(G.lieExp y)⁻¹) (b:=F b) (by simpa only [show F b=y from rfl,inv_mul_cancel] using hu)
  have he := ((hp.comp b (move_drifts G H h)).congr_of_eventuallyEq hw).fderiv
  change fderiv ℝ (move G (G.lieExp b)⁻¹) b= _ at he
  change (coat G y).det * _=(fderiv ℝ _ b).det; rw [he]
  exact (LinearMap.det_comp _ _).symm
end YM.LocalH
