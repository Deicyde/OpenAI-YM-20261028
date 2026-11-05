import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineCharts


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# The actual analytic Q jet in relative (not absolute) coordinates

Prove at fixed finites first; these are NOT yet estimates across a period invoice,
but made for use AFTER replacing reads by the same functions on a reference patch.
No assumption of stochastic smoothness in U where the maximizing/minimizing branch isn't
necessarily near identity. Compare kjet and predicted tangent directly in real colors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff

variable {G : Gauge} {c f n : Side} (S : StepData c f)

abbrev Ground (G : Gauge) (n : Side) := Directions G n × G.Color
abbrev BondTest (G : Gauge) (n : Side) := Directions G n × Ground G n

def absolutize (a : Directions G n) : Config G n := fun i => G.lieExp (a i)

def qForecast (i : Bond c) (k : S.Choices) (u : BondTest G f) :=
  S.prediction (increment (absolutize u.2.1) u.1) k i

def chordColor (i : Bond c) (k : S.Choices) (u : BondTest G f) :=
  G.curvature (G.lieExp u.2.2*(qForecast S i k u)⁻¹)

def qTangent (i : Bond c) (k : S.Choices) (u : BondTest G f) :=
  G.curvature (qForecast S i k u*(qForecast S i k (0,u.2))⁻¹)

private lemma contour (hS : S.patch.Branches S.kernel G) (k : S.Choices) (i : Bond c) :
    let X := qForecast (G:=G) S i k
    ContDiffAt ℝ ω (fun u => G.mat (X u)) (0 : BondTest G f) := by
  intro X
  let h (u : BondTest G f) := increment (absolutize u.2.1) u.1
  have hl (i : Bond f) : ContDiff ℝ ω fun u => G.mat (h u i) := by
    unfold h increment absolutize; simp only [G.mat_mul]
    exact (G.exp_jet.comp ((contDiff_apply ℝ _ _).comp contDiff_fst)).mul
      (G.exp_jet.comp (((contDiff_apply ℝ _ _).comp contDiff_fst).comp contDiff_snd))
  have he (i : Bond f) : Tendsto (fun u => h u i) (𝓝 0) (𝓝 1) := by
    have hi : Continuous (fun u => h u i) := by unfold h increment absolutize; fun_prop
    have h0 : h 0 i=1 := by simp only [h,Prod.fst_zero,Prod.snd_zero,absolutize,increment,Pi.zero_apply,
      G.mat_lieExp_zero,mul_one]
    simpa only [h0] using! hi.tendsto (0:BondTest G f)
  let e := Work.E03.poleEquiv f
  let F (u : BondTest G f) : LogField G f := fun i => G.plog (G.mat (h u (e.symm i)))
  have hz : F 0=0 := by
    funext i
    simp only [F,h,increment,absolutize,Prod.snd_zero,Prod.fst_zero,Pi.zero_apply,G.mat_lieExp_zero,mul_one,G.mat_one,G.plog_one]
  have hh : ContDiffAt ℝ ω F 0 := by
    refine contDiffAt_pi.mpr fun i => ?_
    apply ContDiffAt.comp (g:=G.plog) (f:=fun u => G.mat (h u (e.symm i)))
    · simpa only [h,increment,absolutize,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,G.mat_lieExp_zero,mul_one,G.mat_one] using G.plog_diff
    exact (hl _).contDiffAt
  have hx : ∀ᶠ u in 𝓝 0, h u=represent (F u) := by
    filter_upwards [eventually_all.mpr fun i => (he i).eventually G.plog_right] with u hx
    funext i
    change h u i = G.lieExp (F u (e i))*1
    unfold F; rw [Equiv.symm_apply_apply,mul_one]; exact (hx _).symm
  have hC : ContDiffAt ℝ ω (fun u => G.mat (S.prediction (represent (F u)) k i)) 0 := by
    refine ContDiffAt.comp (g:=fun a => G.mat (S.prediction (represent a) k i)) _ ?_ hh
    exact hz.symm ▸ Push.prediction_cont S hS i k
  refine hC.congr_of_eventuallyEq (hx.mono fun u hu => ?_)
  change G.mat (S.prediction (h u) k i)=_; rw [hu]

/-- On one patch periodization (any c,f, constants not asserted uniform yet). -/
lemma bond_germ (h : S.patch.Branches S.kernel G) (k : S.Choices) (i : Bond c) :
    ContDiffAt ℝ ω (chordColor (G:=G) S i k) 0 ∧ ContDiffAt ℝ ω (qTangent (G:=G) S i k) 0 := by
  have he := contour S h k i
  let X := qForecast (G:=G) S i k
  have hs {f : BondTest G f → G.El} (hm : ContDiffAt ℝ ω (fun u => G.mat (f u)) 0) :
      ContDiffAt ℝ ω (fun u => G.mat (f u)⁻¹) 0 := by
    simp only [G.mat_inv]
    exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ hm
  constructor
  · apply curvature_diff_mat; simp only [G.mat_mul]
    exact (G.exp_jet.comp (contDiff_snd.comp contDiff_snd)).contDiffAt.mul (hs he)
  apply curvature_diff_mat; simp only [G.mat_mul]
  apply he.mul (hs ?_)
  exact (ContDiffAt.comp (g:=fun u => G.mat (X u)) (f:=fun u : BondTest G f => (0,u.2)) _ (by simpa only [Prod.snd_zero,Prod.mk_zero_zero] using he)
    (contDiffAt_const.prodMk contDiffAt_snd))

lemma bond_expense (h : S.patch.Branches S.kernel G) (k : S.Choices) (i : Bond c) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ u : BondTest G f, ∀ v : ℝ, ‖u‖ ≤ v → v ≤ r →
    let a := response (qTangent S i k) u.1 u.2
    let w := chordColor S i k
    DifferentiableAt ℝ (fun t : ℝ => qTangent S i k (t • u.1,u.2)) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ => G.mat (qForecast S i k (t • u.1,u.2))) 0 ∧
    ‖w u-(w (0,u.2)-a)‖ ≤ C*v^2 ∧ ‖w u‖ ≤ C*v ∧ ‖w (0,u.2)‖ ≤ C*v ∧ ‖a‖ ≤ C*v := by
  let F := chordColor (G:=G) S i k; let B := qTangent (G:=G) S i k
  have he := bond_germ S h k i
  have hh : qForecast (G:=G) S i k 0=1 := by
    have he : increment (absolutize (G:=G) (n:=f) 0) 0=(1:Config G f) := by
      ext j; simp only [increment,absolutize, Pi.zero_apply,G.mat_lieExp_zero,mul_one,Pi.one_apply]
    change S.prediction (increment (absolutize (G:=G) (n:=f) 0) 0) k i=1
    rw [he]; exact Push.settled S h i k
  have h0 : F 0=0 := by
    change G.curvature (G.lieExp 0 * (qForecast S i k 0)⁻¹)=_
    rw [hh]; simp
  have hr v : F (v,0) = (-1 : ℝ) • B (v,0) := by
    change G.curvature (G.lieExp 0*_⁻¹) = _ • G.curvature (_*(qForecast S i k 0)⁻¹)
    rw [hh, inv_one,mul_one,G.mat_lieExp_zero,one_mul,G.curvature_inv,neg_smul,one_smul]
  obtain ⟨C,r,hC,hr,H⟩ := charts F B he.1 he.2 _ h0 hr
  obtain ⟨s,hs,HB⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
    ((contour S h k i).eventually (by simp))
  refine ⟨C,min r s,hC,lt_min hr hs,?_⟩
  intro u v hu hv a w
  have hV : 0 ≤ v := (norm_nonneg u).trans hu
  obtain ⟨h1,h2,h3,h4,h5⟩ := H v hV (hv.trans (min_le_left ..)) u.1 u.2 ((le_max_left ..).trans hu) ((le_max_right ..).trans hu)
  rw [neg_smul,one_smul,← sub_eq_add_neg] at h2
  have hi : DifferentiableAt ℝ (fun u : BondTest G f => G.mat (qForecast S i k u))
      ((0:ℝ) • u.1,u.2) := (HB (by
        rw [Metric.mem_closedBall,dist_zero_right, zero_smul]; change max ‖(0 : Directions G f)‖ _ ≤ _
        rw [norm_zero,max_eq_right (norm_nonneg _)]
        exact (le_max_right ..).trans (hu.trans (hv.trans (min_le_right ..))))).differentiableAt (by simp)
  refine ⟨h1, ?_,h2,h3,h4,h5⟩
  have hg : Differentiable ℝ (fun t : ℝ => (t • u.1,u.2)) := by fun_prop
  exact hi.comp (f:=fun t : ℝ => (t • u.1,u.2)) (g:=fun u : BondTest G f => G.mat (qForecast S i k u)) 0 hg.differentiableAt
end YM.SectorNext.Remainder.Affine
