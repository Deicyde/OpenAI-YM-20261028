import YM.Work.C07.Euclid
import YM.Work.C07.Geometry



/-!
# Euclidean identity tested with the rescaled vector field `orbit`

Integration by parts takes place on joint position space with its given volume, including
on the time variables of the test. At this stage only differentiate hierarchy kernels on Conf.
Waves are evaluated, not differentiated. There is no demand that all p in the ambient space at
this parameter should map inside `strict`, only those in the (here compact) support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C07
open Table Analysis Boundary Mink Set Filter Function Complex MeasureTheory Bid
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L} {V : DiffPlan S}
  {h : S.RealSpin} {R : Rotation S} {Y : Waves S} {n : ℕ}

private lemma cancels {g : Points n → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {c : Points n → ℝ} {v : Points n} (hf : Differentiable ℝ c)
    (hz : ∀ p, fderiv ℝ c p v = 0) :
    Integrable (fun p => c p • fderiv ℝ g p v) ∧ (∫ p, c p • fderiv ℝ g p v) = 0 := by
  have hI : Integrable (fun p => c p • g p) :=
    (hf.continuous.smul hg.continuous).integrable_of_hasCompactSupport hc.smul_left
  have hJ : Integrable (fun p => c p • fderiv ℝ g p v) :=
    (hf.continuous.smul ((hg.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := v)))).integrable_of_hasCompactSupport
        (hc.fderiv_apply ℝ v).smul_left
  have hZ : Integrable (fun p => fderiv ℝ c p v • g p) := by
    simp only [hz, zero_smul]; exact integrable_zero _ _ _
  refine ⟨hJ,?_⟩
  have hC := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hZ hJ hI
    (fun p _ => hf p) (fun p _ => hg.differentiable (by simp) p)
  simpa [hz] using hC

private def posL (i : Fin n) (b : Axis) : Points n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => x i b
      map_smul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

/-- This vector field is divergence free. -/
lemma integral_orbit (a : SpaceAxis) (y : Heights n) (w : ℝ)
    {g : Points n → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    (∫ p, fderiv ℝ g p (orbit a y w p)) = 0 := by
  let s (i : Fin n) := Points.direction i a.castSucc
  let t (i : Fin n) := Points.direction i timeAxis
  let D₁ (i : Fin n) (p : Points n) := (p i a.castSucc) • fderiv ℝ g p (t i)
  let D₂ (i : Fin n) (p : Points n) := (w * stretchY y w p i) • fderiv ℝ g p (s i)
  have hd : a.castSucc ≠ timeAxis := Fin.castSucc_ne_last _
  have h₁ (i) : Integrable (D₁ i) ∧ (∫ p, D₁ i p) = 0 := by
    apply cancels hg hc (posL i a.castSucc).differentiable
    intro p
    rw [(posL i a.castSucc).fderiv]
    change Points.direction _ _ _ _ = _
    simp [Points.direction, hd]
  have h₂ (i) : Integrable (D₂ i) ∧ (∫ p, D₂ i p) = 0 := by
    let c (p : Points n) := w * (y i + w * posL i timeAxis p)
    have hz (p : Points n) : HasFDerivAt c (w • (w • posL i timeAxis)) p :=
      ((((posL i timeAxis).hasFDerivAt.const_smul w).const_add (y i)).const_smul w)
    refine cancels (c := c) hg hc (fun p => (hz p).differentiableAt) fun p => ?_
    rw [(hz p).fderiv]
    have he : posL i timeAxis (s i) = 0 := by
      change s i i timeAxis = _
      simp [s, Points.direction, hd.symm]
    simp [he]
  have he (p : Points n) : fderiv ℝ g p (orbit a y w p) = ∑ i, (D₁ i p-D₂ i p) := by
    simp only [orbit, D₁, D₂, s, t, map_sum, map_sub, map_smul]
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (f := fun i p => D₁ i p-D₂ i p) (by exact fun i _ => (h₁ i).1.sub (h₂ i).1)]
  exact Finset.sum_eq_zero fun i _ => by rw [integral_sub (h₁ i).1 (h₂ i).1, (h₁ i).2, (h₂ i).2, sub_self]

/-- Wave on the path. -/
def seen (Y : Waves S) (q : Fin n → S.Union) (y : Heights n) (z : ℂ) (p : Points n) :=
  Y.F n (scaledTimes y z p) (trace p) q

def errorTerm (Y : Waves S) (R : Rotation S) (a : SpaceAxis) (y : Heights n) (v : Fin n → S.Tag)
    (f : Joint n) (z : ℂ) (p : Points n) :=
  seen Y (ink v) y z p * testField a y z f p -
    z * (∑ i, seen Y (update (ink v) i (kick R a (v i))) y z p) * f p

private lemma seen_kick (hr : Y.Region T) (R : Rotation S) (p : Points n)
    (a : SpaceAxis) (y : Heights n) (v : Fin n → S.Tag) (i : Fin n)
    (w : ℝ) (hp : stretchY y w p ∈ east n) :
    seen Y (update (ink v) i (kick R a (v i))) y ((w : ℂ)*I) p =
      (-I) * S.classMoment T (fun j => (v j).1) (foldE y w p)
        (update (fun j => (v j).2) i (R.lie (v i).1 (Ortho.plane timeAxis a.castSucc) (v i).2)) := by
  let A := R.lie (v i).1 (Ortho.plane timeAxis a.castSucc) (v i).2
  let b : (j : Fin n) → S.Field (v j).1 := update (fun j => (v j).2) i ((-I) • A)
  let t (j : Fin n) : S.Tag := ⟨(v j).1, b j⟩
  have he : ink t = update (ink v) i (kick R a (v i)) := by
    funext j
    by_cases hh : j=i
    · subst j; simp [b, t, A, ink, kick]
    simp [b, t, ink, hh]
  rw [← he, seen, scaled_imag, show Y.F n _ _ (ink t) = S.useAt T (foldE y w p) t from
    hr.roots n t (trace p) (stretchY y w p) hp]
  exact MultilinearMap.map_update_smul _ _ _ _ _

private lemma field_flows (hO : R.Oriented T) (hR : R.Laws V h) (hS : T.Smooth)
    (hr : Y.Region T) (p : Points n) (a : SpaceAxis) (y : Heights n) (v : Fin n → S.Tag)
    (w : ℝ) (hp : stretchY y w p ∈ east n) :
    fderiv ℝ (fun x => S.useAt T (foldE y w x) v) p (orbit a y w p) =
      -(((w : ℂ)*I) * ∑ i, seen Y (update (ink v) i (kick R a (v i))) y ((w : ℂ)*I) p) := by
  let q := foldE y w p
  let Ω := Ortho.plane timeAxis a.castSucc
  have hq : q ∈ conf n := clear hp _
  have hd : DifferentiableAt ℝ (fun x => S.useAt T x v) q :=
    ((S.class_smooth T hS v q hq).contDiffAt ((conf_open n).mem_nhds hq)).differentiableAt (by simp)
  have H := ((hd.hasFDerivAt).comp p (fold_derivative y w p)).fderiv
  change fderiv ℝ ((fun x => S.useAt T x v) ∘ foldE y w) p _ = _
  rw [H, ContinuousLinearMap.comp_apply, orbit_image, map_smul]
  change w • D _ _ q = _
  rw [oriented_differential hO hR hS Ω hq]
  simp_rw [seen_kick hr R p a y v _ w hp, ← Finset.mul_sum, real_smul]
  have he (z b : ℂ) : -(z*I*(-I*b)) = z * -b := by
    calc
      _ = z * (I*I) * b := by ring
      _ = _ := by rw [I_mul_I]; ring
  exact (he _ _).symm

theorem error_imag (hO : R.Oriented T) (hR : R.Laws V h) (hS : T.Smooth)
    (hr : Y.Region T) (a : SpaceAxis) (y : Heights n) (v : Fin n → S.Tag) (f : Joint n)
    (w : ℝ) (hK : HasCompactSupport ⇑f)
    (he : ∀ p ∈ tsupport f, scaledTimes y ((w : ℂ)*I) p ∈ strict n) :
    (∫ p in tsupport f, errorTerm Y R a y v f ((w : ℂ)*I) p) = 0 := by
  have hE (p) (hp : p ∈ tsupport f) : stretchY y w p ∈ east n :=
    (scaled_strict_imag y w p).mp (he p hp)
  let u (p : Points n) := S.useAt T (foldE y w p) v
  have hU (p) (hp : p ∈ tsupport f) : ContDiffAt ℝ ∞ u p := by
    have hx : foldE y w p ∈ conf n := clear (hE p hp) _
    exact (((S.class_smooth T hS v (foldE y w p) hx).contDiffAt
      ((conf_open _).mem_nhds hx)).comp p (fold_smooth y w).contDiffAt)
  let g (p : Points n) := u p * f p
  have hG : tsupport g ⊆ tsupport f := tsupport_mul_subset_right
  have hc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _) hG
  have hg : ContDiff ℝ 1 g := contDiff_iff_contDiffAt.mpr fun p => by
    by_cases hx : p ∈ tsupport f
    · exact ((hU p hx).of_le (by norm_num)).mul (f.smooth 1).contDiffAt
    have H := notMem_tsupport_iff_eventuallyEq.mp (fun hi => hx (hG hi))
    exact contDiffAt_const.congr_of_eventuallyEq H
  calc
    _ = ∫ p in tsupport f, fderiv ℝ g p (orbit a y w p) := by
      apply setIntegral_congr_fun (isClosed_tsupport _).measurableSet
      intro p hp
      rw [errorTerm, test_imag]
      have hbase : seen Y (ink v) y ((w : ℂ)*I) p = u p := by
        rw [seen, scaled_imag]; exact hr.roots n v (trace p) (stretchY y w p) (hE p hp)
      change _ = fderiv ℝ (fun z => u z * f z) p (orbit a y w p)
      have hVp : fderiv ℝ u p (orbit a y w p) = _ :=
        field_flows hO hR hS hr p a y v w (hE p hp)
      rw [hbase, fderiv_fun_mul ((hU p hp).differentiableAt (by simp)) f.differentiableAt]
      simp [hVp]; ring
    _ = (∫ p, fderiv ℝ g p (orbit a y w p)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hp (hG h))]; rfl
    _ = 0 := integral_orbit a y w hg hc

end YM.Work.C07
