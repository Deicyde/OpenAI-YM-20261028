import YM.Next.UV_STRESS.Shell
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free

/-!
# No-source divergence from the all-window translation charge

A quick investigate-the-interface result on the free-current needs.

With
T.lit actually delivered, the divergence of its J (as vector in the real
H type here under symmetry & conjugation) doesn't require an independent
Maxwell rank/correlation theorem producer (though ONE and erases etc still
do!).

Don't have T or lit yet.

No assumption equality of analytic
distributions even ON collisions, only ordinary continuity off them as here.

Using the common quotient even in the integration direction, thus no
uniqueness of representation of translated lattice currents/contours needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {L : Register G} {T : Table L} {W : DiffPlan T}

private def readStress (J : T.Stress) {n : ℕ} (x : Points n) (q : Fin n → T.Tag) (i b : Axis) (y : E4) :=
    T.useAt T (Points.cons y x) (Fin.cons ⟨4,J i b⟩ q)

/-- A Window at a specified center survives perturbation supported off all
inserts (including that center). Smooth perturbations also preserve genuine
integrability of the shell terms. -/
private lemma perturb {n : ℕ} {x : Points (n+1)} {χ θ : E4→ℝ} (h : Window x χ)
    (hp : ContDiff ℝ ∞ θ) (hv : HasCompactSupport θ) (hh : ∀ i : Fin (n+1), x i ∉ tsupport θ) : Window x (χ+θ) := by
  have he i : θ =ᶠ[𝓝 (x i)] 0 := notMem_tsupport_iff_eventuallyEq.mp (hh i)
  refine ⟨h.1.add hp,h.2.1.add hv,?_,fun i => ?_⟩
  · filter_upwards [h.2.2.1,he 0] with i hi hh; simp [hi,hh]
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (h.2.2.2 i),he i.succ] with j hj hj'; simp [hj,hj']

private lemma local_charge (J : T.Stress) (p : Parts T) (Y : SpinRows T)
    (h : T.Hierarchy) (hq : StressLaws T J p Y) {n : ℕ} (x : Points (n+1)) (hx : x∈conf _) (q : Fin (n+1) → T.Tag)
    (b : Axis) (θ : E4→ℝ) (hp : ContDiff ℝ ∞ θ) (hv : HasCompactSupport θ) (hh : ∀ i, x i ∉ tsupport θ) :
    ∑ a : Axis, ∫ z : E4, D (basis a) θ z • readStress J x q a b z = 0 := by
  classical
  obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx
  have hu := perturb hχ hp hv hh
  let F (a : Axis) (w : E4 → ℝ) (z : E4) := D (basis a) w z • readStress J x q a b z
  have hs (a) (f : E4→ℝ) (h₁ : ContDiff ℝ ∞ f) (h₂ : HasCompactSupport f)
      (h₃ : ∀ y ∈ tsupport (fderiv ℝ f), Points.cons y x ∈ conf _) : Integrable (F a f) := by
    refine cutoff_integrable (h₂.fderiv_apply ℝ (basis a)) ?_ ?_
    · exact continuous_iff_continuousAt.mpr fun y =>
        (dSmooth (m:=∞) (h₁.contDiffAt (x:=y)) (basis a) (by simp)).continuousAt
    exact fun y hy => (smooth_cons T h.smooth ⟨4,J a b⟩ q (h₃ y ((tsupport_comp_subset (g:=fun L : E4 →L[ℝ] ℝ => L (basis a)) rfl (fderiv ℝ f)) hy))).continuousAt
  have he : ∀ i, Integrable (F i θ) := by
    intro i; apply hs i θ hp hv; intro y hy
    apply Work.A01.conf_cons hx; intro i e; exact hh _ (e ▸ (tsupport_fderiv_subset ℝ hy))
  have hr (a) : F a (χ+θ) = fun y => F a χ y + F a θ y := by
    funext y
    change fderiv ℝ (χ+θ) y _ • _ = _
    rw [fderiv_add (hχ.1.differentiable (by simp) y) (hp.differentiable (by simp) y),_root_.add_apply,add_smul]; rfl
  let R a := hq.translation hx (Fin.tail q) (χ:=a)
  have hz (f) (hf : Window x f) (j : Axis) y : (↑(D (basis j) f y) : ℂ) *
      T.useAt T (Points.cons y x) (Fin.cons ⟨4,J j b⟩ (Fin.cons ⟨(q 0).1,(q 0).2⟩ (Fin.tail q)))=F j f y := by
    unfold F readStress; rw [show (⟨(q 0).1,(q 0).2⟩:T.Tag) = q 0 from rfl,Fin.cons_self_tail]; exact Complex.real_smul.symm
  have ht := (R (χ+θ) hu b (q 0).1 (q 0).2).trans (R χ hχ b (q 0).1 (q 0).2).symm
  unfold shellGrad at ht
  simp_rw [hz _ hu,hz _ hχ,hr] at ht
  rw [neg_inj] at ht
  simp_rw [integral_add (hs _ χ hχ.1 hχ.2.1 (fun _ z => window_separated hx hχ z)) (he _), Finset.sum_add_distrib] at ht
  exact add_eq_left.mp ht

-- IsOpen formulation for application of fundamental lemma: q may be empty
-- in general, but here insert a unit if necessary (see n=0 in source_free).
private theorem external (J : T.Stress) (p : Parts T) (Y : SpinRows T)
    (h : T.Hierarchy) (hq : StressLaws T J p Y) {n : ℕ} (x : Points (n+1)) (hx : x∈conf _) (q : Fin (n+1) → T.Tag)
    (b : Axis) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (readStress J x q a b) y = 0 := by
  let U := {y : E4|Points.cons y x∈conf _}
  let F (a : Axis) := readStress J x q a b
  let Q y := ∑ a : Axis, D (basis a) (F a) y
  have hp : IsOpen U := (conf_open _).preimage (by rw [shifting_head]; exact (headDir _).continuous.add continuous_const)
  have hf (a : Axis) z (hz : z∈U) : ContDiffAt ℝ ∞ (F a) z := smooth_cons T h.smooth ⟨4,J a b⟩ q hz
  have hh a z (hz : z∈U) : ContinuousAt (D (basis a) (F a)) z := (dSmooth (m:=∞) (hf a z hz) (basis a) (by simp)).continuousAt
  have hU : ContinuousOn Q U := continuousOn_finsetSum _ fun a _ z hz => (hh a z hz).continuousWithinAt
  suffices ∀ᵐ z : E4 ∂volume.restrict U, Q z=0 from
    Measure.eqOn_of_ae_eq (show Q =ᵐ[volume.restrict U] (fun _ => 0) from this) hU continuousOn_const (by rw [hp.interior_eq]; exact subset_closure) hy
  have he : ∀ᵐ z : E4 ∂volume,z∈U → Q z=0 := by
    refine hp.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hU.locallyIntegrableOn hp.measurableSet) fun θ hθ hχ ht => ?_
    have h₁ (a : Axis) : Integrable (fun z : E4 => D (basis a) θ z • F a z) := by
      refine cutoff_integrable (hχ.fderiv_apply ℝ _) (hθ.continuous_fderiv (by simp)|>.clm_apply continuous_const) ?_
      exact fun z hz => (hf a z (ht (tsupport_fderiv_apply_subset ℝ _ hz))).continuousAt
    have h₂ (a : Axis) : Integrable (fun z : E4 => θ z • D (basis a) (F a) z) :=
      cutoff_integrable hχ hθ.continuous fun z hz => hh a z (ht hz)
    have he (a : Axis) : (∫ z : E4, θ z • D (basis a) (F a) z) = -(∫ z : E4, D (basis a) θ z • F a z) :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (h₁ a) (h₂ a)
        (cutoff_integrable hχ hθ.continuous (fun z hz => (hf a z (ht hz)).continuousAt))
        (fun z _ => hθ.differentiable (by simp) z) (fun z hz => (hf a z (ht hz)).differentiableAt (by simp))
    have hv i : x i∉U := by
      intro he; have he := (show Points.cons (x i) x∈conf _ from he)
      exact Fin.succ_ne_zero i ((show _ = _ from he (a₁:=i.succ) (a₂:=0) (by simp [Points.cons])))
    unfold Q; simp_rw [Finset.smul_sum]; rw [integral_finsetSum _ (fun a _ => h₂ a)]
    simp_rw [he,Finset.sum_neg_distrib]
    rw [show (∑ a : Axis, ∫ z : E4,D (basis a) θ z • F a z)=0 from local_charge J p Y h hq x hx q b θ hθ hχ (fun i h => hv i (ht h)),neg_zero]
  exact ((ae_restrict_of_ae he).and (ae_restrict_mem hp.measurableSet)).mono fun _ h => h.1 h.2

/-- All-spectator quotient calculation. No assumptions that any rotation
response produced the flux (only the stated all-window identities are used),
or support near contact handled on separated Schwartz cutoffs. Includes n=0. -/
theorem source_free (J : T.Stress) (p : Parts T) (Y : SpinRows T)
    (h : T.Hierarchy) (hd : W.Derivatives T) (hp : StressLaws T J p Y) (b : Axis) :
    ∑ a, W.deriv 4 a (J a b) = 0 := by
  apply T.field_ext h.laws.toSymmetric; intro n q x hx
  rw [← front_eval, ← front_eval, map_zero,map_sum]
  simp_rw [front_eval]
  -- don't actually need unit for n=0
  have hu : x = Points.cons (x 0) (Points.tail x) := by
    ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons,Points.tail]
  let z := Points.tail x
  have hz : Points.cons (x 0) z∈conf _ := hu ▸ hx -- direction maybe
  -- avoid rewriting recursively
  have he (a : Axis) :
      T.useAt T x (Fin.cons ⟨5,W.deriv 4 a (J a b)⟩ q)= D (basis a) (readStress J z q a b) (x 0) :=
    (congr_arg (fun s => T.useAt T s (Fin.cons ⟨5,W.deriv 4 a (J a b)⟩ q)) hu).trans (D_cons h.smooth W hd (J a b) q hz a).symm
  simp_rw [he]
  cases n with
  | succ n => exact external J p Y h hp z (Points.tail_in hx) q b hz
  | zero =>
    apply Finset.sum_eq_zero
    intro i _
    let y := (0 : Points 1)
    rw [show readStress J z q i b = fun _ => T.useAt T y (Fin.cons ⟨4,J i b⟩ q) from ?_]
    · simp [D]
    funext j
    have hr : Points.cons j z = Points.across j y := by
      ext1 u; fin_cases u; simp [Points.cons,y]
    unfold readStress; rw [hr]; exact (show T.useAt T (Points.across j y) (Fin.cons ⟨4,J i b⟩ q) = _ from slide_disc h y _ (fun _ _ _ => Subsingleton.elim _ _) (Fin.cons ⟨4,J i b⟩ q)) -- cast?

namespace FreeInput
variable {C : Family G}
/-- Reduced remaining FreeDiv prerequisites. Also available at Lit stage
without any physical hierarchy. -/
theorem sourced (i : FreeInput C)
    (h : Surjective (currentDiv i.T.W i.kernels.spin i.lit.hers))
    (hp : Module.finrank ℝ (LinearMap.ker (currentDiv i.T.W i.kernels.spin i.lit.hers))=1)
    (ht : i.T.J∈KernelSpace i.kernels.spin) : i.Divergence :=
  ⟨h,hp,ht,source_free i.T.J _ _ i.kernels i.lit.pales i.lit.delta⟩

end FreeInput
end YM.UVNext.Grade
