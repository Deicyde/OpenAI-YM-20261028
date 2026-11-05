import YM.ProjectorNext.PROJECTOR_CALIBRATION.Cylinders
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Divided

/-! # Pick and differentiate the Snap samples of the equation -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Labels Work Function Filter Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}

def course (J : Jet G) (h : ℝ) : Snap G d := trunk d (scaleJet J h)

lemma course_eq (J : Jet G) (h : ℝ) : course (d:=d) J h = stretch h (trunk d J) := rfl

lemma course_smooth (J : Jet G) : ContDiff ℝ ω (course (d:=d) J) := by
  refine contDiff_pi.mpr fun i => ?_
  have he {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (c : F) : ContDiff ℝ ω (fun t : ℝ => t^j • c) := (contDiff_id.pow j).smul contDiff_const
  exact he _ (J i.val)

lemma course_zero (J : Jet G) : course (d:=d) J 0=0 := by funext i; simp [course,trunk,scaleJet]

lemma course_pays (J : Jet G) (θ h : ℝ) : H.links d (θ • J) h=native H d (θ • course J h) := by
  unfold native; rw [scales H]
  congr 2
  funext j; unfold course trunk scaleJet
  simp [smul_comm _ θ]

namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

/-- Filter screen for mass of energy valve at outlet i. -/
def first (i : M.Outlet) : Coupon.Screen (Snap G d) := fun A =>
    (M.estimate (native H d A), M.tap i (sample (native H d A) (M.address i)))

/-- Slides eye for the differentiated weights. Use positive link through
`left`, don't change masks/ledger for the derivative tests. -/
def second (i : M.Outlet) (j : G.ColorIndex) : Coupon.Slides (Snap G d) := fun A =>
    let U := native H d A
    let x := M.address i
    let c := colors G j
    (M.estimate U, left M.estimate x c U, M.channel i U c, left (fun V => M.channel i V c) x c U)

private lemma picked {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : CoverConfig G → X) (h : Small G f) :
    ContDiffAt ℝ ω (fun A => f (native H d A)) 0 := by
  obtain ⟨s,hs⟩ := h
  exact hs.substituted fun i => (G02.linkGerm H d i.val).1.contDiffAt

lemma smooth_first (i : M.Outlet) : ContDiffAt ℝ ω (M.first i) 0 :=
  (picked M.estimate M.small_estimate).prodMk
    (picked _ ((Small.sample _).linear (M.tap i).toContinuousLinearMap))

lemma smooth_second (i : M.Outlet) (j : G.ColorIndex) : ContDiffAt ℝ ω (M.second i j) 0 := by
  refine (picked M.estimate M.small_estimate).prodMk
    ((picked _ (M.small_estimate.derivative (M.address i) (colors G j))).prodMk
      ((picked _ (M.small_channel i (colors G j))).prodMk (picked _ ((M.small_channel i (colors G j)).derivative (M.address i) (colors G j)))))

lemma first_zero (i : M.Outlet) : M.first i 0 = 0 := by simp [first,native_one,M.estimate_one,sample_one]
lemma second_zero (i : M.Outlet) (j : G.ColorIndex) : (M.second i j 0).1=0 := by simp [second,native_one,M.estimate_one]

lemma init_estimate : fderiv ℝ (fun A : Snap G d => M.estimate (native H d A)) 0 = ContinuousLinearMap.id _ _ := by
  let L := M.recover.toContinuousLinearMap
  have he := L.hasFDerivAt.comp (0:Snap G d) M.smooth.differentiableAt.hasFDerivAt
  have hh : (fun A : Snap G d => M.estimate (native H d A))= L ∘ bring H d M.loops := rfl
  rw [hh,he.fderiv]; exact ContinuousLinearMap.ext M.lift_radial

set_option maxHeartbeats 400000 in
lemma init_first (i : M.Outlet) (x : Snap G d) : fderiv ℝ (M.first i) 0 x =
    (x,M.tap i (linearSample H d (M.address i) x)) := by
  let A := fun y => M.estimate (native H d y)
  let Z := fun y => sample (native H d y) (M.address i)
  have ha : HasFDerivAt A (ContinuousLinearMap.id ℝ (Snap G d)) 0 := by
    rw [← init_estimate M]; exact ((picked M.estimate M.small_estimate).differentiableAt (by simp)).hasFDerivAt
  let L := (M.tap i).toContinuousLinearMap
  have hb : HasFDerivAt Z (linearSample H d (M.address i)) 0 :=
    ((sample_smooth H (M.address i) (d:=d)).differentiableAt (by simp)).hasFDerivAt
  have hh : M.first i=(fun y => (A y,(L ∘ Z) y)) := rfl
  rw [hh,(ha.prodMk (L.hasFDerivAt.comp 0 hb)).fderiv]; rfl

lemma complete (x : Snap G d) : (∑ i : M.Outlet, M.tap i (linearSample H d (M.address i) x)) = M.liftAll x := by
  rw [Fintype.sum_sigma]
  have ht (k : Level d) : (∑ i : ↥((M.filters k).addresses), M.tap ⟨k,i⟩ (linearSample H d (M.address ⟨k,i⟩) x)) =
      firing k (M.liftLeg k x) := by
    simp_rw [tap,address,LinearMap.comp_apply]
    change (∑ i : ↥((M.filters k).addresses), firing k ((M.filters k).Z _))= _
    rw [← map_sum (firing k (G:=G)), ← map_sum (M.filters k).Z] -- namespace linear?
    apply congr_arg; unfold liftLeg; rw [LinearMap.comp_apply]; apply congr_arg
    funext j
    rw [Finset.sum_apply]; simp [Pi.single_apply,Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl (fun i _ => ht i)]; unfold liftAll
  funext j; rw [Finset.sum_apply]; simp [firing,Finset.sum_pi_single]

lemma diagnostic (i : M.Outlet) (m : F.Index) (A : Snap G d) :
    M.valve F m i (gradient (native H d A) (M.address i).1 (M.address i).2) (native H d A)=
      Coupon.raw (shade F m) M.U (M.first i A) := rfl

lemma differentiated (i : M.Outlet) (m : F.Index) (j : G.ColorIndex) (A : Snap G d) :
    left (M.valve F m i (colors G j)) (M.address i) (colors G j) (native H d A)=
      Coupon.marked (shade F m) M.U (M.second i j A) := by
  obtain ⟨s,hs⟩ := M.small_estimate
  obtain ⟨q,hq⟩ := M.small_channel i (colors G j)
  have h1 := hs.authentic (native H d A) (M.address i) (colors G j)
  have h2 := hq.authentic (native H d A) (M.address i) (colors G j)
  have he := Cross.mix_deriv (shade F m) M.U h1 h2 |>.deriv
  simp_rw [Empirical.at_nil] at he -- beta reduce?
  exact he

end Machine
end YM.ProjectorNext.Calibration
