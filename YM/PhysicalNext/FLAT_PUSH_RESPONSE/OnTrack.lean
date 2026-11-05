import YM.Extra.WILSON_STARTUP.Comparable

/-!
# Mixed jets needed to control the response of a localized integral

Planes of one parameter t varying and fine normalized chart Y. Later will
use that at a moving center the stationary action Hessian jets of the
REPLACED integrand (Wilson as distinct from stationary PathData) agree with
the MATCH through 4. This module is calculus for that comparator, through
two horizontal and two vertical derivatives. In particular the later lower
bounds won't require exact stationarity of the Wilson action off the identity.
Only useful here on a fixed torus (width not priced).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter WilsonStartup.Change Set Metric Asymptotics
open scoped Topology BigOperators ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : ℝ × E → ℝ) (u : E)

def horizontal (F : ℝ × E → ℝ) (p : ℝ × E) : ℝ := deriv (fun t => F (t,p.2)) p.1
def east (p : ℝ × E) : ℝ := vert F p u



def Bends (F : ℝ × E → ℝ) (x : ℝ) := vert (vert F) (x,0)
def spot (F : ℝ × E → ℝ) (x : ℝ) (y : E) := Bends F x y y/2

variable {F} {p : ℝ × E}

lemma h_cf (hf : DifferentiableAt ℝ F p) : horizontal F p=fderiv ℝ F p (1,0) := by
  have ht : HasDerivAt (fun t : ℝ => (t,p.2)) (1,0) p.1 := (hasDerivAt_id' _).prodMk (hasDerivAt_const _ _)
  exact (hf.hasFDerivAt.comp_hasDerivAt _ ht).deriv
lemma e_cf (hf : DifferentiableAt ℝ F p) : east F u p=fderiv ℝ F p (0,u) := by
  have ht : HasFDerivAt (fun y : E => (p.1,y)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
    (hasFDerivAt_const ..).prodMk (hasFDerivAt_id _)
  exact DFunLike.congr_fun (hf.hasFDerivAt.comp _ ht).fderiv u

lemma horizontal_diff (hf : ContDiffAt ℝ ω F p) : ContDiffAt ℝ ω (horizontal F) p := by
  refine ((hf.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _=>((1,0):ℝ × E)) contDiffAt_const).congr_of_eventuallyEq ?_
  filter_upwards [hf.eventually (by simp)] with i hi
  exact h_cf (hi.differentiableAt (by simp))
lemma Bends_diff {x : ℝ} (hf : ContDiffAt ℝ ω F (x,0)) : ContDiffAt ℝ ω (Bends F) x :=
  (matches_self 2 hf).diff_vert.diff_vert.left.comp x (contDiffAt_id.prodMk contDiffAt_const)
lemma east_diff (hf : ContDiffAt ℝ ω F p) : ContDiffAt ℝ ω (east F u) p :=
  (matches_self 1 hf).diff_vert.left.clm_apply contDiffAt_const

lemma swap (hf : ContDiffAt ℝ ω F p) : horizontal (east F u) p=east (horizontal F) u p := by
  rw [h_cf ((east_diff u hf).differentiableAt (by simp)),e_cf u ((horizontal_diff hf).differentiableAt (by simp))]
  have ht (k : ℝ × E) : fderiv ℝ (fun p => fderiv ℝ F p k) p = ContinuousLinearMap.apply ℝ ℝ k ∘L fderiv ℝ (fderiv ℝ F) p :=
    ((ContinuousLinearMap.apply ℝ ℝ k).hasFDerivAt.comp p ((hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have he : east F u =ᶠ[𝓝 p] fun p => fderiv ℝ F p (0,u) :=
    (hf.eventually (by simp)).mono fun _ hi=> e_cf u (hi.differentiableAt (by simp))
  have hh : horizontal F =ᶠ[𝓝 p] fun p => fderiv ℝ F p (1,0) :=
    (hf.eventually (by simp)).mono fun _ hi=> h_cf (hi.differentiableAt (by simp))
  rw [he.fderiv_eq,hh.fderiv_eq,ht,ht]
  exact hf.isSymmSndFDerivAt_of_omega _ _

lemma east_bends {x : ℝ} (hf : ContDiffAt ℝ ω F (x,0)) : east (east F u) u (x,0)= Bends F x u u := by
  let Q : E → E →L[ℝ] ℝ := fun y => vert F (x,y)
  have hh : DifferentiableAt ℝ Q 0 := ((matches_self 1 hf).diff_vert.left.differentiableAt (by simp)).comp 0
    (differentiableAt_const _|>.prodMk differentiableAt_id)
  unfold east; change fderiv ℝ (ContinuousLinearMap.apply ℝ ℝ u ∘ Q) 0 u = _
  rw [((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp _ hh.hasFDerivAt).fderiv]; rfl

lemma two_raise {x : ℝ} (hf : ContDiffAt ℝ ω F (x,0)) : deriv (fun x => Bends F x u u) x= Bends (horizontal F) x u u := by
  have he : ∀ᶠ y : ℝ in 𝓝 x, ContDiffAt ℝ ω F (y,0) :=
    ((continuous_id.prodMk (continuous_const (y:=(0:E)))).tendsto x).eventually (hf.eventually (by simp))
  have hz : (fun y => Bends F y u u) =ᶠ[𝓝 x] fun y => east (east F u) u (y,0) := he.mono fun _ h=> (east_bends u h).symm
  rw [hz.deriv_eq]
  change horizontal (east (east F u) u) (x,0)= _
  rw [swap u (east_diff u hf),← east_bends u (horizontal_diff hf)]
  have hx : (fun i : E => horizontal (east F u) (x,i)) =ᶠ[𝓝 0] fun i : E => east (horizontal F) u (x,i) := by
    filter_upwards [((continuous_const.prodMk continuous_id : Continuous (fun i : E => ((x,id i):ℝ × E))).tendsto 0).eventually (hf.eventually (by simp))] with i hi
    exact swap u hi
  exact DFunLike.congr_fun hx.fderiv_eq u
lemma spot_raise {x : ℝ} (hf : ContDiffAt ℝ ω F (x,0)) : deriv (fun x => spot F x u) x= spot (horizontal F) x u := by
  unfold spot; rw [deriv_div_const,two_raise u hf]









-- Hand to the real dominated estimate along Y on these same jets


end YM.PhysicalNext.FlatResponse
