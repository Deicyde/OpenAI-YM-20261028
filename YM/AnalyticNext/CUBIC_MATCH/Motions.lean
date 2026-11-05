import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Dues
import YM.Work.F03.Flat
import YM.Work.F05.Actions


set_option warningAsError false

/-!
# Motions of the actual unmasked actions

These apply even to the shared tags including minimizing branches. The
log coordinates are local, unmasked. Left gauge sign made explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch

open Filter Function Lattice RG Wilson Precision Exterior Tree Bid Work.F03 Work.F05
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius

variable {c f n : Side} {G : Gauge} {S : StepData c f}



section actions
variable {t : S.Choices} {p : Clip} {P : PathData G} {σ C Λ : ℝ}







lemma sum_rotated (R : Config G n → ℝ) (s : Signed) (U : Config G n) :
    Patch.average (fun h : Signed => R (pull h 0 (pull s 0 U))) =
      Patch.average (fun h : Signed => R (pull h 0 U)) := by
  simp_rw [Patch.average,pull_pull,affine,Signed.act_zero,add_zero]; congr 1
  exact Equiv.sum_comp (Equiv.mulLeft s) (fun h => R (pull h 0 U))



lemma quadratic_rotated (s : Signed) (U : Config G n) :
    secondTerm p P (pull s 0 U)=secondTerm p P U := sum_rotated (quadratic p P) s U

lemma quadratic_invariant (hP : P.Bounds p σ C Λ) (k : Site n → G.El) (U : Config G n) :
    secondTerm p P (gauge k U)=secondTerm p P U := by simp_rw [secondTerm,pull_gauge_zero,quadratic_gauge hP]




end actions

/-- Local log of unrestricted field. -/
def logged (U : Config G n) : Dir G n := fun i => G.plog (G.mat (U (i.1,axisEquiv.symm i.2)))
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {M : X → Config G n}

@[simp] lemma logged_zero : logged (1 : Config G n)=0 := by ext1 i; simp [logged]
lemma read_logged (e : M 0=1) (h : ∀ i, ContDiffAt ℝ ω (fun z => G.mat (M z i)) 0) :
    (fun z => represent (logged (M z))) =ᶠ[𝓝 0] M := by
  have he (i : Edge (Site n)) : ∀ᶠ z in 𝓝 0, G.lieExp (G.plog (G.mat (M z i)))=M z i := by
    have ht : Tendsto (fun z => M z i) (𝓝 0) (𝓝 (M 0 i)) :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (h i).continuousAt.tendsto
    rw [e,Pi.one_apply] at ht; exact ht.eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with z hz
  funext i; rw [represent_link,logged,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _,hz]

lemma logged_smooth (e : M 0=1) (h : ∀ i, ContDiffAt ℝ ω (fun z => G.mat (M z i)) 0) :
    ContDiffAt ℝ ω (fun z => logged (M z)) 0 := by
  refine contDiffAt_pi.mpr (fun i => ?_)
  let b : Edge (Site n) := (i.1,axisEquiv.symm i.2)
  have ht : ContDiffAt ℝ ω G.plog (G.mat (M 0 b)) := by
    rw [e,Pi.one_apply,G.mat_one]; exact G.plog_diff
  exact ht.comp (f:=fun z => G.mat (M z b)) _ (h _)



/-- Differentiate the log near the identity by reading back each exponential. -/
lemma logged_rate {M : ℝ → Config G n} (e : M 0=1)
    (h : ∀ i, ContDiffAt ℝ ω (fun z => G.mat (M z i)) 0) (v : Dir G n)
    (hv : ∀ i : Edge (Site n), HasDerivAt (fun t => G.mat (M t i)) (G.colorMat (v (i.1,coord i.2))) 0) :
    HasDerivAt (fun t => logged (M t)) v 0 := by
  let w := deriv (fun t => logged (M t)) 0
  have hw : HasDerivAt (fun t => logged (M t)) w 0 := ((logged_smooth e h).differentiableAt (by simp)).hasDerivAt
  apply hw.congr_deriv; funext ⟨x,i⟩
  obtain ⟨j,rfl⟩ := axisEquiv.surjective i
  apply G.colorMat_injective
  have hh := hasDerivAt_pi.mp hw (x,coord j)
  have he : HasFDerivAt (fun y => G.mat (G.lieExp y)) G.colorMat.toContinuousLinearMap
      (logged (M 0) (x,coord j)) := by rw [e,logged_zero]; exact G.expDiff_zero
  apply HasDerivAt.unique (f:=fun t => G.mat (M t (x,j))) _ (hv (x,j))
  apply (he.comp_hasDerivAt 0 hh).congr_of_eventuallyEq
  filter_upwards [read_logged e h] with t ht
  exact congr_arg G.mat ((congr_fun ht (x,j)).symm.trans (represent_link _ _))

lemma exp_smooth_const {v : X → G.Color} (h : ContDiffAt ℝ ω v 0) :
    ContDiffAt ℝ ω (fun t => G.mat (G.lieExp (v t))) 0 := G.exp_jet.contDiffAt.comp (f:=v) 0 h
lemma exp_line (v : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • v))) (G.colorMat v) 0 := by
  have he : HasDerivAt (fun t : ℝ => t • v) v 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v
  have hh : HasFDerivAt (fun y => G.mat (G.lieExp y)) G.colorMat.toContinuousLinearMap
      ((0:ℝ) • v) := by rw [zero_smul]; exact G.expDiff_zero
  exact hh.comp_hasDerivAt 0 he

/-- Left endpoint gauge convention, so this choice ADDS the pure gradient. -/
def rootTurn (u : fieldDir G n 0) (t : ℝ) (x : Site n) : G.El := G.lieExp (t • (-u (x,vac)))

lemma gauged_smooth {u : X → fieldDir G n 1} {k : X → Site n → G.El}
    (h : ContDiffAt ℝ ω u 0) (hp : ∀ i, ContDiffAt ℝ ω (fun z => G.mat (k z i)) 0) (e : Edge (Site n)) :
    ContDiffAt ℝ ω (fun z => G.mat (gauge (k z) (represent (u z)) e)) 0 := by
  simp_rw [Lattice.gauge,G.mat_mul,G.mat_inv]
  exact ((hp e.1).mul ((represent_smooth e).contDiffAt.comp (f:=u) 0 h)).mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hp _))

lemma turn_smooth {v : X → ℝ} (u : fieldDir G n 0)
    (h : ContDiffAt ℝ ω v 0) (x : Site n) : ContDiffAt ℝ ω (fun z => G.mat (rootTurn u (v z) x)) 0 :=
  exp_smooth_const (v:=fun z => v z • _) (h.smul contDiffAt_const)

@[simp] lemma turn_zero (u : fieldDir G n 0) : rootTurn u 0 = 1 := by
  funext i; simp only [rootTurn, zero_smul,G.mat_lieExp_zero,Pi.one_apply]
@[simp] lemma gauge_trivial (U : Config G n) : gauge (fun _ => 1) U=U := funext fun i => by simp [Lattice.gauge]

lemma turns_through (z : Dir G n) (u : fieldDir G n 0) :
    let F := fun t : ℝ => gauge (rootTurn u t) (represent (t • z))
    HasDerivAt (fun t => logged (F t)) (z+dColor G n 0 u) 0 := by
  intro F
  have he : F 0=1 := by
    change Lattice.gauge (rootTurn u 0) (represent ((0:ℝ) • z))=1
    rw [turn_zero,zero_smul,Precision.link_one]; exact gauge_trivial _
  refine logged_rate he (fun i => gauged_smooth (u:=fun t : ℝ => t • z) (by fun_prop)
    (turn_smooth u (v:=id) contDiffAt_id) i) _ (fun i => ?_)
  let a := i.1; let b := i.1+step i.2
  let v := z (i.1,coord i.2)
  have hh (x : Site n) : HasDerivAt (fun t => G.mat (rootTurn u t x)) (-(G.colorMat (u (x,vac)))) 0 :=
    (exp_line (-(u (x,vac)))).congr_deriv (map_neg ..)
  have hu : dColor G n 0 u (i.1,coord i.2) = u (b,vac)-u (a,vac) := by
    ext j; unfold dColor; rw [WithLp.ofLp_toLp,d_sites]; rfl
  have ht : HasDerivAt (fun t => G.mat (F t i))
      (-(G.colorMat (u (a,vac)))+G.colorMat v+G.colorMat (u (b,vac))) 0 := by
    simp only [F,Lattice.gauge,G.mat_mul,G.mat_inv]
    convert! ((hh a).mul (represent_rate z i)).mul (hh b).star using 1
    simp only [turn_zero, Pi.one_apply,G.mat_one,zero_smul,Precision.link_one,
      one_mul,mul_one, star_one,star_neg,G.colorMat_skew,neg_neg]; simp [a,b,v]
  apply ht.congr_deriv
  rw [Pi.add_apply,hu,map_add,map_sub]; unfold v; abel

end YM.CubicMatch
