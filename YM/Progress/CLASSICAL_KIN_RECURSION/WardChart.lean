import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import YM.Progress.CLASSICAL_KIN_RECURSION.Colour
import YM.Work.F03.Flat


set_option warningAsError false

/-!
# Analytic chart for gauge changes at Ward leading order. We use the
finite-dimensional inverse chart *locally*, corresponding to the
original extraction. No assertion of complex equivariance.
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin
open Lattice RG Laurent Exterior Wilson Precision Bid
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

abbrev Booth (G : Gauge) (n : Side) := fieldDir G n 1 × fieldDir G n 0

def caps (g : G.El) (x : Booth G n) (i : Site n) := g*G.lieExp (-(x.2 (i,vac)))

def laced (g : G.El) (v : Booth G n) := Lattice.gauge (caps g v) (represent v.1)
def translatedLog (U : Config G n) : Dir G n := fun i=> G.plog (G.mat (U (i.1,axisEquiv.symm i.2)))
def rotatedLog (g : G.El) (v : Booth G n) : Dir G n := translatedLog (laced g v)

variable (g : G.El)
lemma laced_zero : laced g (0:Booth G n)=1 := by funext e; simp [laced,Lattice.gauge,caps]
lemma log_zero : translatedLog (1:Config G n)=0 := by ext; simp [translatedLog]
lemma chart_zero : rotatedLog g (0:Booth G n)=0 := by rw [rotatedLog,laced_zero]; exact log_zero
lemma laced_norm (e : Edge (Site n)) : ContDiffAt ℝ ω (fun v : Booth G n => G.mat (laced g v e)) 0 := by
  have hk (i : Site n) : ContDiffAt ℝ ω (fun v : Booth G n => G.mat (caps g v i)) 0 := by
    simp only [caps,G.mat_mul]; apply ContDiffAt.mul contDiffAt_const
    exact G.exp_jet.contDiffAt.comp (f:=fun v : Booth G n=>-(v.2 (i,vac))) 0
      (((contDiffAt_apply ℝ G.Color _ _).comp (f:=Prod.snd) _ contDiffAt_snd).neg)
  unfold laced Lattice.gauge; simp only [G.mat_mul,G.mat_inv]
  apply ContDiffAt.mul
  · exact (hk e.1).mul ((Work.F03.represent_smooth e).contDiffAt.comp (f:=Prod.fst) (0:Booth G n) contDiffAt_fst)
  exact ((starL ℝ:G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt).comp (0:Booth G n) (hk _)
lemma laced_smooth : ContDiffAt ℝ ω (rotatedLog (n:=n) g) 0 := by
  refine contDiffAt_pi.mpr fun i => ContDiffAt.comp (f:=fun v => G.mat (laced g v (i.1,axisEquiv.symm i.2))) (0:Booth G n) ?_ (laced_norm _ _)
  rw [laced_zero, Pi.one_apply,G.mat_one]; exact G.plog_diff

lemma laced_germ : (fun v : Booth G n=>represent (rotatedLog g v)) =ᶠ[𝓝 0] laced g := by
  have ht e : ∀ᶠ v in 𝓝 (0:Booth G n), G.lieExp (G.plog (G.mat (laced g v e)))=laced g v e := by
    have hx : ContinuousAt (fun v : Booth G n=>laced g v e) 0 :=
      ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff).mpr ((laced_norm _ _).continuousAt.tendsto)
    have hp := hx.tendsto; rw [laced_zero, Pi.one_apply] at hp
    exact hp.eventually G.plog_right
  filter_upwards [eventually_all.mpr ht] with v hv
  funext e; rw [Work.F03.represent_link,rotatedLog,translatedLog, show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _]; exact hv e

private lemma exp_ray (c : G.Color) : HasDerivAt (fun s : ℝ=> G.mat (G.lieExp (s • c))) (G.colorMat c) 0 := by
  simp only [G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat c) (0:ℝ)
private lemma knit (e : Edge (Site n)) (x : fieldDir G n 0) : dColor G n 0 x (e.1,coord e.2)=x (e.1+step e.2,vac)-x (e.1,vac) := by
  ext i; exact d_sites ..

private lemma laced_deriv (e : Edge (Site n)) (v : Booth G n) :
    HasDerivAt (fun s : ℝ => G.mat (laced g (s • v) e))
      (G.colorMat (Spools.reflects 1 n g (v.1+dColor G n 0 v.2) (e.1,coord e.2))) 0 := by
  let m (i : Site n):=v.2 (i,vac)
  have hx (i : Site n) : HasDerivAt (fun s : ℝ=> G.mat (caps g (s • v) i)) (G.mat g*G.colorMat (-(m i))) 0 := by
    simp only [caps,G.mat_mul]
    change HasDerivAt (fun s:ℝ=>G.mat g*G.mat (G.lieExp (-(s • m i)))) _ _; simp_rw [← smul_neg]
    exact (exp_ray (-(m i))).const_mul _
  let b := v.1
  unfold laced Lattice.gauge; simp only [G.mat_mul,G.mat_inv]
  have hk:=((hx e.1).mul (Work.F03.represent_rate b e)).mul (hx (e.1+step e.2)).star
  convert! hk using 1
  simp only [Spools.reflects,G.mat_adjoint,Pi.add_apply,knit,Gauge.conjugate,map_add,map_sub,map_neg,G.colorMat_skew,
    zero_smul,caps,Prod.snd_zero, Pi.zero_apply, neg_zero,G.mat_lieExp_zero,link_one,
    Pi.one_apply,G.mat_one, mul_one,Pi.mul_apply,star_mul,star_neg, neg_neg,b,m]
  -- expression should `(X v-x₀ +x₁)`
  noncomm_ring

lemma spell (v : Booth G n) : fderiv ℝ (rotatedLog g) 0 v=Spools.reflects 1 n g (v.1+dColor G n 0 v.2) := by
  let w:= fderiv ℝ (rotatedLog g) 0 v
  have hw : HasDerivAt (fun t : ℝ => rotatedLog g (t • v)) w 0 := Push.side _ ((laced_smooth g).differentiableAt (by simp)) v
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0):=by simpa using (show Continuous (fun t : ℝ => t • v) from by fun_prop).tendsto 0
  have he (e : Edge (Site n)) : G.colorMat (w (e.1,coord e.2))=G.colorMat (Spools.reflects 1 n g (v.1+dColor G n 0 v.2) (e.1,coord e.2)) := by
    have hp (i) := hasDerivAt_pi.mp hw i
    let q (s : ℝ):=rotatedLog g (s • v) (e.1,coord e.2)
    have hd : HasFDerivAt (fun c=>G.mat (G.lieExp c)) G.colorMat.toContinuousLinearMap (q 0):=by
      unfold q; rw [zero_smul,chart_zero]; exact G.expDiff_zero
    refine ((hd.comp_hasDerivAt 0 (hp (e.1,coord e.2))).congr_of_eventuallyEq ?_).unique (laced_deriv g e v)
    filter_upwards [ht.eventually (laced_germ g)] with s hs
    rw [show laced g _=_ from hs.symm,Work.F03.represent_link]; rfl
  funext ⟨a,i⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective i
  exact G.colorMat_injective (he (a,j))
end YM.Progress.ClassicalKin
