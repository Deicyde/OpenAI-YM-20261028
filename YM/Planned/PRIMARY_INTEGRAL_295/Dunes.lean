import YM.Planned.PRIMARY_INTEGRAL_295.Emits
import YM.Work.F02.Path

/-!
# Gauge log map at true τ>0 on finite stencil

Extension to real directions for integrating local chart derivatives,
never test that arbitrary extension outside the true buffered germ.
Proof also shows actual linear coefficient, and seal price Before any
Gaussian etc. Doesn't assume root methods already price analytic
continuation of kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Dunes
open Function Filter Set Metric Labels Lattice RG Source Source.Drops Wilson
open  Place
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {S : Finset Cover}

-- cost order phi, true increment relative slice mu, Tcp.
abbrev Dressed (S : Finset Cover) (G : Gauge) := (S→G.Color) × Dev S G × Dev S G

/-- unscaled. Actual last frame of edge. (Logs in color norm.) -/
def tent (v : Dressed S G) (i : Spot S) : G.El := G.lieExp (v.1 (first i)) * (G.lieExp (v.2.1 i) * G.lieExp (v.2.2 i)) * (G.lieExp (v.1 (last i)))⁻¹

def silk (v : Dressed S G) : Dev S G := fun i => G.plog (G.mat (tent v i))
lemma tent_root (i : Spot S) : tent (0:Dressed S G) i=1 := by simp [tent]
@[simp] lemma silk_root : silk (0:Dressed S G) = 0 := by funext i; simp [silk,tent_root]

lemma tent_mat (G : Gauge) (i : Spot S) : ContDiff ℝ ω fun v : Dressed S G=>G.mat (tent v i) := by
  unfold tent; simp_rw [G.mat_mul,G.mat_inv]
  let E (x : G.Color) := G.mat (G.lieExp x)
  have h1 : ContDiff ℝ ω fun v : Dressed S G => E (v.1 (first i)):= G.exp_jet.comp ((contDiff_apply ℝ G.Color (first i)).comp contDiff_fst)
  have h2 : ContDiff ℝ ω fun v : Dressed S G => E (v.1 (last i)) := G.exp_jet.comp ((contDiff_apply ℝ G.Color (last i)).comp contDiff_fst)
  have h3 : ContDiff ℝ ω fun v : Dressed S G => E (v.2.1 i):= G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp (contDiff_fst.comp contDiff_snd))
  have h4 : ContDiff ℝ ω fun v : Dressed S G => E (v.2.2 i):= G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp (contDiff_snd.comp contDiff_snd))
  exact (h1.mul (h3.mul h4)).mul (((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff).comp h2)

lemma silk_smooth (S : Finset Cover) (G : Gauge) : ContDiffAt ℝ ω (silk (S:=S) (G:=G)) 0 := by
  apply contDiffAt_pi.mpr; intro i
  exact (show ContDiffAt ℝ ω G.plog (G.mat (tent (0:Dressed S G) i)) from by rw [tent_root]; simpa using! G.plog_diff).comp (f:=fun v:Dressed S G=>G.mat (tent v i)) _ (tent_mat G i).contDiffAt

lemma tent_valid (G : Gauge) (i : Spot S) : ∀ᶠ v : Dressed S G in 𝓝 0,G.lieExp (silk v i) = tent v i := by
  have he : Continuous (fun v:Dressed S G=>tent v i) := by unfold tent; fun_prop
  have hp : Tendsto (fun v:Dressed S G=>tent v i) (𝓝 0) (𝓝 1) := by rw [← tent_root (G:=G) i]; exact he.continuousAt.tendsto
  exact hp.eventually G.plog_right

def archL (S : Finset Cover) (G : Gauge) : Dressed S G →L[ℝ] Dev S G :=
  LinearMap.toContinuousLinearMap {
    toFun v i := v.1 (first i) + v.2.1 i + v.2.2 i - v.1 (last i)
    map_add' a b := by funext i; simp; abel
    map_smul' r a := by funext i; simp [smul_sub,smul_add] }

lemma silk_first (S : Finset Cover) (G : Gauge) : fderiv ℝ (silk (S:=S) (G:=G)) 0=archL S G := by
  classical
  apply ContinuousLinearMap.ext; intro v; funext i
  let x:= (first i); let y:=last i
  let L:Dressed S G →L[ℝ] Dev S G:=fderiv ℝ silk 0
  let P:Dev S G→L[ℝ]G.Color:=ContinuousLinearMap.proj i
  let z(t:ℝ):=t • v
  have he : HasDerivAt z v 0:= by simpa only [one_smul] using! (hasDerivAt_id' (0:ℝ)).smul_const v
  let auth : G.Color := archL S G v i
  have h : HasDerivAt (P ∘ (silk (S:=S) (G:=G)) ∘ z) (L v i) 0 :=
    P.hasFDerivAt.comp_hasDerivAt 0 (((silk_smooth S G).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (x:=0) he (by simp [z]))
  have ht : HasDerivAt (fun t => G.mat (tent (z t) i)) (G.colorMat auth) 0 := by
    let g (x) (t:ℝ):=G.mat (G.lieExp (t • x))
    have h (x:G.Color) : HasDerivAt (g x) (G.colorMat x) 0 := G.expDiff_zero.comp_hasDerivAt_of_eq (x:=0)
      (show HasDerivAt (fun t:ℝ=>t • x) x 0 from by simpa only [one_smul] using! (hasDerivAt_id' (0:ℝ)).smul_const x) (by simp)
    have hx : (fun t=>G.mat (tent (z t) i))=(fun t => g (v.1 (first i)) t * (g (v.2.1 i) t*g (v.2.2 i) t)* star (g (v.1 (last i)) t)) := funext fun b=> by simp only [tent,z,G.mat_mul,G.mat_inv]; rfl
    rw [hx]; apply (((h (v.1 (first i))).mul ((h (v.2.1 i)).mul (h (v.2.2 i)))).mul (h (v.1 (last i))).star).congr_deriv
    simp only [Pi.mul_apply,g,zero_smul,G.mat_lieExp_zero,G.mat_one,mul_one,one_mul,star_one,G.colorMat_skew]
    change _=G.colorMat (_+_+_-_); rw [map_sub,map_add,map_add]; abel
  have he' : HasDerivAt (fun t=>silk (z t) i) (fderiv ℝ G.plog 1 (G.colorMat auth)) 0 :=
    ((G.plog_diff.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt_of_eq (x:=0) ht (by simp [z,tent_root])
  rw [Place.plog_velocity auth] at he'
  have ht := h.unique he'
  exact ht

/-- Pre-stencil coverage in actual identity neighborhoods. -/
structure Roof (S : Finset Cover) (G : Gauge) where
  stitch : Dressed S G→Dev S G
  smooth : ContDiff ℝ ∞ stitch
  launch : stitch 0=0
  rule : fderiv ℝ stitch 0=archL S G
  radius : ℝ
  radius_pos : 0 < radius
  supported : ∀ v, ‖v‖≤radius → (∀ i,G.lieExp (stitch v i)=tent v i) ∧ ‖stitch v‖ ≤ 1 -- clocks radius 1 OK.

set_option maxHeartbeats 800000 in
lemma bought (S : Finset Cover) (G : Gauge) : Nonempty (Roof S G) := by
  classical
  let E:= Dressed S G
  let H:E→Dev S G:= silk
  have hh : ContDiffAt ℝ ω H 0:= silk_smooth ..
  have ht: ∀ᶠ v : E in 𝓝 0, ContDiffAt ℝ ω H v ∧ (∀ i,G.lieExp (H v i)=tent v i) ∧ ‖H v‖≤1 := by
    have hv (i:Spot S) := tent_valid G i
    filter_upwards [hh.eventually (by simp),eventually_all.mpr hv, hh.continuousAt.norm.eventually (ge_mem_nhds (show ‖H 0‖<1 by simp [H]))] with v hz hq hp
    exact ⟨hz,hq,hp⟩
  obtain ⟨r,hr,h⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp ht
  let B : ContDiffBump (0:E) := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  let g (v:E) := B v • H v
  have hg (v:E) (he : ‖v‖≤r/2) : g v=H v := by change B v • H v = _; rw [B.one_of_mem_closedBall (show v∈ closedBall _ _ from by simpa using he),one_smul]
  have hs : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr; intro v
    by_cases he : v∈closedBall (0:E) r
    · exact B.contDiff.contDiffAt.smul ((h he).1.of_le le_top)
    have hz : g =ᶠ[𝓝 v] 0 := by
      filter_upwards [(isClosed_closedBall (x:=(0:E)) (ε:=r)).isOpen_compl.mem_nhds (show v∈_ from he)] with w hw
      have hw' : r ≤ dist w 0 := (lt_of_not_ge (show ¬ dist w 0 ≤ r from hw)).le
      rw [show g w=B w • H w from rfl, B.zero_of_le_dist hw',zero_smul]; rfl
    exact (show ContDiffAt ℝ ∞ (0 : E→ Dev S G) v from contDiffAt_const).congr_of_eventuallyEq hz
  have hG : g =ᶠ[𝓝 0] H := by
    filter_upwards [closedBall_mem_nhds (0:E) B.rIn_pos] with v hz; exact hg v (by simpa using hz)
  refine ⟨⟨g,hs,hG.self_of_nhds.trans silk_root,hG.fderiv_eq.trans (silk_first S G),r/2,B.rIn_pos,?_⟩⟩
  intro v hv; rw [hg v hv]; exact (h (by simpa using hv.trans B.rIn_lt_rOut.le)).2
end YM.Planned.PrimaryIntegral295.Dunes
