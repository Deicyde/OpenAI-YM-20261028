import YM.Push.LOOP_COEFFICIENT.Column
import YM.Work.F04.Calculus

/-!
# Common finite-period admission and the linear stationary quotient

Binds the same `Critical`, `Guessed`, `PriceGap`, analytic chart on the
actual group and physical path data. This node **uses**, not constructs,
the branch. `graft G S A` gives linear stationary log increments in rooted
coordinates, now suitable for uniform symbol calculations irrespective of F.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Lattice RG Wilson Matrix Function Filter Precision Exterior Tree Set
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f}

structure Admission (F : Forest S.ratio) (ρ : fieldDir G c 1 → AxisChart G F) (p : Clip) (W : PathData G)
    (A : Matrix (Body 1 f) (Body 1 c) ℝ) (P : ChartRatio G) : Prop where
  simple : G.Simple
  branches : S.patch.Branches S.kernel G
  paths : ∃ σ C Λ, W.Bounds p σ C Λ
  critical : Critical F p W ρ
  linear : Guessed F A ρ
  ratio : LocalRatio P
  gap : ∃ a, 0 < a ∧ PriceGap F p W a

def LinearStation (t : S.Choices) (p : Clip) (W : PathData G) (z : Scene G c f) :=
    ∀ a : Loops.Dual G c f, Work.F05.bend (strain t p W) 0 z (0,a) = 0

variable {F : Forest S.ratio} {p : Clip} {W : PathData G} {ρ : fieldDir G c 1 → AxisChart G F} {P : ChartRatio G}
    {A : Matrix (Body 1 f) (Body 1 c) ℝ}

section basic
variable {t : S.Choices} {σ C Λ : ℝ}

lemma vertical_quiet {x : Scene G c f} (hd : ContDiffAt ℝ ω (strain t p W) x)
    (h : AtStation p W t (vary 1 x.1) (vary 1 x.2)) : Work.F04.vert (strain t p W) x = 0 := by
  let U := vary (1:Loops.Inputs G c f) x.2
  have he : (fun v => strain t p W (x.1,v)) =ᶠ[𝓝 x.2]
      (completed p W t (vary 1 x.1) ∘ vary U) ∘ (fun v => displacement U (vary 1 v)) := by
    exact ((vary_diff (U:= (1:Loops.Inputs G c f)) (x:=x.2)).continuousAt.tendsto.eventually
      (vary_displacement U)).mono fun _ hi => congr_arg (completed p W t (vary 1 x.1)) hi.symm
  have hx : displacement U (vary 1 x.2) = 0 := displacement_self _
  have ht := (matDiffAt_const U).displacement (vary_diff (U:=1) (x:=x.2)) rfl
  rw [← (Work.F04.hasFDerivAt_slice _ x.1 x.2 (hd.differentiableAt (by simp))).fderiv,he.fderiv_eq,
    fderiv_comp x.2 (show DifferentiableAt ℝ _ _ from hx.symm ▸ h.smooth.differentiableAt (by simp)) (ht.differentiableAt (by simp)),
    hx,h.quiet,ContinuousLinearMap.zero_comp]

lemma generator_station (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hG : G.Simple) (v : Actors G c f) : LinearStation t p W (generator S v) :=
  fun _ => (Work.F05.bend_apply ..).trans (strain_ward h hw hG ..)

lemma LinearStation.add {x y : Scene G c f} (hx : LinearStation t p W x) (hy : LinearStation t p W y) : LinearStation t p W (x+y) :=
  fun a => by rw [map_add,LinearMap.add_apply,hx a,hy a,zero_add]
lemma LinearStation.sub {x y : Scene G c f} (hx : LinearStation t p W x) (hy : LinearStation t p W y) : LinearStation t p W (x-y) :=
  fun a => by rw [map_sub,LinearMap.sub_apply,hx a,hy a,sub_zero]

lemma LinearStation.kills {x : Loops.Dual G c f} (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ)
    (hG : G.Simple) (he : LinearStation t p W (0,x)) : cost (completed p W t 1) 1 *ᵥ x = 0 := by
  let J := strain t p W
  have hd : ContDiffAt ℝ ω J 0 := strain_diff h hw
  let L := ContinuousLinearMap.inr ℝ (Loops.Links G c) (Loops.Dual G c f)
  have hL := Work.F05.bend_comp_stationary (F:=J) (L.map_zero.symm ▸ hd)
    L.contDiff.contDiffAt (L.map_zero.symm ▸ strain_flat (t:=t) h hw hG)
  rw [map_zero,L.fderiv] at hL
  have hel : completed p W t (1:Config G c) ∘ vary (1:Loops.Inputs G c f) = J ∘ L := by
    ext v; simp only [J,L,strain,Function.comp_apply,ContinuousLinearMap.inr_apply, vary_zero]
  apply dotProduct_eq_zero
  intro v
  rw [dotProduct_comm,cost,bilinearAt_dotProduct,hel, ← Work.F05.bend_apply, hL]
  rw [← he v]; change Work.F05.bend J 0 _ _ = _
  exact hd.isSymmSndFDerivAt_of_omega _ _

end basic

namespace Admission
variable (h : Admission F ρ p W A P) (t : S.Choices)
include h

lemma sample_tendsto : Tendsto (sampled F ρ) (𝓝 0) (𝓝 0) := by simpa only [sampled_zero F h.critical] using! (sampled_diff F h.critical).continuousAt.tendsto

lemma sample_shell : ∀ᶠ x in 𝓝 (0:Loops.Links G c),
    AtStation p W t (vary 1 x) (vary 1 (sampled F ρ x).2) ∧ thermal F t p W ρ P (chartEquiv G c x) = correction W (sampled F ρ x) + expense t p W (sampled F ρ x) := by
  obtain ⟨a,ha,hA⟩ := h.gap
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  have he := thermal_eq t h.branches hw ha hA h.ratio h.critical
  have ht : Tendsto (chartEquiv G c) (𝓝 0) (𝓝 0) := by simpa using (chartEquiv G c).continuous.tendsto 0
  filter_upwards [sampled_joint F h.critical, ht.eventually he] with x hh he
  change _ ∧ _ = loop W (positions _) + scalar p W t (vary 1 x) _
  rw [← represent_chart,hh]; exact he

lemma flat_station : AtStation p W t (1:Config G c) (1:Loops.Inputs G c f) := by
  have he := (h.sample_shell t).self_of_nhds.1
  simpa only [sampled_zero _ h.critical,Prod.snd_zero,vary_zero] using! he

lemma vector_pos : 0 < (vector p W t 1 1).det := by
  have hc := completion_brace h.branches t (1:Loops.Inputs G c f) (beam_near h.branches t).self_of_nhds.patch
  exact ((h.flat_station t).stable _ (hc.symm ▸ (ghost_pos _ _ mu_pos).isUnit)).1

lemma invert_vector : IsUnit (vector p W t 1 1) := (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (h.vector_pos t).ne')

lemma modulo_gauge {x y : Scene G c f} (hx : LinearStation t p W x) (hy : LinearStation t p W y) (he : x.1 = y.1) :
    ∃ v, x = y + generator S (0,v) := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  let R := R_tot S (1:Loops.Inputs G c f)
  let L := completion t (1:Loops.Inputs G c f)
  have hL : IsUnit (L * R) := by
    rw [show L*R = _ from completion_brace h.branches t (1:Loops.Inputs G c f) (beam_near h.branches t).self_of_nhds.patch]; exact (ghost_pos _ _ mu_pos).isUnit
  let u := (L * R)⁻¹ *ᵥ (L *ᵥ (x.2-y.2))
  let z := x-y-generator S (0,u)
  have hz : z.1=0 := by simp [z,generator_fine,he]
  have ht : LinearStation t p W (0,z.2) := by rw [← hz]; exact (hx.sub hy).sub (generator_station h.branches hw h.simple _)
  have hQ := ht.kills h.branches hw h.simple
  have hT : L *ᵥ z.2 = 0 := by
    simp only [z,u,generator_fine, Prod.snd_sub]; rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      show R_tot S 1 = R from rfl,(L * R).mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp hL),Matrix.one_mulVec,sub_self]
  have hv : z.2 = 0 := (Matrix.mulVec_injective_of_isUnit (h.invert_vector t)) (a₂:=0) <| by
    rw [Matrix.mulVec_zero,vector,add_mulVec,← Matrix.mulVec_mulVec, hT, hQ,Matrix.mulVec_zero,add_zero]
  exact ⟨u,by have h := (Prod.ext hz hv : z=0); unfold z at h; rw [sub_eq_zero,sub_eq_iff_eq_add'] at h; exact h⟩

lemma sampled_linearStation (v : Loops.Links G c) : LinearStation t p W (fderiv ℝ (sampled F ρ) 0 v) := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  have ht := sampled_zero F h.critical; have hd := sampled_diff F h.critical
  let S := strain t p W
  have hf : ContDiffAt ℝ ω S 0 := strain_diff h.branches hw
  have he : Work.F04.vert S ∘ sampled F ρ =ᶠ[𝓝 0] 0 := by
    filter_upwards [h.sample_shell t, h.sample_tendsto.eventually (hf.eventually (by simp))] with x hh hv
    exact vertical_quiet hv hh.1
  have hj := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_zero, fderiv_comp 0 (ht.symm ▸ (Work.F04.vert_smooth S 0 hf).differentiableAt (by simp))
      (hd.differentiableAt (by simp)),ht] at hj
  intro a; rw [Work.F05.bend_apply,← Work.F04.vert_rate S _ hf]; exact DFunLike.congr_fun (DFunLike.congr_fun hj v) a

lemma graft_station (x : Loops.Links G c) : LinearStation t p W (graft G S A x) := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  rw [centered_graph F, ← sampled_stationary F A h.critical h.linear]
  exact (h.sampled_linearStation t _).add (generator_station h.branches hw h.simple _)
end Admission
end YM.Push.Loops
