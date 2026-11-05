import YM.AnalyticNext.QUARTIC_MATCH.Pre.Grounded
import YM.AnalyticNext.QUARTIC_MATCH.Ward

/-!
# Installing infinitesimal redundancy in the actual centered action

Box and tangent signs. Used to buy the cheaper joint Gaussian bounds
for the real order-four correction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Pre
open Filter Function Lattice RG Wilson Precision Push Bid Exterior Bloch Matrix Tree Work.F03 Work.F04
open Joint Knot
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
namespace Centered
variable {G : Gauge} {c f : Side}
local notation "Y" => Vertical G c f
local notation "Z" => JointSpace G c f

variable (S : StepData c f) (t : S.Choices)
local notation "X" => LieSpin G f
local notation "α" => Z × X

def moveA (z : α) := adjust (z.1.2.1,z.2)

def moving (z : α) := twist S t z.1.2 * (power z.2 ∘ S.ratio.embed)⁻¹ * centroid S t.1 (moveA z)

def move (z : α) : Y := (moveA z, record (moving S t z))

lemma moveA_id : moveA (0:α)=0 := adjust_zero
lemma movedA : ∀ᶠ z : α in 𝓝 0,represent (moveA z)=Lattice.gauge (power z.2) (represent z.1.2.1) := by
  let T (z : α) := (z.1.2.1,z.2)
  exact ((show Continuous T by unfold T; fun_prop).tendsto 0).eventually (Joint.adjusted)
lemma smoothA : ContDiffAt ℝ ω (moveA (c:=c) (f:=f) (G:=G)) 0 :=
    adjust_analytic.comp (f:=fun z : α => (z.1.2.1,z.2)) (0:α) (by fun_prop)

variable (h : S.patch.Branches S.kernel G)
include h
lemma moveθ_smooth (i : Site c) : Smooth (0:α) (fun z => moving S t z i) := by
  apply Smooth.mul (Q:=fun z => twist S t z.1.2 i * (power z.2 (S.ratio.embed i))⁻¹)
    (V:=fun z => centroid S t.1 (moveA z) i)
  · exact ((show Smooth (0:α) (fun z => twist S t z.1.2 i) from
      (twist_smooth S t h i).comp (f:=fun z : α => z.1.2) (0:α) (by fun_prop))).mul
      ((power_jet (G:=G) (S.ratio.embed i)).inv.comp (f:=Prod.snd) (0:α) contDiffAt_snd)
  have he : ContDiffAt ℝ ω (fun a => G.mat (centroid S t.1 a i)) (moveA (0:α)) := by
    rw [moveA_id]; exact center_smooth S h t.1 i
  exact he.comp (f:=moveA (c:=c)) (0:α) smoothA
lemma moveθ_id : moving S t (0:α) = 1 := by simp [moving,twist_one S t h,power_zero,moveA_id,Knot.at_identity S h]
lemma move_start : move S t (0:α) = 0 := by rw [move,moveA_id,moveθ_id S t h,record_power]; rfl
lemma moves_jet : ContDiffAt ℝ ω (move S t (G:=G)) 0 := smoothA.prodMk (write_smooth (moveθ_smooth S t h) (moveθ_id S t h))
omit h in
lemma move_null : ∀ᶠ z : Z in 𝓝 0,move S t (z,0)=z.2 := by
  have ha : ∀ᶠ z : Dir G f in 𝓝 0, records (represent z)=z := by
    let q (z : Dir G f) (i : Body 1 f) := G.plog (G.mat (G.lieExp (z i)))
    have hh i : ∀ᶠ v : Dir G f in 𝓝 0,q v i=v i := ((continuous_apply i).tendsto (0:Dir G f)).eventually G.plog_left
    filter_upwards [eventually_all.mpr hh] with a ha; funext i
    rw [records,represent_link]; rcases i with ⟨x,i⟩
    change G.plog (G.mat (G.lieExp (a (x,axisEquiv (axisEquiv.symm i)))))=_
    rw [axisEquiv.apply_symm_apply]; exact ha _
  have hT : Tendsto (fun z : Z => z.2.1) (𝓝 0) (𝓝 0) := (show Continuous (fun z : Z => z.2.1) by fun_prop).tendsto 0
  have hU : Tendsto (fun z : Z => z.2.2) (𝓝 0) (𝓝 0) := (show Continuous (fun z : Z => z.2.2) by fun_prop).tendsto 0
  filter_upwards [hT.eventually ha,hU.eventually write_left] with z hz hw
  have he : moveA (z,0)=z.2.1 := by unfold moveA adjust; rw [power_zero,Joint.trivial,hz]
  refine Prod.ext he ?_
  change record (moving S t (z,0))=_
  unfold moving twist
  dsimp only
  rw [power_zero, show (1 : Spin G f) ∘ S.ratio.embed=1 from rfl, inv_one,mul_one,he,inv_mul_cancel_right]; exact hw

lemma free_spin {p : Clip} {W : PathData G} {σ C Λ : ℝ} (hp : W.Bounds p σ C Λ) : ∀ᶠ z : α in 𝓝 0,
    cash S t p W (z.1.1,move S t z)=cash S t p W z.1 := by
  filter_upwards [write_right (moveθ_smooth S t h) (moveθ_id S t h),movedA] with z hz hh
  have he : Lattice.gauge (power (record (moving S t z))) (send S t (moveA z)) = Lattice.gauge (power z.1.2.2) (send S t z.1.2.1) := by
    rw [show power (record _)=_ from hz,send,hh,predicted h]
    rw [moving,gaugeTwice,gaugeTwice,send, gaugeTwice]
    rw [mul_inv_cancel_right,inv_mul_cancel_right]; rfl
  unfold cash move; rw [he,hh, Work.F05.mainTerm_gauge hp]

/-- Scalar site operator with actual patch weights. -/
def palette : Matrix (Body 0 c) (Body 0 f) ℝ := LinearMap.toMatrix' (LinearMap.pi fun i : Body 0 c =>
    ∑ a, S.patch.weight a • (LinearMap.proj (atPoint S i.1 a,vac)))
def sitePart {n : Side} (u : LieSpin G n) (j : G.ColorIndex) : form 0 n := fun i => u i.1 j

def remit (u : LieSpin G f) : LieSpin G c := fun i => WithLp.toLp 2 (fun j => (palette S *ᵥ sitePart u j) (i,vac))
def depart (u : LieSpin G f) : Y := (-gradient u,-remit S u)

omit h in
lemma palette_site (u : form 0 f) (i : Body 0 c) : (palette S *ᵥ u) i=∑ a, S.patch.weight a*u (atPoint S i.1 a,vac) := by
  simp only [palette,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.smul_apply]; rfl
omit h in
lemma parts_grad {n : Side} (u : LieSpin G n) (j : G.ColorIndex) : parts G 1 (gradient u) j=d 0 n *ᵥ sitePart u j := by
  funext ⟨x,i⟩; obtain ⟨i,rfl⟩ := axisEquiv.surjective i
  rw [show axisEquiv i=coord i from rfl,d_sites]
  simp only [parts,gradient,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i]; rfl
lemma move_rate (u : LieSpin G f) : vMap (move S t) 0 u=depart S u := by
  let r (z : ℝ) := ((0:Z), z • u)
  have hs : HasDerivAt (fun s : ℝ => moveA (r s)) (-gradient u) 0 := by
    have hd := Push.side Joint.adjust (adjust_analytic.differentiableAt (by simp)) ((0:Dir G f),u); rw [adjust_rate,zero_sub] at hd
    simpa [moveA,r] using hd
  have hu : HasDerivAt (move S t ∘ r) (vMap (move S t) 0 u) 0 := by
    have hv : HasDerivAt r (0,u) 0 := (hasDerivAt_const _ _).prodMk (show HasDerivAt (fun s : ℝ => s • u) u 0 by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const u)
    have hr : r 0=0 := Prod.ext rfl (zero_smul ..)
    have ht : HasFDerivAt (move S t) (fderiv ℝ (move S t) (0:α)) (r 0) := by rw [hr]; exact ((moves_jet S t h).differentiableAt (by simp)).hasFDerivAt
    exact ht.comp_hasDerivAt _ hv
  have H := (ContinuousLinearMap.fst ℝ (Dir G f) (LieSpin G c)).hasFDerivAt.comp_hasDerivAt _ hu
  refine Prod.ext (H.unique hs) ?_
  funext i; apply G.colorMat_injective
  let a (s : ℝ) := (move S t (r s)).2
  have hk : a 0=0 := by unfold a r; rw [zero_smul]; exact congr_arg Prod.snd (move_start S t h)
  have ha : HasDerivAt (fun s : ℝ => G.mat (moving S t (r s) i)) (G.colorMat (-(remit S u) i)) 0 := by
    let F (v : Dir G f) := G.mat (centroid S t.1 v i)
    have hT : DifferentiableAt ℝ F 0 := (center_smooth S h t.1 i).differentiableAt (by simp)
    have hz : moveA (r 0)=(0:Dir G f) := by unfold r; rw [zero_smul]; exact moveA_id
    have hR : HasDerivAt (fun s => F (moveA (r s))) (G.colorMat (offset S (-gradient u) i)) 0 := by
      rw [← (Push.side F hT (-gradient u)).unique (shift_rate S h t.1 i (-gradient u))]
      exact (hz.symm ▸ hT.hasFDerivAt : HasFDerivAt F _ (moveA (r 0))).comp_hasDerivAt (f:=fun s => moveA (r s)) _ hs
    have he : offset S (-gradient u) i = u (S.ratio.embed i)-remit S u i := by
      ext j
      change -((fixRoot S) *ᵥ (-(parts G 1 (gradient u) j))) _ = u _ j - (palette S *ᵥ sitePart u j) _
      rw [parts_grad, Matrix.mulVec_neg, Pi.neg_apply, neg_neg, psi_proj,palette_site]; rfl
    have hh (s) : moving S t (r s) i=(power (s • u) (S.ratio.embed i))⁻¹ * centroid S t.1 (moveA (r s)) i := by
      have hy : moving S t (r s)=(power (s • u) ∘ S.ratio.embed)⁻¹ * centroid S t.1 (moveA (r s)) := by
        unfold moving
        change twist S t (0:Y)*_ * _ = _
        rw [twist_one S t h]; exact congr_arg (· * centroid S t.1 (moveA (r s))) (one_mul _)
      exact congr_fun hy i
    simp_rw [hh,G.mat_mul,G.mat_inv]
    convert! (power_rate u (S.ratio.embed i)).star.mul hR using 1
    simp only [F,hz,zero_smul,power_zero, at_identity _ h, Pi.one_apply,G.mat_one,mul_one,star_one,one_mul,G.colorMat_skew,he,map_sub,map_neg]; abel
  have Hd := (ContinuousLinearMap.snd ℝ (Dir G f) (LieSpin G c)).hasFDerivAt.comp_hasDerivAt _ hu
  have hd := power_ray hk Hd i
  have hp : Tendsto r (𝓝 0) (𝓝 0) := by
    have hr : r 0=0 := Prod.ext rfl (zero_smul ..)
    have h' := (show Continuous r by unfold r; fun_prop).tendsto 0; rwa [hr] at h'
  have he := hp.eventually (write_right (moveθ_smooth S t h) (moveθ_id S t h))
  exact hd.unique (ha.congr_of_eventuallyEq (he.mono fun s hs => congr_arg G.mat (congr_fun hs i)))
end Centered
end YM.AnalyticNext.QuarticMatch.Pre
