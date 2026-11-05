import YM.AnalyticNext.QUARTIC_MATCH.Joint
import YM.Bid.Craft

/-!
# Patch frame centroid coordinates

Use an alternative centering (nearest to the w centroid),
vertical in the auxiliary joint variables, without changing the kernel,
tags or chosen critical value. Convenient Taylor relation: w-sum is
normal to constant gauge (starProjection). REAL. No estimate/selecting
smoothly far from origin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Pre
open Filter Function Lattice RG Wilson Precision Push Bid Exterior Bloch Matrix Tree Branch Work.F03
open Joint
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

attribute [local instance] Gauge.frobInner

namespace Knot
variable {G : Gauge} {n c f : Side} (S : StepData c f)

def circ (t : S.SitesChoice) (a : Dir G f) (x : Site c) := ∑ i, S.patch.weight i • hats S x t a i

def centroid (t : S.SitesChoice) (a : Dir G f) : Spin G c := fun i => G.focus (circ S t a i)

def point (t : S.SitesChoice) (a : Dir G f) (x : Site c) := fun i => (centroid S t a x)⁻¹ * S.frames (represent a) t x i

def matter (t : S.SitesChoice) (a : Dir G f) (x : Site c) (i : S.patch.Points) := G.mat (point S t a x i)

def send (t : S.Choices) (a : Dir G f) := Lattice.gauge (centroid S t.1 a)⁻¹ (S.prediction (represent a) t)

variable (h : S.patch.Branches S.kernel G)
include h
section
variable (t : S.SitesChoice) (x : Site c)
lemma starting : circ S t (0:Dir G f) x=1 := by simp_rw [circ,hats_zero S x t (h:=h),← Finset.sum_smul,S.patch.weight_sum,one_smul]
lemma at_identity : centroid S t (0:Dir G f) = 1 := by
  funext i; rw [centroid,starting S h]
  exact (mem_of_mem_nhds G.nearest_is_focus 1 (fun i => by simp)).symm
lemma point_id (i : S.patch.Points) : matter S t (0:Dir G f) x i=1 := by
  unfold matter point; rw [at_identity S h,Pi.one_apply,inv_one,one_mul]; exact hats_zero S x t (h:=h) _
lemma center_smooth : Smooth (0:Dir G f) fun a => centroid S t a x := by
  have he : ContDiffAt ℝ ω (fun v => G.mat (G.focus v)) (circ S t (0:Dir G f) x) := by rw [starting _ h]; exact G.focus_diff
  have hh : ContDiffAt ℝ ω (fun a : Dir G f => circ S t a x) 0 :=
    ContDiffAt.sum fun i _ => (scheme S x t (h:=h) i).const_smul (S.patch.weight i)
  exact he.comp (f:=fun a : Dir G f => circ S t a x) _ hh
lemma germ (i : S.patch.Points) : ContDiffAt ℝ ω (fun a : Dir G f => matter S t a x i) 0 :=
    (center_smooth S h t x).inv.mul
      (Q := _) (V:=fun a => S.frames (represent a) t x i) (scheme S x t (h:=h) i)

omit h in
lemma matter_avg (a : Dir G f) : (∑ i, S.patch.weight i • matter S t a x i) = G.mat (centroid S t a x)⁻¹ * circ S t a x := by
  simp only [circ,point,matter,G.mat_mul,Finset.mul_sum,mul_smul_comm]; rfl

/-- Weighted normal at the identity. -/
lemma mass : ∀ᶠ a : Dir G f in 𝓝 0,G.lie.starProjection (∑ i, S.patch.weight i • matter S t a x i) = G.lie.starProjection 1 := by
  have hs : ContDiffAt ℝ ω (fun a : Dir G f => circ S t a x) 0 :=
    ContDiffAt.sum fun i _ => (scheme S x t (h:=h) i).const_smul _
  have ht := hs.continuousAt.tendsto; rw [starting S h] at ht
  filter_upwards [ht.eventually G.nearest_is_focus] with a ha
  have he : G.Nearest (centroid S t a x) (circ S t a x) := by
    obtain ⟨u, hu⟩ := G.nearest_exists (circ S t a x); unfold centroid; exact (ha u hu) ▸ hu
  have hh := (G.lie.starProjection_apply_eq_zero_iff).mpr (G.nearest_normal he)
  rw [map_sub, sub_eq_zero] at hh
  rw [matter_avg,G.mat_inv]; exact hh

lemma rays (i : S.patch.Points) : ∀ᶠ a : Dir G f in 𝓝 0,
    matter S t a x i = G.mat (G.focus (cloud S x (a,matter S t a x) i)) := by
  have hQ : ContDiffAt ℝ ω (fun a => cloud S x (a,matter S t a x) i) (0:Dir G f) :=
    (cloud_form S x i _).comp (f:=fun a : Dir G f => (a,matter S t a x)) _ (contDiffAt_id.prodMk (contDiffAt_pi.mpr (germ S h t x)))
  have ht := hQ.continuousAt.tendsto
  simp only [cloud,point_id S h, product_zero,Pressure.one,G.mat_one,star_one,mul_one,avg_const] at ht
  filter_upwards [threshold S x (G:=G),ht.eventually G.nearest_is_focus] with a ha hc
  let U := product S x a
  let H (i : S.patch.Points) := S.patch.frame S.kernel U (t x) i
  have hg := Pressure.Road.strips S.patch _ U ha (t x) (fun _ => 1)
  rw [show (Lattice.gauge (fun _ => (1:G.El)) U)=U from funext fun i => by simp [Lattice.gauge]] at hg
  have hb : (Pressure.Road.pairs S.patch U).Solves H := by simpa only [inv_one,mul_one,H, U] using hg
  have hh : point S t a x = fun i => (centroid S t a x)⁻¹ * H i := rfl
  have he : (Pressure.Road.pairs S.patch U).Solves (point S t a x) := by
    intro u; rw [hh,Pairs.moves]; exact hb u
  apply congr_arg G.mat (hc _ ?_)
  convert! (Pressure.Road.pairs S.patch U).self_consistent he i using 1

def offset (a : Dir G f) (x : Site c) : G.Color := WithLp.toLp 2 fun i => -((fixRoot S) *ᵥ parts G 1 a i) (x,vac)
lemma shift_rate (a : Dir G f) : HasDerivAt (fun s : ℝ => G.mat (centroid S t (s • a) x)) (G.colorMat (offset S a x)) 0 := by
  have hm : offset S a x = ∑ i, S.patch.weight i • (tap S x i a-tap S x S.patch.center a) := by
    ext j
    let pr : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj j) (WithLp.linearEquiv 2 ℝ _).toLinearMap
    change _ = pr _; rw [map_sum]; simp_rw [map_smul,map_sub]
    change -((fixRoot S) *ᵥ _) _ = ∑ i, S.patch.weight i • ((tap S x i a) j - _)
    simp only [tap_line]; change -((fixRoot S) *ᵥ _) _ = ∑ i, S.patch.weight i • (_ - (tap S x S.patch.center a) j)
    simp only [tap_line,smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,S.patch.weight_sum,one_smul]
    simp only [fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,Precision.adjusted,LinearMap.sub_apply,
      LinearMap.sum_apply,LinearMap.smul_apply]; abel
  have hh : HasDerivAt (fun s : ℝ => circ S t (s • a) x) (G.colorMat (offset S a x)) 0 := by
    unfold circ; rw [hm,map_sum]; simp_rw [map_smul]
    apply HasDerivAt.fun_sum; intro i _
    exact (Push.derivative S h x t i a).const_smul (S.patch.weight i)
  have he := focused _ hh (by rw [zero_smul,starting S h])
  rw [Submodule.starProjection_eq_self_iff.mpr (G.colorMat_mem _)] at he; exact he
end

section bond
variable (e : Edge (Site c))
def ballot (t : S.SitesChoice) (a : Dir G f) (i : S.patch.Points) := matter S t a e.1 i *
    G.mat (travel (represent a) (atPoint S e.1 i) (S.repath e.2)) * star (matter S t a (e.1+step e.2) i)
def pool (t : S.SitesChoice) (a : Dir G f) := ∑ i, S.patch.weight i • ballot S e t a i
lemma ballot_start (t : S.SitesChoice) (i : S.patch.Points) : ballot S e t (0:Dir G f) i=1 := by
  simp only [ballot,point_id S h,stroll_zero,G.mat_one,star_one,mul_one]
lemma pool_start (t : S.SitesChoice) : pool S e t (0:Dir G f) = 1 := by simp_rw [pool,ballot_start _ h,← Finset.sum_smul,S.patch.weight_sum,one_smul]
lemma ballot_rate (t : S.SitesChoice) (i : S.patch.Points) : ContDiffAt ℝ ω (fun a : Dir G f => ballot S e t a i) 0 :=
  ((germ S h t e.1 i).mul (writes ..)).mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (germ S h t (e.1+step e.2) i))
lemma deliver (t : S.Choices) : ∀ᶠ a : Dir G f in 𝓝 0,send S t a e=G.focus (pool S e t.1 a) := by
  have hh : ContDiffAt ℝ ω (pool S e t.1 (G:=G)) 0 := ContDiffAt.sum fun i _ => (ballot_rate S h e t.1 i).const_smul _
  have ht := hh.continuousAt.tendsto; rw [pool_start S h] at ht
  have hu : ContDiffAt ℝ ω (bonds S e t.1 (G:=G)) 0 := ContDiffAt.sum fun i _ => (builds S h e t.1 i).const_smul _
  have hy := hu.continuousAt.tendsto; rw [bonds_zero S h] at hy
  filter_upwards [ht.eventually G.nearest_is_focus, hy.eventually G.nearest_is_focus, lips S h e t] with a ha hw hm
  have hs : G.Nearest (S.prediction (represent a) t e) (bonds S e t.1 a) := by
    obtain ⟨u, hu⟩ := G.nearest_exists (bonds S e t.1 a); rw [hm]; exact (hw u hu) ▸ hu
  let θ := centroid S t.1 a
  have he : pool S e t.1 a = G.mat ((θ e.1)⁻¹)*bonds S e t.1 a*G.mat (θ (e.1+step e.2)) := by
    unfold pool ballot matter point bonds deck StepData.connector
    simp only [θ,travel_at, G.mat_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      star_mul, G.mat_inv,star_star, mul_assoc]; rfl
  apply ha _
  rw [send,Lattice.gauge,Pi.inv_apply, Pi.inv_apply, inv_inv, he]; exact (G.nearest_right ..).mpr ((G.nearest_left ..).mpr hs)
end bond
lemma send_zero (t : S.Choices) : send S t (0:Dir G f) = 1 := by funext i; rw [send,at_identity S h, inv_one,Joint.trivial,link_one,settled _ h]; rfl
lemma send_smooth (t : S.Choices) (i : Edge (Site c)) : Smooth (0:Dir G f) fun a => send S t a i :=
    (((center_smooth S h t.1 i.1).inv).mul (V:=fun a => S.prediction (represent a) t i) (prediction_cont S h i t)).mul
      ((center_smooth S h t.1 (i.1+step i.2)).inv.inv)

def firstT (a : Dir G f) : Dir G c := fun i => WithLp.toLp 2 (fun j => (Precision.mean S *ᵥ parts G 1 a j) i)

lemma send_rate (t : S.Choices) (e : Edge (Site c)) (a : Dir G f) :
    HasDerivAt (fun s : ℝ => G.mat (send S t (s • a) e)) (G.colorMat (firstT S a (e.1,coord e.2))) 0 := by
  have he : firstT S a (e.1,coord e.2) = -offset S a e.1+bills S a (e.1,coord e.2)+offset S a (e.1+step e.2) := by
    ext j; change (Precision.mean S *ᵥ _) _ = - (offset S a e.1 j) + ((probe S) *ᵥ _) _ + offset S a _ j
    rw [probe,add_mulVec,Pi.add_apply, ← mulVec_mulVec,d_sites]; simp only [offset,WithLp.ofLp_toLp]; abel
  have hb := ((shift_rate S h t.1 e.1 a).star.mul (prices S h e t a)).mul (shift_rate S h t.1 (e.1+step e.2) a)
  rw [he]; simp_rw [send,Lattice.gauge, Pi.inv_apply, inv_inv,G.mat_mul, G.mat_inv]
  convert! hb using 1
  simp only [Pi.mul_apply,G.colorMat_skew, zero_smul,at_identity S h,Pi.one_apply,G.mat_one,mul_one,one_mul,
    link_one,settled S h,star_one,map_add,map_neg]; rfl

end Knot
end YM.AnalyticNext.QuarticMatch.Pre
