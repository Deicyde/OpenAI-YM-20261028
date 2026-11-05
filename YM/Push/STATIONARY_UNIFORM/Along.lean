import YM.Next.FOUNDATIONS.SU2
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STATIONARY_UNIFORM.Response


/-!
# Uniform control along actual continued path

These price *real* polarized kernels in all physical coordinates on the finite
tori, K+trials may choose further metrics through cross formulas to identify
e.g. as arising from periodizations of same new path coefficients. NOT
claiming that. Distinguish translation of a stencil test into the middle of
one of these balls (all distances still in native inputs), versus c_J
estimates no polynomial L loss on specially routed continuation inputs. This
doesn't imply the latter, so does not license perpetual commissioning. But
e.g. can pay o-delay costs on these paths after the L commitments, without
changing to trees at other periods/covers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid
open Work.F03 Work.F04 Matrix
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio}
variable {t : S.Choices} {μ C Λ : ℝ} {n : ℕ} {R : PathData G} {p : Clip}
variable {j : ℕ} {Q : KernelChoices} {A : Before G μ C j Q n}
variable {x y : Positions (Primary c G)} {g : In G c → AxisChart G B}

-- view common g in reindexed real coordinates

def station (g : In G c → AxisChart G B) := (tint G _).symm ∘ g ∘ tint G _

namespace Before.Service
variable (h : A.Service B p R g)
include h
lemma x_pos : 0 < (A.tables p S.patch).horizon := h.1
lemma zone_pos : 0 < (A.tables p S.patch).zone := h.2.2.1
lemma critical : Critical B p R g := h.2.2.2.2.2.1
lemma series (hx : x∈ball 0 (A.tables p S.patch).horizon) : ContDiffAt ℝ ω (station g) x := by
  have hv : ContDiffAt ℝ ω g (tint G _ x) := (h.2.2.2.2.2.2 _ (by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hx)).1
  exact (tint G B.Free).symm.contDiff.contDiffAt.comp x (f:=g ∘ tint G _) (hv.comp x (tint G (Body 1 c)).contDiff.contDiffAt)
lemma landed (hx : x∈ball 0 (A.tables p S.patch).horizon) :
    station g x∈closedBall 0 (A.tables p S.patch).zone := by
  let P := A.tables p S.patch
  have hz : ‖station g x‖ ≤ P.zone/2 := (h.2.2.2.2.2.2 _
    (by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hx)).2.1
  rw [mem_closedBall,dist_zero_right]; exact hz.trans (half_lt_self h.zone_pos).le
lemma pricing (hx : x∈ball 0 (A.tables p S.patch).horizon) :
    curve (station g) x∈closedBall 0 (A.tables p S.patch).safety := by
  have he := h.landed hx
  let P := A.tables p S.patch
  exact closedBall_subset_closedBall (show P.zone ≤ _ from min_le_left ..) (Receipt.holds
    (m:=P.gap) (r:=P.initial) (C:=P.value) (K:=P.coords) (a:=P.width) hx he)
lemma choice (t : S.Choices) (hx : x∈ball 0 (A.tables p S.patch).horizon) :
    HasFDerivAt (𝕜:=ℝ) (tested B t p R (tint G _ x)) 0 (g (tint G _ x)) := by
  have hx' : (tint G _).symm (tint G _ x)∈ball 0 (A.tables p S.patch).horizon := by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hx
  exact ((h.2.2.2.2.2.2 _ hx').2.2 t _ (h.landed hx)).2 rfl
lemma entered (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) (hx : x∈ball 0 (A.tables p S.patch).horizon) (t) :
    Slope (priced B t p R) ∘ curve (station g) =ᶠ[𝓝 x] 0 := by
  filter_upwards [isOpen_ball.mem_nhds hx] with i hi
  have hr := (A.receipt B t hp hK hj ht).1
  have hh := (hr.born _ (closedBall_subset_ball hr.reserveH_lt (h.pricing hi))).1
  have he : ContDiffAt ℝ ω (priced B t p R) (meetVar i (station g i)) := hh
  exact (slope_zero_test he).mpr ((view_exact _ _).2 (by
    unfold station; rw [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]; exact h.choice t hi))

lemma coefficient (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) {k : ℕ} (hk : k<n)
    (hx : x∈ball 0 (A.tables p S.patch).horizon) :
    let P := A.tables p S.patch
    Envelope (address B G ∘ Sum.inl) (address B G ∘ Sum.inr) (responseRate P.coords n P.value P.width P.gap)
      k (station g) x (curveCost P.coords P.value P.width P.gap k) := by
  let t : S.Choices := Classical.arbitrary _
  have hv := h.series hx
  have he := envelopes (A.receipt B t hp hK hj ht).1 hv (h.pricing hx) (h.entered hp hK hj ht hx t) hk
  intro P i hi hl q j
  cases i with
  | zero => exact False.elim (hi rfl)
  | succ i => rw [← higher_positions hv]; exact he _ (by omega) hl q (Sum.inr j)

lemma station_cost (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q)
    (hx : x∈ball 0 (A.tables p S.patch).horizon) (t : S.Choices) :
    let P := A.tables p S.patch; let v (x : Positions (Primary c G)) := tested B t p R (tint G _ x) (g (tint G _ x))
    ContDiffAt ℝ ω v x ∧ Scatter (address B G ∘ Sum.inl)
      (weaker n (responseRate P.coords n P.value P.width P.gap)) n v x
      (onShellCost P.width P.value P.coords n P.gap) := by
  have hr := (A.receipt B t hp hK hj ht).1
  let F := priced B t p R
  let P := A.tables p S.patch; let v (x : Positions (Primary c G)) := tested B t p R (tint G _ x) (g (tint G _ x))
  have he : v = F ∘ curve (station g) := by
    funext u
    change _ = priced B t p R (meetVar u (station g u))
    rw [written]; unfold station; rw [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]; rfl
  change ContDiffAt ℝ ω v x ∧ Scatter _ _ _ v _ _; rw [he]
  have hH := h.pricing hx
  have ha := h.series hx
  exact ⟨(hr.born _ (closedBall_subset_ball hr.reserveH_lt hH)).1.comp _ (along ha),star_cost hr ha hH (h.entered hp hK hj ht hx t)⟩

/-- Real sup estimate along the *same* branch. -/
def trailCost (P : ChartPrices) (n : ℕ) :=
  let d := responseRate P.coords n P.value P.width P.gap
  1+curveCost P.coords P.value P.width P.gap 1*(P.coords*countCost d)

lemma trail_lipschitz (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) :
    let P := A.tables p S.patch; let s := ball (0 : Positions (Primary c G)) P.horizon; let C := trailCost P n
    0<C ∧ ∀ x∈s, ∀ y∈s, ‖station g x - station g y‖ ≤ C*‖x-y‖ := by
  let t : S.Choices := Classical.arbitrary _
  have hr := (A.receipt B t hp hK hj ht).1
  let P := A.tables p S.patch; let M := curveCost P.coords P.value P.width P.gap 1; let d := responseRate P.coords n P.value P.width P.gap
  let L := trailCost P n; have hM : 1 ≤ M := curveCost_ge hr _; have hd : 0<d := rate_pos hr
  have hL : 0<L := by
    have hx := count_pos hd
    change 0 < 1+M*(P.coords*countCost d); positivity
  let s := ball (0 : Positions (Primary c G)) P.horizon
  have hh x (hx : x∈s) : ‖fderiv ℝ (station g) x‖ ≤ L := by
    refine ContinuousLinearMap.opNorm_le_bound _ hL.le fun v => ?_
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL.le (norm_nonneg _))).mpr; intro i
    let l := address B G; let y := l (Sum.inr i)
    have hb (j : Primary c G) : ‖fderiv ℝ (station g) x (bolt j) i‖ ≤ M*Decay d y (l (Sum.inl j)) := by
      have h := h.coefficient hp hK hj ht (show 1<n by have := hr.order; omega) hx 1 (by decide) le_rfl ![j] i
      simpa [M,d,y,l,P,entry,glaze,spanSites,Decay,Fin.sum_univ_succ] using h
    rw [by_row,Finset.sum_apply]
    have ht : 0 ≤ M*‖v‖ := mul_nonneg (zero_le_one.trans hM) (norm_nonneg _)
    calc
      _ ≤ ∑ j, ‖v j‖ * ‖fderiv ℝ (station g) x (bolt j) i‖ := by simpa [norm_mul] using!
        (norm_sum_le (f:=fun j : Primary c G => v j * fderiv ℝ (station g) x (bolt j) i) (s:=Finset.univ))
      _ ≤ ∑ j, M*‖v‖*Decay d y (l (Sum.inl j)) := Finset.sum_le_sum fun j _ =>
        (mul_le_mul (norm_le_pi_norm _ j) (hb j) (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)
      _ = M*‖v‖*∑ j, Decay d y (l (Sum.inl j)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        have hq : _ ≤ (P.coords:ℝ)*countCost d := (hr.mult.comp (Sum.inl_injective)).count
          (l ∘ (@Sum.inl (Primary c G) (Key B G))) hd y
        apply (mul_le_mul_of_nonneg_left hq ht).trans; change _ ≤ (1+M*(P.coords*countCost d))*‖v‖
        rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)
  exact ⟨hL,fun x hx y hy => (convex_ball ..).norm_image_sub_le_of_norm_fderiv_le (fun x hx => (h.series hx).differentiableAt (by simp)) hh hy hx⟩
end Before.Service
end YM.Push.Uniform
