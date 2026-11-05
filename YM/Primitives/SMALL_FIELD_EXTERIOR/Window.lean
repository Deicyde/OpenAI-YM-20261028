import YM.Next.FOUNDATIONS.SU2
import YM.Primitives.SMALL_FIELD_EXTERIOR.Cloud
import YM.Primitives.SMALL_FIELD_EXTERIOR.HaarCoin
import YM.Primitives.SMALL_FIELD_EXTERIOR.Town
import YM.Push.STATIONARY_UNIFORM.Wilson


/-!
# Charge on a uniform box for a Wilson response integral

At the Wilson input. Bring G, kernel/prices Before and local Haar prices;
after L, pay a beta floor, and all patches of this shape for larger periods
share the same bound. On the unscaled real log links in any Forest. `cover`
is the SectorChange Gaussian cloud covariance used in this alternative
one-step integral, uses ordinary counting (no modified charges there).

Keep independent of the path metrics and convexity *across* defaults. Here
we don't partition the vacuum into Stores, use actual gauge slice and actual
joint kernel using all predictions. Not identifying this covariance with affine-sector fog.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior.Forestage
open Function Set Filter Metric MeasureTheory Matrix
open Lattice Precision Wilson RG Tree Push.Uniform HaarCoin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {μ C β r R m k : ℝ} {j n : ℕ} {Q : KernelChoices}
    {A : Before G μ C j Q n} {P : ChartRatio G}
variable {c f : Side} {S : StepData c f} (B : Forest S.ratio) (t : S.Choices)

-- prices specialize to ordinary Wilson (no top Taylor matches called here)
def chart (A : Before G μ C j Q n) := A.tables firstClip

def margin (A : Before G μ C j Q n) (S : Patch) (β : ℝ) := β * (chart A S).gap / 8
structure Pilot (A : Before G μ C j Q n) (P : ChartRatio G) (S : StepData c f) (β r R m k : ℝ) : Prop where
  coeff : 0 < μ
  budget : 0 ≤ C
  index : S.patch.J=j
  kernel : S.kernel=Q
  shape : Bid.Larger (G:=G) S
  stamp : Stamp P R m k
  positive : 0 < r
  localBox : r ≤ R
  safe : r ≤ (chart A S.patch).safety
  betaPos : 0 < β
  issued : tariff G k ≤ margin A S.patch β

lemma Pilot.hessian_data (h : Pilot A P S β r R m k) :
    let Y := chart A S.patch
    Receipt (address B G) Y.width n Y.coords Y.value Y.initial Y.gap (priced B t firstClip (wil G)) :=
  (A.receipt B t (initial_bounds G h.coeff h.budget (Λ:=0) le_rfl (p:=firstClip) rfl) h.shape h.index h.kernel).1
include B t in
lemma Pilot.margin_pos (h : Pilot A P S β r R m k) : 0 < margin A S.patch β :=
  div_pos (mul_pos h.betaPos (h.hessian_data B t).pos_m) (by norm_num)

section coords
variable {ι κ : Type} [Fintype ι] [Fintype κ]
    {x : Positions ι} {v : Positions κ} {f : Positions (ι ⊕ κ) → ℝ}

lemma meet_smooth {k : ℕ∞ω} (x : Positions ι) : ContDiff ℝ k (meetVar x : Positions κ → _) :=
  ((partSpace ..).symm.contDiff).comp (f:=fun z : Positions κ => (x,z)) (contDiff_const.prodMk contDiff_id)

omit [Fintype κ] in
lemma pc_bolt [DecidableEq κ] (i : κ) (f : Points κ → ℝ) (v : Points κ) : pc i f v=fderiv ℝ f v (bolt i) := by
  unfold pc bolt; congr! -- proof irrelevance

lemma pc_meet [DecidableEq κ] [DecidableEq (ι⊕κ)] (i : κ) (hf : DifferentiableAt ℝ f (meetVar x v)) :
    pc i (f ∘ meetVar x) v=pc (.inr i) f (meetVar x v) := by
  rw [pc_bolt, (hf.hasFDerivAt.comp v (meet_derivative x v)).fderiv,ContinuousLinearMap.comp_apply,lower_bolt,pc_bolt]

lemma vertical_matrix [DecidableEq κ] (hf : ContDiffAt ℝ ω f (meetVar x v)) :
    curvature (f ∘ meetVar x) v = block f (meetVar x v) := by
  ext i j
  let p := meetVar x v
  have hg : pc i (f ∘ meetVar x) =ᶠ[𝓝 v] pc (.inr i) f ∘ meetVar x := by
    filter_upwards [(meet_derivative x v).continuousAt.tendsto.eventually (hf.eventually (by simp))] with z hz
    exact pc_meet _ (hz.differentiableAt (by simp))
  have he : curvature (f ∘ meetVar x) v i j = pc (.inr j) (pc (.inr i) f) p := by
    rw [curvature,Matrix.of_apply, pc_comm _ _ ((hf.comp v ((meet_smooth x).contDiffAt)).of_le le_top)]
    rw [pc,hg.fderiv_eq]; exact pc_meet _ ((pcat _ hf (k:=ω) (by simp)).differentiableAt (by simp))
  rw [he, pc_pc _ _ (show ContDiffAt ℝ 2 f p from hf.of_le le_top),block,Matrix.of_apply,entry,iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]; unfold bolt; congr!
end coords

def bill (G : Gauge) (x : Positions (Primary c G)) := priced B t firstClip (wil G) ∘ meetVar x

def actual (β : ℝ) (P : ChartRatio G) (x : Positions (Primary c G)) := β • bill B t G x + HaarCoin.dues P B.Free

def location (G : Gauge) := (address B G) ∘ Sum.inr

def pace (A : Before G μ C j Q n) (S : Patch) :=
  let Y := chart A S; tiltWidth Y.coords (Y.gap/2) Y.width Y.value

include B t in
lemma Pilot.positive_pace (h : Pilot A P S β r R m k) : 0 < pace A S.patch := by
  have hf := h.hessian_data B t
  exact tiltWidth_pos _ (half_pos hf.pos_m) hf.pos_a hf.pos_C.le

variable {x : Positions (Primary c G)}
lemma Pilot.within (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) {v : Points (Key B G)} (hv : v ∈ cube _ r) :
    meetVar x v∈closedBall 0 (chart A S.patch).safety := by
  rw [mem_closedBall_zero_iff,norm_meet,max_le_iff]; exact ⟨hx,(mem_closedBall_zero_iff.mp hv).trans h.safe⟩
lemma Pilot.smooth (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) {v : Points (Key B G)} (hv : v∈cube _ r) :
    ContDiffAt ℝ ω (priced B t firstClip (wil G)) (meetVar x v) := by
  have hf := h.hessian_data B t
  exact (hf.born _ (closedBall_subset_ball hf.reserveH_lt (h.within B hx hv))).1
lemma Pilot.classic (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) : SmallFieldExterior.Regular r ω (bill B t G x) :=
  fun _ hv => (h.smooth B t hx hv).comp _ (meet_smooth x |>.contDiffAt)
lemma Pilot.potential (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) : SmallFieldExterior.Regular r 2 (actual B t β P x) :=
  (((h.classic B t hx).mono le_top).smul β).add (dues_smooth h.stamp h.positive.le h.localBox _)

private lemma summed {ι : Type} [Fintype ι] [DecidableEq ι] {u : Points ι} {f g : Points ι → ℝ} (hf : ContDiffAt ℝ 2 f u)
    (hg : ContDiffAt ℝ 2 g u) : curvature (f+g) u=curvature f u+curvature g u := by
  ext i j; unfold curvature; simp only [Matrix.add_apply,Matrix.of_apply]
  have he : pc j (f+g)=ᶠ[𝓝 u] pc j f+pc j g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hx
    exact pc_plus j (hy.differentiableAt two_ne_zero) (hx.differentiableAt two_ne_zero)
  rw [pc,he.fderiv_eq]; exact pc_plus i ((pcat _ hf (k:=1) (by norm_num)).differentiableAt one_ne_zero)
    ((pcat _ hg (k:=1) (by norm_num)).differentiableAt one_ne_zero)

lemma Pilot.widen (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) (v : Points (Key B G)) (hv : v∈cube _ r)
    (w : B.Free → ℝ) (hw : ∀ i,w i ≠ 0)
    (hh : Charge (conjugated (fun i => w i.1) (block (priced B t firstClip (wil G)) (meetVar x v))) ((chart A S.patch).gap/4)) :
    Charge (conjugated (fun i => w i.1) (curvature (actual B t β P x) v)) (margin A S.patch β) := by
  have hg : Charge (curvature (dues P B.Free) v) (-tariff G k) := by
    convert! h.stamp.receipt (ι:=B.Free) h.positive.le h.localBox _ hv using 1
    congr!
  let F := bill B t G x
  have hi : ContDiffAt ℝ 2 F v := (h.classic B t hx _ hv).of_le le_top
  rw [actual,summed (show ContDiffAt ℝ 2 (β • bill B t G x) v from contDiffAt_const.smul hi) (dues_smooth h.stamp h.positive.le h.localBox _ _ hv), curvature_smul hi]
  have hdiv (M L : Matrix (Key B G) (Key B G) ℝ) :
      conjugated (fun i => w i.1) (β • M + L)=β • conjugated (fun i => w i.1) M + conjugated (fun i => w i.1) L := by
    ext; simp only [conjugated,Matrix.of_apply,Matrix.smul_apply, Matrix.add_apply,smul_eq_mul]; ring
  have hst : conjugated (fun i => w i.1) (curvature (dues P B.Free) v)=curvature (dues P B.Free) v := by
    convert! h.stamp.still h.positive.le h.localBox hw v hv using 2; congr!
  rw [hdiv,hst]
  have hp : curvature F v = _ := vertical_matrix (h.smooth B t hx hv)
  rw [hp]; intro u; rw [Matrix.add_mulVec,Matrix.smul_mulVec, dotProduct_add,dotProduct_smul,smul_eq_mul]
  have hc := mul_le_mul_of_nonneg_left (hh u) h.betaPos.le
  apply le_trans _ (add_le_add hc (hg u));
  have he : margin A S.patch β ≤ β*((chart A S.patch).gap/4)-tariff G k := by
    have hs := h.issued; unfold margin at hs ⊢; linarith
  apply (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ ∑ i,u i^2)).trans_eq; ring

lemma Pilot.gap (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) :
    Charged r (actual B t β P x) (margin A S.patch β) := by
  intro v hv
  have hf := h.hessian_data B t
  have he := hf.snaps _ (h.within B hx hv)
  rw [← conjugated_one (curvature (actual B t β P x) v)]; apply h.widen B t hx _ hv (fun _ => 1) (fun _ => one_ne_zero)
  rw [show (fun _ : Key B G => (1:ℝ))=1 from rfl,conjugated_one]
  intro u
  have hk : 0 < (chart A S.patch).gap := hf.pos_m
  exact (mul_le_mul_of_nonneg_right (show (chart A S.patch).gap/4≤(chart A S.patch).gap/2 by linarith) (by positivity : 0 ≤ ∑ i,u i^2)).trans (he u)

lemma Pilot.extended (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) :
    ∀ v∈cube _ r, ∀ i : Site f, Charge (conjugated (slow (location B G) (pace A S.patch) i) (curvature (actual B t β P x) v))
      (margin A S.patch β) := by
  intro v hv i
  let Y := chart A S.patch
  let l := location B G
  let H := block (priced B t firstClip (wil G)) (meetVar x v)
  have hf := h.hessian_data B t
  have hw := h.within B hx hv
  have he : Sealed l Y.width H Y.value := block_rows (hf.born (meetVar x v) (closedBall_subset_ball hf.reserveH_lt hw)).2
      (show 2 ≤ n from le_trans (by norm_num) A.n_ok)
  let W (j : B.Free) := Real.exp (pace A S.patch*separation i j.val.1)
  apply h.widen B t hx v hv W (fun _ => (Real.exp_pos _).ne')
  change Charge (conjugated (slow l _ i) H) _
  rw [costed]
  convert! tiltedCharge he (half_pos hf.pos_m) hf.pos_a (hf.snaps _ hw) hf.pos_C.le (K:=Y.coords)
    (Multiplicity.comp (town B) Sum.inr_injective) i using 1; ring

/-- Use stiffness of the actual Wilson-tree score at zero. `β` SAME
parameter as in bare Wilson and noise. `Positions` unscaled. -/
def cover (B : Forest S.ratio) (t : S.Choices) (G : Gauge) (β : ℝ) := (β • block (priced B t firstClip (wil G)) 0)⁻¹
lemma Pilot.cover_pos (h : Pilot A P S β r R m k) : (cover B t G β).PosDef := by
  have he := h.hessian_data B t
  exact ((he.gap.positive (block_hermitian (he.born _ (mem_ball_self he.pos_r)).1) he.pos_m).smul h.betaPos).inv

/-- The actual perturbation, axis bgs and cube chosen independently
from any hard-sector addresses. -/
def Wplan (β : ℝ) (P : ChartRatio G) (x : Positions (Primary c G)) := actual B t β P x - stiffness (cover B t G β)
lemma load_Wplan (β : ℝ) (P : ChartRatio G) (x : Positions (Primary c G)) : load (cover B t G β) (Wplan B t β P x)=actual B t β P x :=
  add_sub_cancel ..
lemma Pilot.field (h : Pilot A P S β r R m k) (hx : ‖x‖ ≤ (chart A S.patch).safety) : SmallFieldExterior.Regular r 2 (Wplan B t β P x) :=
  (h.potential B t hx).sub (fun _ _ => (stiffness_diff _).contDiffAt.of_le le_top)
end YM.Primitives.SmallFieldExterior.Forestage
