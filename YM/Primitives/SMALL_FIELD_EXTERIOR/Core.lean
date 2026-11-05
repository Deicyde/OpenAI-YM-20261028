import YM.Primitives.SMALL_FIELD_EXTERIOR.Shed
import YM.Primitives.SMALL_FIELD_EXTERIOR.Window
import YM.Push.BETA_TRANSPORT.Block


/-!
# One-step normalized response in an exact convex domain

Wilson and the actual block kernel; not assuming a running `Rep`. Real β,
real source parameter. At fixed V, condition on `shed` in the Haar tree
slice. This probability is NOT fed to a global bound without paying the
out-of-domain term. Keep the whole part inside, including Haar weight, paths
from the frame, noise, and counting/gauge conventions. Includes a response
in the Wilson sources, not differentiation in the choice of domain, forest or
payoff schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior.Forestage
open Function Set Filter Metric MeasureTheory Matrix
open Lattice Precision Wilson RG Tree Push.Uniform YM.Next.Fluctuations.Sector
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (B : Forest S.ratio) (t : S.Choices) {β r : ℝ}
    {F H : Config G f → ℝ}

def kernelWeight (β : ℝ) (V : Config G c) (u : B.Slice G) := S.density β (B.drape u) V*bare β (B.drape u)


/-- Entire tag sum is in the kernel; on the operating log domain tag replacements in the predictors
are jointly justified (`normal_identity`). -/
def funnel (β : ℝ) (V : Config G c) (F : Config G f → ℝ) (u : B.Slice G) := kernelWeight B β V u * F (B.drape u)
lemma live (a : S.patch.Branches S.kernel G) (β : ℝ) (V : Config G c) (hF : Continuous F) : Integrable (funnel B β V F) (B.order G) := by
  let k := (Push.BetaTransport.slice_estimate S a V).comp (f:=B.drape) B.continuous_drape.measurable
  let f : B.Slice G → ℝ := fun u => (bare β (B.drape u))*F (B.drape u)
  have hh : Continuous f := ((bare_cont β).mul hF).comp B.continuous_drape
  have h := k.smul_integrable β (hh.integrable_of_hasCompactSupport (μ:=B.order G) (HasCompactSupport.of_compactSpace f))
  unfold funnel kernelWeight
  simpa only [mul_assoc,f,smul_eq_mul] using! h

/-- The mass WITH operand, still unnormalized, on `shed`. -/
def localMass (x : Positions (Primary c G)) (β r : ℝ) (F : Config G f → ℝ) :=
  ∫ a in shed B x r, funnel B β (roof G x) F a ∂B.order G

def view (x : Positions (Primary c G)) (F : Config G f → ℝ) : Points (Key B G) → ℝ := F ∘ B.drape ∘ convertSlice B x
lemma view_coin (x : Positions (Primary c G)) (hF : Continuous F) : Continuous (view B x F) :=
  hF.comp (B.continuous_drape.comp (convertSlice_cont B x))
lemma realize (x : Positions (Primary c G)) (v : Points (Key B G)) :
    B.drape (convertSlice B x v)=fine G B (meetVar x v) := by
  unfold fine outer
  rw [paint_meet B]; rfl
lemma reflect_bg (x : Positions (Primary c G)) (v : Points (Key B G)) :
    roof G x=outer G B (meetVar x v) := by rw [outer,paint_meet]; rfl

section pilot
variable {μ C R m k : ℝ} {j n : ℕ} {Q : KernelChoices}
    {A : Before G μ C j Q n} {P : ChartRatio G}
    (a : Pilot A P S β r R m k) {x : Positions (Primary c G)} (hx : ‖x‖ ≤ (chart A S.patch).safety)
include a hx
lemma incoming (v : Points (Key B G)) (hv : v∈cube _ r) : kernelWeight B β (roof G x) (convertSlice B x v) =
    prefactor S G β * Real.exp (-β * bill B t G x v) := by
  rw [kernelWeight, realize,reflect_bg B x v,mul_comm];
  exact normal_identity B (p:=firstClip) rfl A a.shape.1 a.index a.kernel t β (meetVar x v)
    (closedBall_subset_ball (a.hessian_data B t).reserveH_lt (a.within B hx hv))
lemma local_price (hF : Continuous F) : localMass B x β r F=prefactor S G β * raw r (actual B t β P x) (view B x F) := by
  unfold localMass
  rw [uses B a.stamp a.positive.le a.localBox x _ (live B a.shape.1 _ _ hF).integrableOn,raw, ← integral_const_mul]
  apply setIntegral_congr_fun (cube_meas _); intro y hy
  unfold funnel actual view; simp only; rw [incoming B t a hx y hy, coin_exp B a.stamp a.positive.le a.localBox y hy]
  simp only [Pi.add_apply,neg_add,Real.exp_add,Pi.smul_apply,smul_eq_mul,Function.comp_apply, neg_mul]; ring



end pilot

def mark (F : Config G f → ℝ) (θ : ℝ) (U : Config G f) := Real.exp (θ * F U)
lemma mark_cont (hF : Continuous F) (θ : ℝ) : Continuous (mark F θ) := by unfold mark; fun_prop


def fiber (x : Positions (Primary c G)) (β r : ℝ) (F H : Config G f → ℝ) (θ : ℝ) :=
  localMass B x β r (mark F θ * H) / localMass B x β r (mark F θ)

variable {μ C R m k : ℝ} {j n : ℕ} {Q : KernelChoices}
    {A : Before G μ C j Q n} {P : ChartRatio G}
    (a : Pilot A P S β r R m k) {x : Positions (Primary c G)} (hx : ‖x‖ ≤ (chart A S.patch).safety)
include a hx
lemma tagged (hF : Continuous F) (hH : Continuous H) (θ : ℝ) : localMass B x β r (mark F θ * H) = prefactor S G β *
    raw r (actual B t β P x - θ • view B x F) (view B x H) := by
  rw [local_price B t a hx ((mark_cont hF θ).mul hH)]
  congr 1; unfold raw; apply integral_congr_ae; filter_upwards with y
  simp only [Pi.sub_apply, neg_add,neg_neg,sub_eq_add_neg,Real.exp_add,view,Function.comp_apply,Pi.mul_apply,mark,Pi.smul_apply,smul_eq_mul]
  ring
lemma tagMass (hF : Continuous F) (θ : ℝ) : localMass B x β r (mark F θ) = prefactor S G β * raw r (actual B t β P x - θ • view B x F) 1 := by
  nth_rw 1 [← mul_one (mark F θ)]
  exact tagged B t a hx hF (show Continuous (1:Config G f → ℝ) from continuous_const) θ

lemma lean_price (hF : Continuous F) (hH : Continuous H) (θ : ℝ) : fiber B x β r F H θ =
    ∫ y, view B x H y ∂plume (cover B t G β) r (Wplan B t β P x - θ • view B x F) := by
  rw [fiber,tagged B t a hx hF hH, tagMass B t a hx hF, plume_read (a.cover_pos B t),
    show load _ (_ - θ • view B x F)=actual B t β P x- θ • view B x F by unfold load Wplan; abel,
    mul_div_mul_left _ _ (prefactor_pos _).ne']; rfl
lemma marked (hF : Continuous F) (hH : Continuous H) : HasDerivAt (fiber B x β r F H)
    (correlated (plume (cover B t G β) r (Wplan B t β P x)) (view B x F) (view B x H)) 0 := by
  rw [show fiber B x β r F H = _ from funext (lean_price B t a hx hF hH)]
  simpa only [zero_smul, sub_zero] using plume_source (a.cover_pos B t) a.positive (a.field B t hx).cOn (view_coin B x hF).continuousOn
    (view_coin B x hH).continuousOn 0


include t in
/-- Response estimate with explicit supports and prices. Interpret ALL on
the SAME tree. `StepData.push` comparison will also use this tree. -/
theorem features (hF : Continuous F) (hH : Continuous H) (ρ σ : Site f) (p q : ℕ) (L N : Finset (Key B G)) (d e : ℝ)
    (h₁ : Features (location B G) ρ p L r (view B x F) d)
    (h₂ : Features (location B G) σ q N r (view B x H) e) : let b := pace A S.patch
    |deriv (fiber B x β r F H) 0| ≤ feat b L p d / margin A S.patch β * (Decay b ρ σ * feat b N q e) := by
  intro b
  rw [(marked B t a hx hF hH).deriv, covariance_cloud (a.cover_pos B t),load_Wplan]
  have he := a.margin_pos B t
  exact featured a.positive (a.potential B t hx) (a.positive_pace B t).le he ((a.gap B t hx).drop he.le)
    (fun y hy => a.extended B t hx y hy ρ) h₁ h₂
end YM.Primitives.SmallFieldExterior.Forestage
