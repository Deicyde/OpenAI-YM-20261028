import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Planned.ATOM_FORCED_ESTIMATE.Vacuum


/-!
# Pricing a forced primary occurrence with held integration variables

A kernel *before multiplying in* the bounded Borel forced input and its indicated other
incoming gas factors.

Sufficient socket for working through output derivatives WITHOUT
assuming smoothness of those functions/flags in a field direction.

The change of
variables for all held arguments has to represent the very same first integrated gas
term; it can change coordinates between term labels, not the law for a shared read
within the term.

In particular any chart/kernel Jacobians left by holding are costs of
the kernel here.

Linear integral readers are continuous already on `L¹`.

Their norm
bound uses an inequality on the actual common integrand, not independence.

Derivatives
needed only on the empty-inventory output before its mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced
open Lattice Wilson RG MeasureTheory Function Filter Source Push.Local Extra.Histories
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius ENNReal

namespace Reader
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {g : α → ℂ}

private lemma allowed (hg : AEStronglyMeasurable g μ) {c : ℝ} (h : ∀ x, ‖g x‖ ≤ c) (w : α →₁[μ] ℂ) :
    Integrable (fun x => g x * w x) μ := (L1.integrable_coeFn w).bdd_mul hg (Eventually.of_forall h)

private def map (hg : AEStronglyMeasurable g μ) {c : ℝ} (h : ∀ x, ‖g x‖ ≤ c) : (α →₁[μ] ℂ) →ₗ[ℝ] ℂ where
  toFun w := ∫ x, g x * w x ∂μ
  map_add' w v := by
    rw [← integral_add (allowed μ hg h w) (allowed μ hg h v)]; apply integral_congr_ae
    filter_upwards [Lp.coeFn_add w v] with x hx; rw [hx, Pi.add_apply, mul_add]
  map_smul' r w := by
    rw [RingHom.id_apply,← integral_smul]; apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul r w] with x hx; rw [hx,Pi.smul_apply,mul_smul_comm]

theorem pay (hg : AEStronglyMeasurable g μ) {c : ℝ} (h : ∀ x, ‖g x‖ ≤ c) (w : α →₁[μ] ℂ) :
    ‖∫ x, g x * w x ∂μ‖ ≤ c * ‖w‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [L1.norm_eq_integral_norm, ← integral_const_mul]
  exact integral_mono (allowed μ hg h w).norm ((L1.integrable_coeFn w).norm.const_mul _) (fun x =>
    (norm_mul ..).trans_le (mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)))


end Reader

variable {G : Gauge} {c n : Side}

structure Held (G : Gauge) (c n : Side) where
  Space : Type*
  [meas : MeasurableSpace Space]
  μ : Measure Space
  input : Space → Config G n
  measured : Measurable input
  support : Support c
  inventory : Support c
  subset : inventory ⊆ support
  other : Finset ℕ
  kernel : Config G c → Space →₁[μ] ℂ

attribute [instance] Held.meas
namespace Held
variable (M : Held G c n) (A : Activities G n) (g : Config G n → ℂ)

def multiplier (x : M.Space) := g (M.input x) * ∏ i∈M.other,(A.K i (M.input x) : ℂ)





variable {A g} {P B : BudgetPoint}



/-- Sufficient locality, measurability & pre-mask differentiability tests on the **kernel**
on its fixed held integration space. Need covariance of the read separately (gauge changes
can act on held variables). No smoothness requirement in V for any nonempty inventory.
-/
structure Regular (B : BudgetPoint) (o : Site c) : Prop where
  owner : o ∈ M.support
  local_reads : UsesFinal B.threshold M.support M.kernel
  unforced : M.inventory = ∅ → LocalOn M.support M.kernel
  borel_kernel : @Measurable _ _ _ (borel _) M.kernel
  chart (V : Config G c) : M.inventory = ∅ → Healthy B.threshold M.support V → Chart B.order M.kernel V

structure Estimate (B : BudgetPoint) (o : Site c) (u : ℝ) : Prop where
  nonnegative : 0 ≤ u
  value (V : Config G c) : M.support ∩ flags B.threshold V = M.inventory → ‖M.kernel V‖ ≤ u
  jets (V : Config G c) : M.inventory = ∅ → Healthy B.threshold M.support V → ∀ l : List _, l.length ≤ B.order →
    (∀ A∈l,B.dirBound o A) → ‖leftDerivs M.kernel l V‖ ≤ u

lemma amount {u : ℝ} {b : ℕ → ℝ} (h : ∀ U, ‖g U‖ ≤ u) (hb : ∀ i ∈ M.other, ∀ U, ‖A.K i U‖ ≤ b i) (x : M.Space) :
    ‖M.multiplier A g x‖ ≤ u * ∏ i∈M.other,b i := by
  unfold multiplier; rw [norm_mul,norm_prod]
  exact mul_le_mul (h _) (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => (Complex.norm_real _).trans_le (hb i hi _)))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans (h 1))




end Held
end YM.Planned.Forced
