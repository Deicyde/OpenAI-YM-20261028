import YM.Further.CORRECTED_LIFT_COEFFICIENTS.ChartCost
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Unpack

/-!
# Plaquette coordinates used for the calibration

State exact geometric and finite chart gates. `Board.replay` is on the
*independent* old-t-scaled plaquette slots, returns old-t-scaled links in
log directions. Can include repeated slots. No approximation assumed for
moments or beta or fitted test outputs. Keep costs evaluable even with local
(nonuniform radius) charts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Next.Extract Extraction Source Source.Drops
open Push.Corrected Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {X : Support n} {P : BudgetPoint} {o : Site n} {f : Config G n → ℂ}
  {C : Family G} {d m p t : ℕ}

abbrev Panel := GaugePanel
-- cover conventions
structure Board (G : Gauge) (n : Side) (P : BudgetPoint) (t : ℕ) where
  size : ℕ
  leg : Fin size → RG.Slot
  cube : Support n
  replay : Panel G size → Directions G n
  empty : replay 0 = 0
  nice : ContDiffAt ℝ t replay 0
  fits (x : Fin size) (y : Cover) (h : y ∈ (leg x).stencil) (i : Axis) :
      20*((y i).natAbs+1) ≤ n.val
  -- true group, one common gauge for the whole cube
  authentic : ∀ᶠ U : Config G n in 𝓝 1, ∃ u : Site n → G.El,
    Agrees cube (gauge u U) (increment 1 (P.threshold • replay (P.threshold⁻¹ • fun i => (leg i).atSite U 0)))

namespace Board
variable (B : Board G n P t)

abbrev Eye := Panel G B.size
abbrev Bit := Fin B.size × G.ColorIndex
abbrev Word (l : ℕ) := Fin l → Bit B
abbrev All := (l : Fin (t+1)) × B.Word l.val

def blade (b : Bit B) : B.Eye := Pi.single b.1 (EuclideanSpace.basisFun G.ColorIndex ℝ b.2)
lemma blade_norm (b : Bit B) : ‖B.blade b‖ ≤ 1 := by
  simp [blade, Pi.norm_single]

def showAt (Y : B.Eye) : Config G n := increment 1 (P.threshold • B.replay Y)

def input (U : Config G n) : B.Eye := P.threshold⁻¹ • fun i => (B.leg i).atSite U 0

def print (f : Config G n → ℂ) (l : ℕ) (w : B.Word l) : ℂ :=
  Tensor.coeff (f ∘ B.showAt) l 0 fun i => B.blade (w i)

lemma smooth {l : ℕ} (h : P.Regular X f) (ht : t ≤ P.order) (hl : l ≤ t) :
    ContDiffAt ℝ l (f ∘ B.showAt) 0 := by
  change ContDiffAt ℝ l (Costs.scaledFun P f ∘ B.replay) 0
  apply ContDiffAt.comp _ _ (B.nice.of_le (Nat.cast_le.mpr hl))
  rw [B.empty]; exact Costs.scaled_nice h l (hl.trans ht)

/-- Cost computed from the chosen path/chart. Later need NUMERICAL estimate.
Can take after L, not here asserting pre-side admission. -/
def rate : ℝ := 1+ ∑ l ∈ Finset.range (t+1), ‖iteratedFDeriv ℝ l B.replay 0‖
lemma rate_one_le : 1 ≤ B.rate := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

def derivativeFee (l : ℕ) : ℝ := (∑ i∈Finset.range (l+1),Costs.ticket G i)*B.rate^l
lemma derivativeFee_nonnegative (l : ℕ) : 0 ≤ B.derivativeFee l :=
    mul_nonneg (Finset.sum_nonneg fun i _ => Costs.ticket_ok G i) (pow_nonneg (zero_le_one.trans B.rate_one_le) _)

lemma affordable (h : P.Regular X f) (ht : t ≤ P.order) {a : ℝ} (e : P.supBounds o X f a)
    (l : ℕ) (hl : l ≤ t) (w : B.Word l) : ‖B.print f l w‖ ≤ B.derivativeFee l * a := by
  let R := ∑ i∈Finset.range (l+1),Costs.ticket G i
  have he i (hi : i ≤ l) : ‖iteratedFDeriv ℝ i (Costs.scaledFun P f) 0‖ ≤ R*a := by
    exact (Costs.operator_cost i h e (hi.trans (hl.trans ht))).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => Costs.ticket_ok G j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) e.1)
  have hu i (hp : 1 ≤ i) (hi : i ≤ l) : ‖iteratedFDeriv ℝ i B.replay 0‖ ≤ B.rate^i := by
    have he := Finset.single_le_sum (s:=Finset.range (t+1)) (f:=fun j => ‖iteratedFDeriv ℝ j B.replay 0‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (hi.trans hl)))
    exact (he.trans (le_add_of_nonneg_left zero_le_one)).trans
      ((pow_one B.rate).symm.le.trans (pow_le_pow_right₀ B.rate_one_le hp))
  let T := Tensor.coeff (f ∘ B.showAt) l 0
  have H : ‖T‖ ≤ R*a*B.rate^l := by
    change ‖Tensor.coeff (Costs.scaledFun P f ∘ B.replay) l 0‖ ≤ _
    exact Costs.composition_at_zero _
      (Costs.scaled_nice h l (hl.trans ht)) (B.nice.of_le (Nat.cast_le.mpr hl)) B.empty he hu
  apply (T.le_opNorm _).trans
  apply (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => B.blade_norm (w i)))).trans
  exact H.trans_eq (by unfold derivativeFee R; ring)

private lemma hol_near (H : Hol G) (J : Labels.Jet G) :
    Tendsto (H.testLinks d (0:Site n) J) (𝓝 0) (𝓝 1) := by
  let r := testLog H d (0:Site n) J
  let F (x : ℝ) := increment (1:Config G n) (r x)
  have hr : ContinuousAt r 0 := (testLog_diff ..).continuousAt
  have hF : ContinuousAt F 0 := (show Continuous (increment (1:Config G n)) by unfold increment; fun_prop).continuousAt.comp hr
  rw [show (1:Config G n) = F 0 by unfold F r; rw [testLog_zero, Work.G07.at_zero_increment]]
  exact hF.tendsto.congr' (increment_testLog H d (0:Site n) J).symm

lemma same (H : Hol G) (J : Labels.Jet G) (d : ℕ) (h : P.Regular X f) (hx : X⊆B.cube) :
    let F := H.testLinks d (0:Site n) J
    (fun y : ℝ => f (F y)) =ᶠ[𝓝 0] (f ∘ B.showAt) ∘ (B.input ∘ F) := by
  intro F
  filter_upwards [(hol_near (n:=n) (d:=d) H J).eventually B.authentic] with x hu
  obtain ⟨u,hu⟩ := hu
  exact (h.symmetry u (F x)).symm.trans (h.sites _ _ (agrees_mono hu (Finset.coe_subset.mpr hx)))

lemma full_cover (H : Hol G) (J : Labels.Jet G) (r : ℝ) :
    B.input (H.testLinks d (0:Site n) J r) = P.threshold⁻¹ • (fun i => (B.leg i).eval (H.links d J r)) := by
  funext i; unfold input; simp only [Pi.smul_apply]
  congr 1
  exact ProjectorNext.Calibration.Machine.fitsTest (B.leg i).stencil (B.leg i).eval (B.leg i).covered (B.fits i) _ H d J r
end Board
end YM.Further.CorrectedLift
