import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Reprice
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.MaskMotion
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Walls



/-!
# The TWO masks used in the respective pre-reset interfaces

Caution: even on the same step data and layout, `CouplingShape.received`
and `VerifiedReset.Collection.earlyValue` are not interchangeable. Show
exactly the quadratic-mask difference (on genuine V, no factoring a
quadratic in place of it), keeping signed rebase & term stencils. Only the
direct plaquette terms differ. Produce the *local* correction for retaining
this difference (do not change any accepted definition). For a witness that
the two-mask issue is real see `Shadow`. E permits different choices here,
but requires preserving indicators and performing paid attachment when
shifting.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas.TwoMasks
open RG Lattice Wilson PathData MeasureTheory Filter Function
open AnalyticBridge.CouplingShape AnalyticBridge.VerifiedReset Next.Scheduling Push.LogIdentity
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side}

/-- The orientation-preserving shuffling of the prescriptions. No quotient by
support or by equality of two curvature rows. -/
def seats (n : Side) : Card n ≃ Collection.Faces n where
    toFun x := ((x.turns,x.atPin),x.token)
    invFun x := (x.1.2,x.1.1,x.2)
    left_inv _ := rfl
    right_inv _ := rfl

variable (R : PathData G) (c : Clip) (p : BudgetPoint)

/-- `wide` is the regular address used for the extra alpha charge in
Collection; `cardSite` is the other one. -/
def wide (i : Card n) : RegularAddress n :=
    let (y,z) := seats n i
    y.reg (z.home R p 0) (z.small_home R p 0)

lemma inclusion (i : Card n) : (cardSite R p i).support ⊆ (wide R p i).support := by
  change i.region (imageOf R p _) ⊆ i.region (Low.home R _ p _)
  apply Finset.image_subset_image
  rcases i with ⟨o,s,a,_|i,j⟩
  · change halo 1 { (0:Site n) } ⊆ halo p.B _
    exact Corona.halo_mono p.B_pos (Finset.Subset.refl _)
  exact Finset.Subset.refl _

lemma marked (i : Card n) (V : Config G n) :
    let (x,L) := seats n i
    young R c i V = factor * (L.mark R c * L.plain R 0 (x.view V)) := by
  rcases i with ⟨o,s,a,_|i,j⟩
  · unfold young Around.read raw; simp only [Sum.elim_inl]
    change factor * c.direct * _ = factor * (c.direct * _)
    rw [mul_assoc]; rfl
  unfold young Around.read raw
  simp only [Around.token,Sum.elim_inr,seats]
  unfold copper
  change factor/2 * _ * _ * _ = factor*((_ * _)*(_/2))
  simp only [Around.turns,Around.atPin,Seat.view,Low.left,Low.right,Equiv.coe_fn_mk,AnalyticBridge.CouplingShape.first,earnCoeff]
  ring

def wider (i : Card n) := masked p.threshold (wide R p i).support (young R c i)

lemma signifies (V : Config G n) (i : Card n) :
    let z := seats n i
    wider R c p i V=factor * z.2.maskedPlain R c 0 p (z.1.view V) := by
  intro z
  let X := z.2.home R p (0:Site n)
  have he : (wide R p i).support = z.1.spread X := rfl
  have hvi := z.1.healthy p.threshold X V
  unfold wider Low.maskedPlain; rw [he]
  by_cases hh : Healthy p.threshold X (z.1.view V)
  · rw [masked_eq _ _ _ _ (hvi.2 hh),masked_eq _ _ _ _ hh]
    exact marked ..
  rw [masked_ne _ _ _ _ (mt hvi.1 hh),masked_ne _ _ _ _ hh,mul_zero]

lemma tallyWide {σ C Λ : ℝ} (hR : R.Bounds c σ C Λ) (V : Config G n) :
    Collection.receipt R c p V = ∑' i,wider R c p i V := by
  rw [Collection.receipt,layer_total (f:=fun i => Low.maskedPlain R c i 0 p)
    _ (fun U=> Low.maskedPlain_sum hR p 0 U)]
  let e := seats n; let F (z : Collection.Faces n) := factor*z.2.maskedPlain R c 0 p (z.1.view V)
  change ∑' i,F i = _; rw [← e.tsum_eq]; exact tsum_congr (fun i => (signifies ..).symm)

/-- Volume-dependent, no extra width price assumed for the *identity*. -/
def due (i : Card n) := (factor * 2) * |(seats n i).2.mark R c|
lemma profile (i : Card n) (V : Config G n) : ‖young R c i V‖ ≤ due R c i := by
  let z := seats n i; let v := z.1.view V
  have hp : ‖z.2.plain R 0 v‖ ≤ 2 := by
    unfold Low.plain
    cases h : z.2.2 with
    | inl _ =>
      simp only [Sum.elim_inl]; exact (Real.norm_of_nonneg (G.price_range _).1).trans_le (G.price_range _).2
    | inr j =>
      rw [Sum.elim_inr, norm_div,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2),Real.norm_eq_abs,div_le_iff₀ (by norm_num : (0:ℝ)<2)]
      have he (r : Slot) : ‖r.atSite v 0‖ ≤ 2 := r.eval_norm ..
      exact (abs_real_inner_le_norm ..).trans (mul_le_mul (he _) (he _) (norm_nonneg _) (by norm_num))
  have he : young R c i V=factor * (z.2.mark R c * z.2.plain R 0 v) := marked ..
  rw [he,norm_mul, norm_mul,Real.norm_of_nonneg factor_pos.le]
  unfold due
  rw [mul_right_comm factor (2:ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) factor_pos.le

lemma prices {σ C Λ : ℝ} (hR : R.Bounds c σ C Λ) : Summable (due (n:=n) R c) := by
  let f (x : Collection.Faces n) := |x.2.mark R c|
  have he : Summable f := (summable_prod_of_nonneg (f:=f) (fun _ => abs_nonneg _)).mpr
    ⟨fun _ => Low.mark_sum hR,Summable.of_finite⟩
  exact ((seats n).summable_iff.mpr he).mul_left _

lemma original {σ C Λ : ℝ} (hR : R.Bounds c σ C Λ) (V : Config G n) :
    Summable (fun i => framed R c p i V) ∧ Summable (fun i => wider R c p i V) := by
  have he : Summable fun i => young R c i V := (prices R c hR).of_norm_bounded (profile R c · V)
  exact ⟨Low.masked_summable _ _ _ _ he,Low.masked_summable _ _ _ _ he⟩

/-- Mask prenormalization discrepancy. At zero flags it vanishes; a single function
on whole V. Signed, in the exponent (log of a genuine positive correction, NOT
asserting positivity of any covered or forced gas). -/
def ticket (α : ℝ) (i : Card n) (V : Config G n) : ℝ := α * (framed R c p i V - wider R c p i V)

def slips (n : Side) : Slip n := ⟨Card n, fun i => (wide R p i).support,fun i => ⟨_, (wide R p i).anchor⟩⟩



lemma spends (α : ℝ) : (slips R p n).Lands p (ticket R c p α) := by
  intro i V ht hV
  apply ht
  unfold ticket framed wider
  change Healthy p.threshold (wide R p i).support V at hV
  rw [masked_eq _ _ _ _ hV,masked_eq _ _ _ _ (Finset.disjoint_of_subset_left (inclusion R p i) hV),sub_self,mul_zero]

lemma routes (α : ℝ) : (slips R p n).Vouched p (ticket R c p α) := by
  let f (i : Card n) := MaskMotion.diff (fun i => (cardSite R p i).support) (fun i => (wide R p i).support) p (young R c) i
  have h (i : Card n) := MaskMotion.diff_used (fun i => (cardSite R p i).support) (fun i => (wide R p i).support) p
    (young R c) i (inclusion R p i) (young_local R c p i).1
  have he (i : Card n) : ticket R c p α i = fun U => -α * f i U := by
    ext U; unfold ticket framed wider f MaskMotion.diff; ring
  refine ⟨fun i U V ha hb => ?_,fun i k V => ?_,fun i => ?_⟩
  · rw [he]; exact congr_arg (-α * ·) ((h i).2.1 U V ha hb)
  · rw [he]; exact congr_arg (-α * ·) ((h i).2.2 k V)
  rw [he]; exact measurable_const.mul (h i).1

end YM.PhysicalNext.PreAtlas.TwoMasks
