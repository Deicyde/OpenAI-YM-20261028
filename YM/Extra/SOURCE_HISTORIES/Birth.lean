import YM.Extra.SOURCE_HISTORIES.Purchase
import YM.Extra.SOURCE_HISTORIES.Unit

/-!
# Birth of true single-source transfers

Uniform quantitative producer at a chosen level, on its *supplied*
address shelf (a real requirement to be met for the shared Bolt).
E `(pfx),(Jinit)`. No lower bound or division by vacuum; no K product
factorization assumptions. k=full purchased k (address bounds/covers after
growth), and the price still has to fit, see gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {G : Gauge} {d : ℕ} {F : Labels.Frame G d} (S : SectionData F)
variable {A : Hol G}
variable (R : Rep G n) (o : Site n)

/-- True missing piece of the primary column. NOT multiplying the unit by a mask. -/
def supplement (v : F.Coeff) (U : Config G n) :=
  S.places (F.scaled R.p.threshold⁻¹ v) o U - part S o R U v

lemma supplement_linear : IsLinearMap ℂ (supplement S R o) := by
  constructor
  · intro i j; funext U
    simp only [supplement,map_add,SectionData.places,S.eval_linear.map_add,Pi.add_apply]; abel
  intro i j; funext U
  simp only [supplement,map_smul,SectionData.places,S.eval_linear.map_smul,Pi.smul_apply,smul_sub]

lemma healthy_supplement (h : S.Sound A) (v : F.Coeff) (U) (hu : Healthy R.p.threshold (S.footprint o) U) :
    supplement S R o v U=0 := by
  simp only [supplement,part,LinearMap.coe_mk, AddHom.coe_mk, masked_eq _ _ _ _ hu]
  nth_rw 1 [← Size.core_plus F v]
  simp only [map_add,map_smul,SectionData.places,S.eval_linear.map_add, Frame.scaled_unit,
    S.eval_linear.map_smul,Pi.add_apply,h.unit,Pi.one_apply,Pi.smul_apply,smul_eq_mul]; ring

lemma supplement_read (v : F.Coeff) : UsesFinal R.p.threshold (S.footprint o) (supplement S R o v) := by
  intro U V he ht
  have hx (z) := S.placed_local o z U V he
  have hu : Healthy R.p.threshold (S.footprint o) U ↔ Healthy R.p.threshold (S.footprint o) V := by
    simp only [Healthy,Finset.disjoint_iff_inter_eq_empty]; rw [ht]
  by_cases hh : Healthy R.p.threshold (S.footprint o) U
  · simp only [supplement,part,LinearMap.coe_mk, AddHom.coe_mk,masked_eq _ _ _ U hh,masked_eq _ _ _ V (hu.mp hh),hx]
  simp only [supplement,part,LinearMap.coe_mk, AddHom.coe_mk, masked_ne _ _ _ U hh,
    masked_ne _ _ _ V (fun h => hh (hu.mpr h)),hx]

lemma supplement_gauge (h : S.Sound A) (v : F.Coeff) : GaugeInvariant (supplement S R o v) := by
  intro k U
  have hu : Healthy R.p.threshold (S.footprint o) (gauge k U) ↔ Healthy R.p.threshold (S.footprint o) U := by
    simp [Healthy]
  by_cases hh : Healthy R.p.threshold (S.footprint o) U
  · rw [healthy_supplement S R o h v _ hh, healthy_supplement S R o h v _ (hu.mpr hh)]
  simp only [supplement,part,LinearMap.coe_mk, AddHom.coe_mk, masked_ne _ _ _ U hh,
    masked_ne _ _ _ _ (fun h => hh (hu.mp h)), S.placed_invariant h o _ k U]

lemma supplement_meas (v : F.Coeff) : Measurable (supplement S R o v) :=
  (S.continuous_places ..).measurable.sub (measurable_const.add
    (masked_measurable _ _ _ (S.continuous_places ..).measurable))

/-- Max slot degree cost in this *one* section. Works also d=0. -/
def degree (F : Labels.Frame G d) : ℕ := Finset.univ.sup (fun i => (F.grades i).2)

def fullCost (F : Labels.Frame G d) (p : BudgetPoint) (c : ℝ) := c * p.threshold⁻¹^(degree F)

lemma supplement_bound (h : S.Sound A) {B : ℝ} (hb : 1 ≤ B)
    (ht : ∀ (i : F.Index) U, ‖S.places (Size.axis F i) o U‖ ≤ B) (v : F.Coeff) (U) :
    ‖supplement S R o v U‖ ≤ fullCost F R.p B * F.coeffSize (F.core v) := by
  have hB := lt_of_lt_of_le zero_lt_one hb
  let z := F.scaled R.p.threshold⁻¹ (F.core v)
  have h0 := R.p.threshold_pos
  have hQ : 0 ≤ fullCost F R.p B := by unfold fullCost; positivity
  by_cases hh : Healthy R.p.threshold (S.footprint o) U
  · rw [healthy_supplement S R o h v _ hh,norm_zero]
    exact mul_nonneg hQ (Work.G08.size_nonneg ..)
  have ht' : supplement S R o v U = S.places z o U := by
    simp only [supplement,part,LinearMap.coe_mk, AddHom.coe_mk,masked_ne _ _ _ _ hh]
    nth_rw 1 [← Size.core_plus F v]
    simp only [map_add,map_smul,SectionData.places,S.eval_linear.map_add, Frame.scaled_unit,
      S.eval_linear.map_smul,Pi.add_apply,h.unit,Pi.one_apply,Pi.smul_apply,smul_eq_mul]; unfold z; ring
  rw [ht']
  let f : F.Coeff →ₗ[ℂ] ℂ := {
    toFun i := S.places i o U
    map_add' a b := congr_fun (S.eval_linear.map_add a b) (expandAt o U)
    map_smul' a b := congr_fun (S.eval_linear.map_smul a b) (expandAt o U) }
  have hz i : ‖z i‖ ≤ R.p.threshold⁻¹^(degree F) * ‖F.core v i‖ := by
    have hh : 1 ≤ R.p.threshold⁻¹ := (one_le_inv₀ h0).mpr R.p.threshold_le
    have he : (F.grades i).2 ≤ degree F := Finset.le_sup (f:=fun i => (F.grades i).2) (Finset.mem_univ i)
    unfold z
    rw [F.scaled_apply,norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hh he) (norm_nonneg _)
  calc
    _ = ‖∑ i, z i • f (Size.axis F i)‖ := by simp_rw [← map_smul,← map_sum,Size.sum_axes]; rfl
    _ ≤ ∑ i, ‖z i • f (Size.axis F i)‖ := norm_sum_le ..
    _ ≤ ∑ i, fullCost F R.p B * ‖F.core v i‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_smul]; refine (mul_le_mul (hz i) (ht i U) (norm_nonneg _)
        ((norm_nonneg _).trans (hz i))).trans_eq ?_; unfold fullCost; ring
    _ = _ := by rw [Frame.coeffSize,Finset.mul_sum]

variable (H : Shelf R.activities)

def born (q : ℕ) (v : F.Coeff) : Coefficient F n :=
  { primary o v with forced := Attach.line R (S.footprint o) H q (supplement S R o v) }

def fee (F : Labels.Frame G d) (p : BudgetPoint) (Y : Support n) (B w : ℝ) :=
    fullCost F p B * (p.mass Y 1 * (Real.exp (Y.card*w)-1))

/-- Actual price paid at birth; hypotheses below are native-stage checks.
Price chosen before p or N in clock application: B comes from the single
section (e.g., Next.Foundations.full_value_bound); check fees vs sqrt w
under coupling delays, not via volume limits. `Shelf` is on the SAME path.
-/
theorem launched {σ C Λ δ w : ℝ} (hS : S.Sound A) (h : R.Lawful σ C Λ δ w) (hW : 0 < w) {B : ℝ} (hb : 1 ≤ B)
    (ht : ∀ (i : F.Index) U, ‖S.places (Size.axis F i) o U‖ ≤ B)
    (hm : fee F R.p (S.footprint o) B w ≤ Real.sqrt w) (q : ℕ) :
    Ledger F n (born S R o H q) ∧ ∀ v,
    (born S R o H q v).Format o A R ∧ (born S R o H q v).remBound o R (Real.sqrt w) (F.coeffSize (F.core v)) ∧
    ∀ U,(born S R o H q v).density o S R U = (R.eval U:ℂ)* S.places (F.scaled R.p.threshold⁻¹ v) o U := by
  classical
  let Y := S.footprint o
  have hy : o∈Y := Finset.mem_image.mpr ⟨0,hS.anchored,by simp⟩
  refine ⟨⟨?_,?_,?_,fun _ => rfl⟩,fun v => ?_⟩
  · exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  · constructor
    · intro a b; simp [born,primary]
    intro a b; simp [born,primary]
  · have hx := Attach.line_linear R Y H q
    have hy := supplement_linear S R o
    exact (((IsLinearMap.mk' _ hx).comp (IsLinearMap.mk' _ hy)).isLinear)
  let f := supplement S R o v
  let P := born S R o H q v
  have hf := supplement_bound S R o hS hb ht v
  have hr (i) : SlotFit R o i (P.forced i) :=
    Attach.line_fit R Y H q hy (supplement_gauge _ _ _ hS v) (supplement_meas ..) (supplement_read S R o v) h.labels.forced i
  refine ⟨?_,?_,fun U => ?_⟩
  · have hx := primary_format (o:=o) (H:=A) (R:=R) v
    exact ⟨hx.smooth, hx.origin,hx.identity_null,hx.projects,fun i => (hr i).permits,fun i => (hr i).tagged,
      fun i => (hr i).invariant,fun i => (hr i).read,fun i => (hr i).borel⟩
  · obtain ⟨p,hp,hH⟩ := Attach.line_budget R Y H q hf h.labels.boundK
    refine ⟨0,_,le_rfl, Work.G08.size_nonneg F (F.core v), (zero_add _).le,Real.sqrt_pos.2 hW,
      ⟨fun _ => 0,budget0 R.p _,fun _ => (regular0 R.p _ o).2⟩,p,⟨hp.1,hp.2.1,?_⟩, hH⟩
    refine hp.2.2.trans ?_
    calc
      _ = fee F R.p Y B w * F.coeffSize (F.core v) := by unfold fee; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (Work.G08.size_nonneg ..)
  have he : P.exponentialEntry o S R U = part S o R U v := by
    have ht (i) : P.maskedTerm R i U=0 := by
      by_cases he : Healthy R.p.threshold {o} U <;> simp [P,born,primary,Coefficient.maskedTerm,he]
    unfold Coefficient.exponentialEntry; simp only [ht,tsum_zero,add_zero]; rfl
  have hk : ∑' b, P.marked R b U = f U * (R.activities.gas R.p U:ℂ) := by
    unfold f
    rw [Attach.paid R Y H q U h ⟨_,hf⟩ (healthy_supplement S R o hS v) |>.symm]
    exact tsum_congr fun _ => marked_as ..
  change P.density o S R U = _
  rw [Coefficient.density,he,hk]
  unfold Rep.eval f supplement
  push_cast
  ring

end YM.Extra.Histories
