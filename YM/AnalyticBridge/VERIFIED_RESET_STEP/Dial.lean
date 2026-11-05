import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.UVNext.COUPLING_RESET.Catalog

/-! The new post-activity trial template permits a FULL field response
calculus: fixed reader after the local projections+charges and varying β
in exactly the committed kinetic. No field-independent comparison of different
push kernels is being used. ShapeControl constant may depend on the whole
finite volume (incl signed gas); *not* a uniform remainder price. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Quotes WilsonStartup Averaging Geo Progress.DirectedRecipe Push.BetaTransport UVNext.CouplingReset Collection
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {X : Listing G n} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ α δ γ : ℝ}
    {s t : Set ℝ}

def terms (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (α : ℝ) (a : ℝ → Collection.Source G n) : ℝ → ℝ → Activities G n :=
    fun x _ => (finish R c p (shelves X R p) (branch X R c p (a x) α) 0 0).activities
private lemma budgets_sum {e k : ℕ → ℝ} {S : Activities G n} (h : LabelBudget p e k S δ γ) : Summable e ∧ Summable k := by
  let f (o : Site n) i := if (S.reg i).site=o then p.mass (S.reg i).support (e i) else 0
  exact ⟨(summable_sum (s:=Finset.univ) (fun o _ => (show Summable (f o) from (h.E o).2.1))).of_nonneg_of_le
    (fun i => (h.smooth i).1) (fun i => by simpa [f] using p.loMass (S.reg i).support (e i) (h.smooth i).1),
    Activities.summable_charge (fun i => (S.forced i).inventory_ne.mono (S.forced i).inventory_sup) (fun i => (h.hard i).1) h.K⟩
lemma catalogs {F : ℝ → RG.Rep G n} (hc : Curve p F s) (he : ∀ x∈s,(F x).activities.Valid p δ γ) (hx : R.Bounds c σ C Λ) :
    Catalog ⟨R,c,p,fun x _ => (F x).activities⟩ s t δ γ := by
  have hZ z (hz : z∈s ×ˢ t) : Tendsto Prod.fst (𝓝[s ×ˢ t] z) (𝓝[s] z.1) := by rw [← z.eta, nhdsWithin_prod_eq]; exact tendsto_fst
  refine ⟨fun x hx _ _ => he x hx,⟨_,_,_,hx⟩,fun z hz y hy => hc.reg _ hz.1 _ hy.1,fun z hz y hy => hc.forced _ hz.1 _ hy.1,
    fun z hz => ?_,fun z hz q hq => ?_⟩
  · constructor
    · intro i ε hε; filter_upwards [(hZ z hz).eventually (hc.continuous ε hε _ hz.1)] with ⟨x,v⟩ h
      obtain ⟨a,b,ha,-,hA,-⟩ := h
      have hp := (p.loMass _ _ (ha i).1).trans (Push.AbsoluteSums.budget_single hA i)
      exact ⟨hε.le,fun U hU l hl hd => ((ha i).2 U hU l hl hd).trans hp⟩
    intro i ε hε; filter_upwards [(hZ z hz).eventually (hc.continuous ε hε _ hz.1)] with ⟨x,v⟩ h U
    obtain ⟨a,b,-,hb,-,hB⟩ := h
    exact ((hb i).2 U).trans ((p.loMass _ _ (hb i).1).trans (Push.AbsoluteSums.budget_single hB i))
  obtain ⟨r,e,k,hr,_,hA,hB⟩ := input_subsequence hc hz.1 (he _ hz.1) ((hZ z hz).comp hq) zero_lt_one
  exact ⟨r,e,k,hr.tendsto_atTop,(budgets_sum hA).1,(budgets_sum hA).2,hA.toMajorizes,Eventually.of_forall (fun j => (hB j).toMajorizes)⟩

private lemma exp_meter {x C : ℝ} (hc : 0 ≤ C) (h : x ≤ C) : |Real.exp x - 1| ≤ Real.exp C * |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx))]
    apply le_trans (b:=Real.exp x*x) _ (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h) hx)
    linarith only [(mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le).trans_eq
      (by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] : Real.exp x * Real.exp (-x) = 1)]
  have hx := le_of_not_ge hx
  rw [abs_of_nonpos hx,abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx))]
  linarith only [Real.add_one_le_exp x, mul_le_mul_of_nonneg_right (Real.one_le_exp hc) (neg_nonneg.mpr hx)]

namespace Fixed
variable (A : Template G n) {H : ℝ → Config G n → ℝ} {V : Config G n} {pred : ℝ → ℝ} {x Δ v : ℝ}
lemma rate (hm : ∀ d, A.terms x d = A.terms x Δ) (hf : ∀ i, (A.terms x Δ).E i 1 = 0) (he : flags A.p.threshold V = ∅)
    (h : (A.trial pred x Δ v).eval = H x) (d : ℝ) : A.residual H V pred x d = (d-Δ) * A.leg V := by
  rw [Template.residual,A.contrast_eq hf he (congr_fun h 1) (congr_fun h V),Template.add,hm,← Template.add]; ring

lemma price_shape (hm : ∀ d, A.terms x d = A.terms x Δ) (hf : ∀ i, (A.terms x Δ).E i 1 = 0) (he : flags A.p.threshold V = ∅) (hV : 0 < A.leg V)
    (h : (A.trial pred x Δ v).eval = H x) (U : Config G n) (hw : ∀ d∈t, |d| ≤ 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ d∈t,
      |A.shape pred U x d - H x U / H x 1| ≤ C * |A.residual H V pred x d| := by
  have heq : H x U / H x 1 = A.shape pred U x Δ := by rw [← h, A.trial_one _ hf,A.eval_trial]; exact mul_div_cancel_left₀ _ (Real.exp_pos _).ne'
  let l := |A.leg U|; let r := A.shape pred U x Δ; let D := Real.exp ((1+|Δ|)*l) * l * |r|
  refine ⟨D/A.leg V, div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (abs_nonneg r)) hV.le, fun d hd => ?_⟩
  have hx (d : ℝ) : A.shape pred U x d = Real.exp ((Δ-d)*A.leg U)*r := by
    simp only [r, Template.shape,Template.add,hm d, ← mul_assoc,← Real.exp_add]; congr 2; ring
  rw [heq,hx,rate A hm hf he h,abs_mul,abs_of_pos hV]
  change |Real.exp _ * r - r| ≤ D / _ * _
  rw [← sub_one_mul,abs_mul]; rw [mul_comm _ (A.leg V),← mul_assoc,div_mul_cancel₀ _ hV.ne']
  have hL : 0 ≤ (1+|Δ|)*l := mul_nonneg (add_nonneg zero_le_one (abs_nonneg _)) (abs_nonneg _)
  have hz : (Δ-d)*A.leg U ≤ (1+|Δ|)*l := (le_abs_self _).trans <| by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right ((abs_sub ..).trans (by linarith only [hw d hd])) (abs_nonneg _)
  unfold D; have hi := exp_meter hL hz
  rw [abs_mul,abs_sub_comm Δ d] at hi
  linarith only [mul_le_mul_of_nonneg_right hi (abs_nonneg r)]
end Fixed
end YM.AnalyticBridge.VerifiedReset
