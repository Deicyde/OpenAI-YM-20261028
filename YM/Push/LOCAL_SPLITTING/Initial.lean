import YM.Push.LOCAL_SPLITTING.Funding


/-!
# Bare columns on the actual labels (with the specified reservations)

 `Jinit`: flag-requiring complement of a placed unmasked canonical
cylinder. No regular remainder initially. The threshold power, section support
and delay that must be paid to enter the Clocks are explicit. Does not need a
hypothesis on propagated marker estimates or any tuning by the terminal map.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}

theorem full_cost (T : SectionData F) : ∃ K : ℝ, 1 ≤ K ∧ ∀ i : F.Index, ∀ U : CoverConfig G, ‖T.evaluate (Pi.single i 1) U‖ ≤ K := by
  classical
  choose c hc using (fun i : F.Index => (isCompact_range (T.continuous_evaluate (Pi.single i 1)).norm).bddAbove)
  have h i : 0 ≤ max 0 (c i) := le_max_left _ _
  refine ⟨1+∑ i,max 0 (c i), le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => h i)),fun i U => ?_⟩
  exact (((hc i ⟨U,rfl⟩).trans (le_max_right _ _)).trans (Finset.single_le_sum (fun i _ => h i) (Finset.mem_univ i))).trans (le_add_of_nonneg_left zero_le_one)

def fullPrice (T : SectionData F) := (full_cost T).choose

def maxPower (F : Labels.Frame G d) := Finset.univ.sup fun i => (F.grades i).2

theorem full_presented (T : SectionData F) (o : Site n) (B : BudgetPoint) (v : F.Coeff) (U : Config G n) :
    ‖presented T o B.threshold v U‖ ≤ (fullPrice T*(B.threshold⁻¹)^maxPower F)*F.coeffSize v := by
  classical
  let e (i : F.Index) : F.Coeff := Pi.single i 1
  let L := presented T o B.threshold
  have he : L v = ∑ i, v i • L (e i) := by
    simp_rw [← map_smul, ← map_sum]; apply congr_arg L; ext i; simp [e,Finset.sum_apply,Pi.single_apply]
  let r := B.threshold⁻¹
  have hr : 1 ≤ r := (one_le_inv₀ B.threshold_pos).2 B.threshold_le
  have hx (i : F.Index) : ‖L (e i) U‖ ≤ fullPrice T*r^maxPower F := by
    have h : F.scaled r (e i) = (((r^(F.grades i).2:ℝ):ℂ)) • e i := by
      funext j; by_cases hj : j = i <;> simp [e,hj]
    change ‖T.evaluate (F.scaled r (e i)) _‖ ≤ _
    rw [h,T.eval_linear.map_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity),mul_comm]
    exact mul_le_mul ((full_cost T).choose_spec.2 i _) (pow_le_pow_right₀ hr (Finset.le_sup (f:=fun j => (F.grades j).2) (Finset.mem_univ i))) (by positivity) (zero_le_one.trans (full_cost T).choose_spec.1)
  change ‖L v U‖ ≤ (fullPrice T*r^maxPower F)*F.coeffSize v
  rw [he,Finset.sum_apply,Frame.coeffSize,Finset.mul_sum]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => by simp only [Pi.smul_apply,norm_smul]; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hx i) (norm_nonneg _))

namespace Bare

def complement (T : SectionData F) (o : Site n) (t : ℝ) := presented T o t - primary T o t

theorem attaches {T : SectionData F} (h : T.Sound A) (o : Site n) (v : F.Coeff) (t : ℝ) :
    Attaches t (T.footprint o) (complement T o t v) := by
  refine ⟨fun U V huv ht => ?_, fun g U => ?_, (T.continuous_places _ o).measurable.sub (measurable_const.add (masked_measurable _ _ _ (T.continuous_places _ o).measurable)), fun U hu => sub_eq_zero.mpr (presented_primary o h v U hu).symm⟩
  · exact congr_arg₂ (· - ·) (T.placed_local o _ U V huv) (congr_arg (v 0+·) (uses_mask t (T.placed_local o _) U V huv ht))
  exact congr_arg₂ (· - ·) (T.placed_invariant h o _ g U) (congr_arg (v 0+·) (invariant_mask (T.placed_invariant h o _) t _ g U))

theorem bill {T : SectionData F} (h : T.Sound A) (o : Site n) (B : BudgetPoint) (v : F.Coeff) (U : Config G n) :
    ‖complement T o B.threshold v U‖ ≤ (fullPrice T*(B.threshold⁻¹)^maxPower F)*F.coeffSize (F.core v) := by
  apply le_trans _ (full_presented T o B (F.core v) U)
  change ‖presented T o B.threshold v U - (v 0 + masked B.threshold (T.footprint o) _ U)‖ ≤ _
  by_cases hU : Healthy B.threshold (T.footprint o) U
  · change ‖presented T o B.threshold v U - primary T o B.threshold v U‖ ≤ _
    rw [presented_primary o h v U hU,sub_self,norm_zero]; exact norm_nonneg _
  rw [masked_ne _ _ _ _ hU, add_zero]
  conv_lhs => rw [core_split F v,map_add,map_smul,Pi.add_apply,Pi.smul_apply] -- also v 0 replaced!
  simp only [presented,LinearMap.coe_mk, AddHom.coe_mk,F.scaled_unit,SectionData.places,h.unit]
  simp [Frame.core,Frame.e0,add_sub_cancel_left]

variable {T : SectionData F} {R : Rep G n} {o : Site n} {S : Slots R.activities (fun _ : Unit => T.footprint o)}

variable (T R o S) in
def make (v : F.Coeff) : Coefficient F n where
  x := v
  support _ := T.footprint o
  regular := 0
  forced := S.pack R.p.threshold (fun _ => complement T o R.p.threshold v)

theorem format (h : T.Sound A) (hr : R.activities.ForcedFamily R.p) (v : F.Coeff) : (make T R o S v).Format o A R := by
  have ho : o ∈ T.footprint o := Finset.mem_image.mpr ⟨0,h.anchored,by simp⟩
  have he := S.forceFormat hr (fun _ => ho) (fun _ => attaches h o v R.p.threshold)
  exact ⟨fun _ => regular_const _, fun _ => ho, fun _ => rfl,fun _ _ _ => ⟨contDiffAt_const,fun i _ => by simp [make]⟩,he.forcing,he.carried,he.invariant,he.supported,he.borel⟩

theorem exact_density (h : T.Sound A) (v : F.Coeff) {δ w : ℝ} (hr : R.activities.Valid R.p δ w) (U : Config G n) :
    (make T R o S v).density o T R U = (R.eval U : ℂ) * presented T o R.p.threshold v U := by
  let P := make T R o S v
  have he : P.exponentialEntry o T R U = primary T o R.p.threshold v U := by
    suffices h : ∀ i, P.maskedTerm R i U = 0 by simp [Coefficient.exponentialEntry,h]; rfl
    intro i; change maskLinear R.p.threshold (P.support i) (0 : Config G n → ℂ) U = 0 -- syntax
    rw [map_zero]; rfl
  have hr := (S.recover R.p U (fun _ => complement T o R.p.threshold v) (fun _ => attaches h o v _) hr (.of_finite)).tsum_eq
  have hmark : (∑' q, P.marked R q U) = (presented T o R.p.threshold v U - primary T o R.p.threshold v U)*(R.activities.gas R.p U:ℂ) := by
    simp only [gasMark_eq,tsum_fintype,Fintype.sum_unique] at hr; exact hr
  change P.density o T R U = _
  rw [Coefficient.density,hmark,he,Rep.eval,Complex.ofReal_mul]; ring

theorem linear : IsLinearMap ℂ (fun v => (make T R o S v).x) ∧ IsLinearMap ℂ (fun v => (make T R o S v).regular) ∧ IsLinearMap ℂ (fun v => (make T R o S v).forced) ∧ ∀ v, (make T R o S v).support = (make T R o S 0).support := by
  let c : (Config G n → ℂ) →ₗ[ℂ] (Unit → Config G n → ℂ) := LinearMap.pi (fun _ => LinearMap.id)
  have he (v) : (make T R o S v).support = fun _ => T.footprint o := rfl
  exact ⟨LinearMap.id.isLinear, LinearMap.isLinear (0 : F.Coeff →ₗ[ℂ] ℕ → Config G n → ℂ), (S.packLinear R.p.threshold ∘ₗ c ∘ₗ complement T o R.p.threshold).isLinear, fun v => (he v).trans (he 0).symm⟩

theorem cap (h : T.Sound A) (v : F.Coeff) {w : ℝ} (hr : R.activities.KBound R.p w) (hp : 0 < w) :
    let κ := Real.sqrt w
    let cost := mergePrice R.p w (T.footprint o) (fullPrice T*(R.p.threshold⁻¹)^maxPower F * F.coeffSize (F.core v))
    (make T R o S v).remBound o R κ (cost/κ) := by
  intro κ cost
  have hc : 0 < κ := Real.sqrt_pos.mpr hp
  have hC := (full_cost T).choose_spec.1
  have he := S.forceCost (f:=fun _ => complement T o R.p.threshold v) (a:=fun _ => fullPrice T*(R.p.threshold⁻¹)^maxPower F * F.coeffSize (F.core v)) (c:=cost) hr
  have ha : 0 ≤ fullPrice T*(R.p.threshold⁻¹)^maxPower F * F.coeffSize (F.core v) := mul_nonneg (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (inv_nonneg.mpr R.p.threshold_pos.le) _)) (Work.G08.size_nonneg F _)
  have h0 : 0 ≤ cost := mergePrice_nonneg _ _ hp.le ha
  refine ⟨0,cost/κ,le_rfl,by positivity,by rw [zero_add],hc,⟨0, ?_, fun i => by simpa only [norm_zero] using! (bound_const (B:=R.p) (X:=T.footprint o) (o:=o) (0:ℂ))⟩,?_⟩
  · simp only [BudgetPoint.mass, Pi.zero_apply, mul_zero]; exact sumBudget_zero le_rfl
  rw [mul_div_cancel₀ _ hc.ne']; exact he ⟨fun _ => h0, .of_finite, by rw [tsum_fintype,Fintype.sum_unique]⟩ (fun _ => ha) (fun _ => bill h o R.p v)
end Bare

def bareConstant (T : SectionData F) (u : ℝ) := Real.exp (u*atomTiles T)*fullPrice T * (2*(T.stencil.card:ℝ))

theorem bare_charge (T : SectionData F) (o : Site n) (v : F.Coeff) (B : BudgetPoint) {w : ℝ} (hp : 0 < w) (h : (T.stencil.card:ℝ)*w ≤ 1) :
    mergePrice B w (T.footprint o) (fullPrice T*(B.threshold⁻¹)^maxPower F * F.coeffSize (F.core v))/Real.sqrt w ≤
      bareConstant T B.supportExponent*(B.threshold⁻¹)^maxPower F*Real.sqrt w* F.coeffSize (F.core v) := by
  have he : ((T.footprint o).card:ℝ)*w ≤ (T.stencil.card:ℝ)*w := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) hp.le
  have hy := Real.abs_exp_sub_one_le (x:=((T.footprint o).card:ℝ)*w) (by simpa [abs_of_nonneg (le_of_lt hp)] using he.trans h)
  rw [abs_of_nonneg (mul_nonneg (by positivity) hp.le)] at hy
  unfold mergePrice BudgetPoint.mass
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
  apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show ((coverNumber B.B (T.footprint o):ℕ):ℝ) ≤ (atomTiles T:ℝ) by exact_mod_cast atomTiles_price T B o) B.exponent_pos.le))
    (by positivity [show 1 ≤ fullPrice T from (full_cost T).choose_spec.1,B.threshold_pos,Work.G08.size_nonneg F (F.core v)])) (((le_abs_self _).trans hy).trans (mul_le_mul_of_nonneg_left he zero_le_two)) (by simp only [sub_nonneg, Real.one_le_exp_iff]; positivity) (by positivity [show 1 ≤ fullPrice T from (full_cost T).choose_spec.1, B.threshold_pos,Work.G08.size_nonneg F (F.core v)]))
  apply le_of_eq
  nth_rw 1 [← Real.mul_self_sqrt hp.le]; unfold bareConstant; ring

def BareDelay (T : SectionData F) (B : BudgetPoint) (w : ℝ) :=
    (T.stencil.card:ℝ)*w ≤ 1 ∧ bareConstant T B.supportExponent*(B.threshold⁻¹)^maxPower F*Real.sqrt w ≤ 1

theorem thick {T : SectionData F} {o : Site n} {R : Rep G n} {S : Slots R.activities (fun _ : Unit => T.footprint o)} (h : T.Sound A) (v : F.Coeff) {w : ℝ}
    (hr : R.activities.KBound R.p w) (hp : 0 < w) (hpay : BareDelay T R.p w) :
    (Bare.make T R o S v).remBound o R (Real.sqrt w) (F.coeffSize (F.core v)) := by
  obtain ⟨a,b,ha,hb,hab,hv⟩ := Bare.cap (S:=S) h v hr hp
  exact ⟨a,b,ha,hb,hab.trans ((bare_charge _ _ _ _ hp hpay.1).trans (mul_le_of_le_one_left (Work.G08.size_nonneg ..) hpay.2)),hv⟩

theorem charges (H : RG.History G) (N p : ℕ) {T : SectionData F} {o : Site (H.S.side N p)} {S : Slots (H.rep N p N).activities (fun _ : Unit => T.footprint o)}
    (h : H.Conv N p N) (ht : T.Sound A) (v : F.Coeff) (U : Config G (H.S.side N p)) :
    (Bare.make T (H.rep N p N) o S v).density o T (H.rep N p N) U = ((H.S.a N : ℂ)^d) * ((H.rep N p N).eval U : ℂ) * initial T H N p v o U := by
  rw [Bare.exact_density ht v h.good.labels, h.vac]
  simp [presented, Levels.budget, initial, mul_comm ((H.S.a N:ℂ)^d) _,mul_assoc, (H.S.a_pos N).ne']
end YM.Push.Local
