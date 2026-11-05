import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product of link chart densities over a finite index set

The Jacobian argument uses restricted *measures*. Here are product
facts for their nonnegative densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal BigOperators

-- lprodFin adapts the Fin-coordinate decomposition of Mathlib's
-- integral_fin_nat_prod_eq_prod to ENNReal lintegrals, adding explicit
-- measurability hypotheses. Copyright (c) 2023 Xavier Roblot. All rights
-- reserved. Apache-2.0. See NOTICE.
private lemma lprodFin {n : ℕ} {E : Fin n → Type}
    [mE : ∀ i, MeasurableSpace (E i)] (μ : (i : Fin n) → Measure (E i))
    [hμ : ∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (h : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    let W := (measurePreserving_piFinSuccAbove μ 0).symm
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
          f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
            rw [W.lintegral_map_equiv]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
            rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) * (∫⁻ x : (i : Fin n) → E (Fin.succ i),
          ∏ i : Fin n, f i.succ (x i) ∂Measure.pi (fun i ↦ μ i.succ)) :=
            lintegral_prod_mul (h 0).aemeasurable (g:=fun x : (i : Fin n) → E (Fin.succ i) => ∏ i : Fin n, f i.succ (x i)) (by apply Measurable.aemeasurable; fun_prop)
      _ = _ := by
            rw [ih (fun i : Fin n => μ i.succ) (fun i => f i.succ) (fun i => h i.succ),
              Fin.prod_univ_succ]

section finite
variable {ι : Type} [Fintype ι] {E : ι → Type} [mE : ∀ i, MeasurableSpace (E i)]

lemma lprod (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (h : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [(measurePreserving_piCongrLeft μ e).lintegral_map_equiv]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lprodFin _ _ (fun i => h (e i))

lemma piDensity (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (h : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) =
      Measure.pi (fun i => (μ i).withDensity (f i)) := by
  refine Eq.symm (Measure.pi_eq (fun s hs => ?_))
  simp_rw [withDensity_apply _ (hs _), withDensity_apply _ (.univ_pi hs), restrict_pi_pi]
  exact lprod _ _ h
end finite
end YM.Work.F05
