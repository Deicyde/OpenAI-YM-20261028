import YM.Next.FOUNDATIONS.Readout
import YM.Next.FOUNDATIONS.Regular

/-!
# Local readout with the actual data: finite-budget consumer

For any B70 `Regular`, the reference parts can actually be read at the
purchased price and separated with the exact PiVanish/identity-null
properties of `Source.Coefficient.Format`. This is subtraction on *unmasked*
functions. We retain both supports. E.g., making a similar decomposition at
density level will at least require handling the masks (they needn't agree!),
cost of external reads and support enlargement/merging. That larger problem,
true matching dynamics/invertibility, etc., are not addressed at this cut.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations
open Function Filter Lattice Wilson RG Source Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}

lemma combination_bound {d : ℕ} {F : Labels.Frame G d} {T : SectionData F}
    (B : BudgetPoint) (o : Site n) {u : ℝ} (hT : Bid.Credit T B.order B.power u) (v : F.Coeff) :
    B.Regular (T.footprint o) (T.places v o) ∧
      B.supBounds o (T.footprint o) (T.places v o) (u * F.coeffSize (F.scaled B.threshold v)) := by
  classical
  let c (i : F.Index) := u*B.threshold^(F.grades i).2
  let L : F.Coeff →ₗ[ℂ] Config G n → ℂ := {
    toFun v := T.places v o
    map_add' a b := funext fun U => congr_fun (T.eval_linear.map_add a b) (expandAt o U)
    map_smul' a b := funext fun U => congr_fun (T.eval_linear.map_smul a b) (expandAt o U) }
  let P i := L (Pi.single i 1)
  have he : T.places v o = ∑ i : F.Index, v i • P i := by
    change L v = _
    simp_rw [P, ← map_smul, ← map_sum]
    apply congr_arg L
    ext1 i
    simp [Pi.single_apply]
  rw [he]
  have hu (i : F.Index) : u * ‖F.scaled B.threshold v i‖ = ‖v i‖ * c i := by
    rw [F.scaled_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg B.threshold_pos.le _)]
    unfold c; ring
  unfold Frame.coeffSize
  rw [Finset.mul_sum]; simp_rw [hu]
  exact regular_bound_sum _ _ _ fun i _ => ⟨regular_smul _ (hT B rfl rfl n o i).1,
    bound_smul _ (hT B rfl rfl n o i).2⟩

lemma reads_null_iff (H : Hol G) (d : ℕ) (o : Site n) (X : Support n) (f : Config G n → ℂ) :
    Reads H o X (0 : Label G d) f ↔ f 1 = 0 ∧ (Nonwrapping X o → H.PiVanish d o f) := by
  classical
  by_cases he : Nonwrapping X o
  · rw [Reads, if_pos he, jetTest_zero_iff]
    refine ⟨fun h => ⟨?_, fun _ => h⟩, fun h => h.2 he⟩
    have ht := (h (0:Jet G)).2 0 (Nat.zero_le _)
    simpa only [iteratedDeriv_zero, test_one] using ht
  rw [Reads, if_neg he]
  rw [eq_comm]
  simp [he, smul_eq_zero, unit_not_zero]

lemma reads_sub {H : Hol G} {o : Site n} {X : Support n} {f g : Config G n → ℂ}
    {d : ℕ} {p q : Label G d} (hp : Reads H o X p f) (hq : Reads H o X q g) :
    Reads H o X (p-q) (f-g) := by
  classical
  unfold Reads at *
  split at hp <;> rename_i ha
  · rw [if_pos ha] at hq ⊢
    intro J
    have he := hp J
    have ht := hq J
    refine ⟨he.1.sub ht.1, (read_smooth J _ _).contDiffAt,fun k hk => ?_⟩
    have hk' : (k : WithTop ℕ∞) ≤ (d : WithTop ℕ∞) := Nat.cast_le.mpr hk
    simp only [Pi.sub_apply, Submodule.coe_sub, map_sub]
    rw [iteratedDeriv_fun_sub (he.1.of_le hk') (ht.1.of_le hk'), he.2.2 k hk, ht.2.2 k hk]
    exact (iteratedDeriv_fun_sub (he.2.1.of_le hk') (ht.2.1.of_le hk')).symm
  rw [if_neg ha] at hq ⊢
  rw [hp,hq,Pi.sub_apply]
  exact (sub_smul _ _ _).symm





end YM.Next.Foundations
