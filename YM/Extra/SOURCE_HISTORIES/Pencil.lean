import YM.Extra.SOURCE_HISTORIES.Merge
import YM.Next.FOUNDATIONS.Regular

/-! Scalar and finite linear superposition operators on exact addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {d : ℕ} {ι : Type*} {G : Gauge} {F : Labels.Frame G d} {o : Site n}
variable {R : Rep G n} {H : Hol G}

/-- No reassigning supports based on coefficient values. -/
def stretch (c : ℂ) (P : Coefficient F n) : Coefficient F n where
  x := c • P.x
  support := P.support
  regular := c • P.regular
  forced := c • P.forced

lemma masked_scale (c : ℂ) (f : Config G n → ℂ) (t : ℝ) (S : Support n) (U) :
    masked t S (c • f) U = c • (masked t S f U) := by
  by_cases hu : Healthy t S U <;> simp [hu]

theorem stretch_density (S : SectionData F) (R : Rep G n) (o : Site n) (c : ℂ) (P : Coefficient F n) (U) :
    (stretch c P).density o S R U = c * P.density o S R U := by
  let Q := stretch c P
  have hb (j) : Q.maskedTerm R j U = c * P.maskedTerm R j U := masked_scale ..
  have he : Q.exponentialEntry o S R U = c * P.exponentialEntry o S R U := by
    change part S o R U (c • P.x) + ∑' j, Q.maskedTerm R j U = c * ((part S o R U) P.x + ∑' j, P.maskedTerm R j U)
    simp only [map_smul, hb, smul_eq_mul,tsum_mul_left, mul_add]
  have hf (b) : Q.marked R b U = c * P.marked R b U := by
    rw [marked_as,marked_as, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    change (c*_) * _ = c * (_ * _); ring
  unfold Coefficient.density
  change _ * Q.exponentialEntry .. + _ * ∑' b, Q.marked R b U = _
  simp only [he,hf,tsum_mul_left]; ring

theorem stretch_format {P : Coefficient F n} (c : ℂ) (h : P.Format o H R) :
    (stretch c P).Format o H R where
  origin := h.origin
  identity_null i := by simp [stretch, h.identity_null]
  projects i he := by
    intro J
    let F := fun r : ℝ => P.regular i (H.testLinks d o J r)
    obtain ⟨ht,hk⟩ := h.projects i he J
    refine ⟨(show ContDiffAt ℝ _ F 0 from ht).const_smul c,fun j hj => ?_⟩
    change iteratedDeriv j (c • F) 0 = 0
    rw [iteratedDeriv_const_smul (ht.of_le (Nat.cast_le.mpr hj)), show iteratedDeriv j F 0 = 0 from hk j hj, smul_zero]
  smooth i := Next.Foundations.regular_smul _ (h.smooth i)
  forcing i U hu := h.forcing i U fun he => hu (by simp [stretch,he])
  carried i hi := h.carried i fun he => hi (by simp [stretch,he])
  borel i := (h.borel i).const_smul c
  invariant i k U := congr_arg (c • ·) (h.invariant i k U)
  supported i U V hA hF := congr_arg (c • ·) (h.supported i U V hA hF)

lemma mass_scale (p : BudgetPoint) (X : Support n) (a b : ℝ) : p.mass X (a*b) = a * p.mass X b := by
  unfold BudgetPoint.mass; ring

theorem stretch_rem {P : Coefficient F n} {t v : ℝ} (c : ℂ) (h : P.remBound o R v t) :
    (stretch c P).remBound o R v (‖c‖ * t) := by
  obtain ⟨a,b,ha,hb,hw,h₀,⟨e,he,ht⟩,f,hf,hy⟩ := h
  have hl i := Next.Foundations.bound_smul c (ht i)
  refine ⟨‖c‖*a,‖c‖*b,mul_nonneg (norm_nonneg _) ha,mul_nonneg (norm_nonneg _) hb,?_,h₀,
    ⟨fun i => ‖c‖*e i,?_,hl⟩,fun i => ‖c‖*f i,?_,fun i => ⟨mul_nonneg (norm_nonneg _) (hy i).1,fun U => ?_⟩⟩
  · rw [← mul_add]; exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  · simp_rw [mass_scale]; exact budget_scale he (norm_nonneg _)
  · simp_rw [mass_scale, mul_left_comm v ‖c‖ b]; exact budget_scale hf (norm_nonneg _)
  rw [show (stretch c P).forced i U=c • P.forced i U from rfl,norm_smul]
  exact mul_le_mul_of_nonneg_left ((hy i).2 U) (norm_nonneg _)

section Pencil
variable (e : ℕ ≃ ι × ℕ) (P : ι → Coefficient F n) (w : F.Coeff →ₗ[ℂ] ι → ℂ)

def pencil (v : F.Coeff) := merge e (fun i => stretch (w v i) (P i))

variable [Fintype ι]

theorem pencil_x (v : F.Coeff) : (pencil e P w v).x = ∑ i, w v i • (P i).x := tsum_fintype _

/-- `Paper.Clocks.linear` on a manufactured column family. -/
structure Ledger (F : Labels.Frame G d) (n : Side) (P : F.Coeff → Coefficient F n) : Prop where
  x : IsLinearMap ℂ fun v => (P v).x
  reg : IsLinearMap ℂ fun v => (P v).regular
  f : IsLinearMap ℂ fun v => (P v).forced
  tags v : (P v).support = (P 0).support

theorem pencil_ledger : Ledger F n (pencil e P w) := by
  have hk (v : F.Coeff) (j) (U) : (pencil e P w v).forced j U = ∑ i, w v i • (P i).forced j U := tsum_fintype _
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,fun _ => rfl⟩
  · intro x y; simp only [pencil_x,map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · intro x y; simp only [pencil_x, map_smul,Pi.smul_apply,Finset.smul_sum,smul_assoc]
  · intro x y; funext j U; simp [pencil,merge,stretch,add_mul]
  · intro x y; funext j U; simp [pencil,merge,stretch,mul_assoc]
  · intro x y; funext j U; simp only [hk, map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  intro x y; funext j U; simp only [hk, map_smul, Pi.smul_apply, smul_assoc]; simp only [Finset.smul_sum]

theorem pencil_cost {X : ι → ℝ} {v : ℝ} (hp : 0 < v) (h : ∀ i, (P i).Format o H R ∧
    (P i).remBound o R v (X i)) (u : F.Coeff) : (pencil e P w u).Format o H R ∧
      (pencil e P w u).remBound o R v (∑ i, ‖w u i‖ * X i) := by
  classical
  refine ⟨merge_format e _ (fun i => stretch_format _ (h i).1),?_⟩
  let V i := stretch (w u i) (P i)
  have hx i := stretch_rem (w u i) (h i).2
  simpa only [tsum_fintype,pencil,V] using (merge_budget e V hp hx (hasSum_fintype _).summable).1

theorem pencil_density {X : ι → ℝ} {v : ℝ} {σ C Λ δ w' : ℝ}
    (hr : R.Lawful σ C Λ δ w') (hp : 0 < v) (h : ∀ i, (P i).remBound o R v (X i)) (u : F.Coeff)
    (B : SectionData F) (U) :
    (pencil e P w u).density o B R U = ∑ i, w u i * (P i).density o B R U := by
  classical
  let V i := stretch (w u i) (P i)
  rw [show (pencil e P w u).density o B R U = ∑' i, (V i).density o B R U from (merge_density e V hp hr
    (fun i => stretch_rem _ (h i)) (hasSum_fintype _).summable (hasSum_fintype _).summable B U).tsum_eq.symm,tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => stretch_density ..

end Pencil
end YM.Extra.Histories
