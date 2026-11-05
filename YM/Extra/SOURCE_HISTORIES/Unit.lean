import YM.Extra.SOURCE_HISTORIES.Merge
import YM.Next.FOUNDATIONS.Regular

/-! Global units do not spawn spurious forced terms. Keep tag supports
anchored even for all zero payloads. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {d : ℕ} {G : Gauge} {F : Labels.Frame G d} {o : Site n}
variable {R : Rep G n} {H : Hol G}

lemma regular0 (P : BudgetPoint) (s : Support n) (o : Site n) :
    P.Regular s (0 : Config G n → ℂ) ∧ P.supBounds o s (0 : Config G n → ℂ) 0 := by
  simpa using Next.Foundations.regular_bound_sum (P:=P) (s:=s) (o:=o) (∅ : Finset ℕ)
    (fun _ => (0 : Config G n → ℂ)) (fun _ => 0) (by simp)

lemma vanishing0 (d : ℕ) (o : Site n) (H : Hol G) : H.PiVanish d o (0 : Config G n → ℂ) := by
  intro J
  refine ⟨contDiffAt_const,fun k hk => ?_⟩
  change iteratedDeriv k (fun _ : ℝ => (0:ℂ)) 0 = 0
  rw [iteratedDeriv_const]; simp

def primary (o : Site n) (v : F.Coeff) : Coefficient F n :=
  ⟨v,fun _ => {o},0,0⟩

theorem primary_format (u : F.Coeff) : (primary o u).Format o H R := by
  refine ⟨fun _ => (regular0 R.p _ o).1,?_,fun _ => rfl,fun _ _ => vanishing0 d o H,?_,?_,fun _ _ _ => rfl,
    fun _ _ _ _ _ => rfl,fun _ => measurable_const⟩
  · intro _; exact Finset.mem_singleton_self _
  · intro i U h; exact (h rfl).elim
  intro i h; exact (h rfl).elim

lemma budget0 (P : BudgetPoint) (s : ℕ → Support n) : SumBudget (fun i => P.mass (s i) 0) 0 := by
  simp [SumBudget,BudgetPoint.mass]

theorem primary_rem (u : F.Coeff) {v : ℝ} (hv : 0 < v) : (primary o u).remBound o R v 0 := by
  refine ⟨0,0,le_rfl,le_rfl,(add_zero 0).le,hv,⟨fun _ => 0,budget0 _ _,fun _ => (regular0 R.p _ o).2⟩,
    fun _ => 0,by rw [mul_zero]; exact budget0 _ _,fun i => ⟨le_rfl,fun U => ?_⟩⟩
  exact (norm_zero (E:=ℂ)).le

theorem primary_density (S : SectionData F) (R : Rep G n) (v : F.Coeff) (U) :
    (primary o v).density o S R U = (R.eval U:ℂ) * part S o R U v := by
  have ht i : (primary o v).maskedTerm R i U = 0 := by
    by_cases he : Healthy R.p.threshold {o} U <;> simp [Coefficient.maskedTerm,primary,he]
  simp only [Coefficient.density,marked_as, ht, Coefficient.exponentialEntry]; simp only [primary,Pi.zero_apply,zero_mul,tsum_zero,mul_zero,add_zero]
  rfl

theorem unit_density (S : SectionData F) (R : Rep G n) (o : Site n) :
    (primary o F.e0).density o S R = fun U => (R.eval U:ℂ) := by
  funext U
  rw [primary_density]
  have he : part S o R U F.e0 = 1 := by
    change F.e0 0 + masked R.p.threshold (S.footprint o) _ U = 1
    rw [Size.unit_core]
    by_cases ht : Healthy R.p.threshold (S.footprint o) U <;> simp [Frame.e0,ht,SectionData.places,SectionData.evaluate]
  rw [he,mul_one]

end YM.Extra.Histories
