import YM.Push.LOCAL_SPLITTING.Merge

/-!
# Forced-label singleton reattachment for changing anchor on a fixed insertion

Primary forced marks can meet different vacuum labels after an enlargement;
cannot just move their predicates to a larger support without merger. This
version fuses ALL allowed meeting vacuum addresses into a booked address,
retains the pointed mark and old support disjointness and coverage. Same
alphabet, singleton linearity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Lattice Wilson RG Source
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side}



namespace Slots
variable {A : Activities G n} {X : ℕ → Support n} (S : Slots A X)

def fill (t : ℝ) (s : Letters A X) (f : ℕ → Config G n → ℂ) (U : Config G n) :=
  if s.1 ∈ s.bundle ∧ (A.forced (S.label s)).eligible t U then f s.1 U * ∏ i∈s.bundle.erase s.1, (A.K i U : ℂ) else 0

def collect (t : ℝ) : (ℕ → Config G n → ℂ) →ₗ[ℂ] ℕ → Config G n → ℂ where
  toFun f := extend S.label (fun s => S.fill t s f) 0
  map_add' a b := funext fun i => funext fun U => by
    by_cases h : ∃ s, S.label s = i
    · obtain ⟨s,rfl⟩ := h; simp only [S.label.injective.extend_apply, fill, Pi.add_apply]; split <;> simp [add_mul]
    simp [extend_apply' _ _ _ h]
  map_smul' a b := funext fun i => funext fun U => by
    by_cases h : ∃ s, S.label s = i
    · obtain ⟨s,rfl⟩ := h; simp only [S.label.injective.extend_apply, fill, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split <;> simp [mul_assoc]
    simp [extend_apply' _ _ _ h]

@[simp] theorem collect_label (s : Letters A X) (t : ℝ) (f : ℕ → Config G n → ℂ) : S.collect t f (S.label s) = S.fill t s f := S.label.injective.extend_apply (fun s => S.fill t s f) (0 : ℕ → Config G n → ℂ) s
















section Eval
variable (B : BudgetPoint) (U : Config G n) (f : ℕ → Config G n → ℂ)










end Eval
end Slots
end YM.Push.Local
