import YM.Overlay.Pays
import YM.Vac.Shelter

/-!
# Endpoint estimate in complete marked density

Crude extensive rooted-cost bill, still pays ONCE and allows ∀ numbers
at fixed site multiplicity. Statement after normalizing via FULL denominator.
All markers wall, root limit later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Overlay
open Function Marker RG Lattice Wilson MeasureTheory Filter
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V} {P : Rep G n}
variable (a : Bands R P) {w : V → ℝ} {u c d b σ C Λ δ κ : ℝ} (hr : a.Active) (t : a.Radial w u c d b)
variable (H : P.Lawful σ C Λ δ κ) (hP : 0 ≤ P.beta)

namespace Bands

def fine (nCard : ℕ) (P : Rep G n) (u c d b C Λ δ κ : ℝ) :=
    (Fintype.card (Site n):ℝ)*(P.exCost C Λ δ+κ)+(nCard:ℝ)*(u+c+d*b)

include hP H hr t

lemma physical (U : Config G n) : Poly.price w (a.density U) ≤ Real.exp (P.scalar + fine (Fintype.card V) P u c d b C Λ δ κ) := by
  have h := (a.population hr t H.labels U).2
  have hg := (Poly.pass_budget t.pure _).trans (Real.exp_monotone (a.bulkBound hr t U).2)
  rw [density, Poly.adapted,Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left (Poly.multiplication t.pure ..) (Real.exp_pos _).le).trans
  apply (mul_le_mul (Real.exp_monotone (P.exponent_hi H hP U))
    (mul_le_mul hg h (Poly.nonnegative t.pure _) (Real.exp_pos _).le)
    (mul_nonneg (Poly.nonnegative t.pure _) (Poly.nonnegative t.pure _)) (Real.exp_pos _).le).trans
  rw [← Real.exp_add _ (Fintype.card (Site n)*κ+_), ← Real.exp_add]; unfold fine; exact le_of_eq (by ring_nf)

lemma material (X : R.Mode) : Integrable (fun U => (a.density U).part X) (prior G n) ∧
    ‖(∫ U,(a.density U).part X ∂prior G n)‖ ≤
      Real.exp (P.scalar+fine (Fintype.card V) P u c d b C Λ δ κ) / Poly.toll w X := by
  have he (U : Config G n) : ‖(a.density U).part X‖ ≤ Real.exp (P.scalar+fine (Fintype.card V) P u c d b C Λ δ κ) / Poly.toll w X := by
    rw [le_div_iff₀ (Poly.worth t.pure _),mul_comm]
    exact (Poly.member t.pure _ _).trans (a.physical hr t H hP U)
  have hg := ((Poly.part_cont X).measurable.comp (a.density_meas hr H))
  have hh : Integrable (fun U => (a.density U).part X) (prior G n) := Integrable.of_bound hg.aestronglyMeasurable _ (Eventually.of_forall he)
  refine ⟨hh,(norm_integral_le_integral_norm _).trans ?_⟩
  exact (integral_mono hh.norm (integrable_const _) he).trans (by simp)

/-- `Billed` includes vacuum denominator. Use with `nCard` ≤ L_m vol.
Any unbounded arity factor not already displayed still needs pre-existing
proof budgets; no ℓ^p norm equivalences in this per-site inequality!
-/
def finalBill (nCard : ℕ) (P : Rep G n) (s u c d b C Λ δ κ : ℝ) :=
    (Fintype.card (Site n):ℝ) * ((2*P.exCost C Λ δ)+κ+P.beta*baseBudget P.clip C s +
        4 * Module.finrank ℝ G.Mat*Real.log (16/s)) + (nCard:ℝ)*(u+c+d*b)

lemma total (s : ℝ) (hh : 0<s) (h : s≤P.p.threshold) (hpos : ∀ U,0≤P.eval U) (T : R.Mode) :
    ‖(∫ U,(a.density U).part T∂ prior G n)‖ / (∫ U,P.eval U ∂prior G n) *Poly.toll w T ≤
      Real.exp (finalBill (Fintype.card V) P s u c d b C Λ δ κ) := by
  have ht := P.denominator H hP s hh h hpos
  have hj := lt_of_lt_of_le (Real.exp_pos _) ht
  have hv := (le_div_iff₀ (Poly.worth t.pure _)).mp (a.material hr t H hP T).2
  rw [div_mul_eq_mul_div,div_le_iff₀ hj]
  apply le_trans hv
  apply le_trans _ (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)
  rw [← Real.exp_add]
  unfold fine finalBill
  refine le_of_eq ?_; congr 1
  rw [show Fintype.card (Edge (Site n))=Fintype.card (Site n)*4 by simp [Edge,Axis]]
  push_cast; ring
end Bands
end YM.Overlay
