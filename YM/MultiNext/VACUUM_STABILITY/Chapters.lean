import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# Raw first-system conversion through the actual analytic log
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

namespace Rates
variable (P : BudgetPoint)
lemma radius_nice : 0 < radius P := add_pos P.exponent_pos (by norm_num)
lemma inner_pos : 0 < inner P := add_pos (radius_nice _) zero_lt_one
lemma gate : 1 ≤ siteUnit P.B := by unfold siteUnit; exact one_le_pow₀ (by simp)
lemma window_pos : 0 < window P := inv_pos.mpr (mul_pos (by norm_num) (zero_lt_one.trans_le (gate P)))
lemma raw_pos : 0 < raw P := div_pos (window_pos _) (add_pos zero_lt_one (logPrice_pos _))
lemma cabin : window P ≤ 1/64 := by
  unfold window
  have hh := gate P
  rw [one_div]; apply inv_anti₀ (by norm_num); linarith
lemma still_thin : raw P ≤ window P := by
  unfold raw; apply div_le_self (window_pos P).le; linarith [logPrice_pos P]
lemma funded : logPrice P*raw P ≤ window P := by
  have hv := logPrice_pos P
  unfold raw; rw [←mul_div_assoc]; apply (div_le_iff₀ (by linarith)).mpr
  nlinarith [window_pos P]
lemma launchable : siteUnit P.B * (5*window P) ≤ 1 := by
  have h := gate P; have ht : 0 < siteUnit P.B := by linarith
  unfold window; rw [←one_div,mul_one_div,←mul_div_assoc]; rw [div_le_iff₀ (by positivity)]; linarith

end Rates

variable {I : Type*} {V : Type} {n : Side} {G : Gauge}



def Widens (L : V→Support n→Prop) := ∀ i a b, a ⊆ b → L i a → L i b

namespace SmoothLetter
variable (T : SmoothLetter V G n) [Fintype V]

def echoes (P : BudgetPoint) (z : V → ℂ) := masked P.threshold T.zone (T.stamp.tell z)

lemma tint (P : BudgetPoint) (z : V → ℂ) (U : Config G n) : T.echoes P z U =
    Stamp.beat T.stamp.name z * masked P.threshold T.zone T.stamp.ink U := by
  unfold echoes; by_cases H : Healthy P.threshold T.zone U <;> simp [H]

lemma rate_echo (P : BudgetPoint) (z : V → ℂ) (o : Site n) {c : ℝ} (hh : P.supBounds o T.zone (T.stamp.tell z) c) :
    ∀ U, ‖T.echoes P z U‖ ≤ c := by
  intro U; unfold echoes
  by_cases he : Healthy P.threshold T.zone U
  · rw [masked_eq _ _ _ _ he]; exact hh.2 U he [] (by simp) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact hh.1
end SmoothLetter

namespace Brush
variable (B : Brush V G n) {P : BudgetPoint} {C : Restock V G n} {L : V → Support n → Prop} {T : Finset V}

lemma chap_ok (h : Supported B C P L T) (j) : P.Regular (B.chapter j).zone (B.chapter j).stamp.ink :=
  Jets.stanza_regular _ _ _ h.reg _



variable [Fintype V]

lemma chap_eq (z : V→ℂ) (i) : (B.chapter i).stamp.tell z =
    Jets.stanza (fun i => (B.u i).stamp.tell z) (B.station.tune.line i) := by
  funext U
  unfold chapter Jets.stanza; dsimp only; rw [Stamp.tells]; simp_rw [Stamp.beat_list,Syllable.eval,Stamp.tells,List.prod_map_mul]; ring

namespace Stock
omit [Fintype V] in
lemma thin_of_quote {B : Brush V G n} {f : ℕ → ℝ} (P : BudgetPoint)
    (h : Ac.Hit (fun i => (B.u i).zone) P.B f (Rates.inner P+7) (Rates.raw P)) :
    Thin (fun i => (B.u i).zone) P.B (Rates.inner P+6) f (Rates.raw P) := by
  have ht := Rates.cabin P; have hi := Rates.still_thin P; have he := Rates.window_pos P
  refine ⟨by linarith [Rates.inner_pos P], (Rates.raw_pos _).le,
    (Absolute.burden (fun i => show (B.u i).zone.Nonempty from ⟨_,(B.u i).origin⟩) h).1,
    by linarith,?_,?_⟩
  · have hh := Rates.launchable P; apply le_trans _ hh
    have hj := Rates.gate P; apply mul_le_mul_of_nonneg_left <;> linarith
  rw [show Rates.inner P+6+1=Rates.inner P+7 by ring]; exact h
end Stock


end Brush
end YM.Multi.Vacuum
