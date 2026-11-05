import YM.WilsonBulk.Heat.Mirror

/-!
# Connected Wick output and denominator before log

Exact finite e, exact finite volume. Sending to dressed `moment`
uses the unshifted WICK convention (evaluate proxy polynomial at `mean`
after dressing). Covariance can include or ignore selected spectator variables,
as caller prescribes. We also exhibit log output for the normalized Markov
factor: `ratio numerator/denominator` with denominator of the FULL unmarked
series (`Woven` output), not just a leading Gaussian. Mark theory will use it
with position placeholders. This is not claiming bounds for volume-growing
forced-loop factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Finset
open MvPolynomial (X C pderiv)
open scoped Topology Classical ENNReal BigOperators
variable {α : Type} [Fintype α] {I J : Record α} (G : Page α 2)

abbrev Tape (α : Type) := PowerSeries (Formula α)
def volumeTape (I : Record α) : Tape α := PowerSeries.mk fun i=>capsule i (I i)
lemma tape_free (hi : Free I) : PowerSeries.constantCoeff (volumeTape I)=0 := by simp [volumeTape,capsule,hi _]
def reading (z : Formula α) := parallel (reader z).toLinearMap
lemma read_vat (x : Formula α) (I : Record α) (e : ℕ) : PowerSeries.coeff e (reading x (vat G I))=Polynomial.eval x (magnitude G I e) := by rw [reading,coeff_parallel,vat,PowerSeries.coeff_mk]; exact reader_actual _ _
omit [Fintype α] in
lemma EvalTime (f : ℕ→ Formula α) (z : Formula α) (e : ℕ) : Polynomial.eval z (∑ x∈spend e, Polynomial.monomial x (f x)) = ∑ t∈spend e,f t*z^t := by
  simp [Polynomial.eval_finsetSum]
lemma turning_off (h : FrameBound I) (hf : Free I) : reading 0 (vat G I)=volumeTape I := by
  ext1 e; rw [read_vat, volumeTape, PowerSeries.coeff_mk]
  rw [← Polynomial.coeff_zero_eq_eval_zero,tick G h hf e 0]; simp [capsule]
lemma turning_on (I : Record α) : reading 1 (vat G I)= volumeTape (receive G I false) := by
  ext1 e; rw [read_vat, volumeTape, PowerSeries.coeff_mk]; unfold magnitude; rw [EvalTime]; simp_rw [one_pow,mul_one]; unfold capsule receive; simp_rw [script_sum]; exact sum_comm

-- independent Wick density before conditional denominator. `G` has ZERO rows for coordinates
-- NOT integrated. No leading vacuum scalar: integration relative to completed square
-- already (and subsequent substitition to mean carried separately).
def moment (G : Page α 2) (I : Record α) := parallel (wick G) (tide (volumeTape I))
def momentRelative (J I : Record α) := quotient (moment G J) (moment G I)
lemma moment_flat (I : Record α) : PowerSeries.constantCoeff (moment G I)=1 := by
  unfold moment; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_parallel,PowerSeries.coeff_zero_eq_constantCoeff_apply,tide_const]; exact wick_one _
lemma moment_unit (I : Record α) : IsUnit (moment G I) := unit_const_one (moment_flat G I)
lemma pays_relative (I J : Record α) : momentRelative G J I*moment G I=moment G J := quotient_pay (moment_unit G I)

lemma conforms (hi : Based I) (hb : FrameBound I) (hf : Free I) (e : ℕ) : Wields G (PowerSeries.coeff e (tide (volumeTape I))) (PowerSeries.coeff e (tide (vat G I))) := by
  refine ⟨?_, gaussian_pde G hi hf hb e⟩
  rw [← turning_off G hb hf]; unfold reading; rw [← tide_map, coeff_parallel]
  exact (Polynomial.coeff_zero_eq_eval_zero _).trans (reader_actual _ 0).symm

lemma warm (hi : Based I) (hb : FrameBound I) (hf : Free I) : tide (vat G I)=parallel (timer G) (tide (volumeTape I)) := by
  ext1 n; rw [coeff_parallel,timer_ray]; exact (conforms G hi hb hf n).is G
lemma connected (hi : Based I) (hb : FrameBound I) (hf : Free I) : tide (volumeTape (receive G I false)) = moment G I := by
  rw [← turning_on,reading, ← tide_map, warm G hi hb hf]
  ext1 n; unfold moment; simp only [coeff_parallel]; rfl
/-- Uniqueness of full log of unnormalized moment with prescribed zeroth order. -/
lemma isLog {L : Tape α} (hi : Based I) (hb : FrameBound I) (hf : Free I) :
    (tide L = moment G I ∧ PowerSeries.constantCoeff L=0) ↔ L=volumeTape (receive G I false) :=
  ⟨fun ⟨l,r⟩ => tide_injective r (tape_free (siteLimits G false hb hf hi).2.2) (l.trans (connected G hi hb hf).symm), fun h=> h ▸ ⟨connected G hi hb hf,tape_free (siteLimits G false hb hf hi).2.2⟩⟩
lemma loggedRelative (hi : Based I) (hb : FrameBound I) (hf : Free I) (hj : Based J) (hb' : FrameBound J) (hf' : Free J) :
    momentRelative G J I=tide (volumeTape (receive G J false)-volumeTape (receive G I false)) := by
  unfold momentRelative; rw [← connected G hi hb hf,← connected G hj hb' hf']; exact quotient_terms (tape_free (siteLimits G false hb' hf' hj).2.2) (tape_free (siteLimits G false hb hf hi).2.2)
end YM.WilsonBulk.Sheet
