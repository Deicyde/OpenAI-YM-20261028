import YM.Axis.Word

/-!
# Cross measures via polarization. Use in bands/open gap claims.

Evaluate only WHEN INTEGRABLE against all ν; no total var assertion for
noncompact. These sets include any bounded energy mask. Relative correlation
reading is physical N/R matter port, not arbitrary cross coefficient conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Row
open Function Set Filter MeasureTheory Measure Spectral Analysis Complex Boundary Probe OS Word
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis} (V : Chamber S a)

def phase (i : Fin 4) : ℂ := I^i.val

def combo (A B : Weight L) i := A+(phase i • B)

def fits (A B : Weight L) (w : E4 → ℂ) :=
    ∀ i, Integrable w (ν V (combo A B i))

def cross (A B : Weight L) (w : E4 → ℂ) := (4:ℂ)⁻¹ * ∑ i : Fin 4,
    star (phase i) * (∫ p, w p ∂(ν V (combo A B i)))

theorem identity {H : Hilbert} (C : H.Op) (a b : H) :
    (4:ℂ)⁻¹ * ∑ i : Fin 4, star (phase i) * inner ℂ (a+phase i • b) (C (a+phase i • b))=inner ℂ a (C b) := by
  rw [Fin.sum_univ_four]
  simp only [phase,map_add, map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right]
  norm_num [pow_succ]
  ring_nf
  simp [Complex.I_sq]; ring

lemma meets_air (A B : Weight L) (t : ℝ≥0) (h : Lowered a A t) (ht : Lowered a B t) (i) : Lowered a (combo A B i) t := by
  classical
  intro k hk
  cases Finset.mem_union.mp (Finsupp.support_add hk) with
  | inl hh => exact h _ hh
  | inr hz => exact ht _ (Finsupp.support_smul hz) -- signature

lemma route (A B : Weight L) (r : ℝ) (i) : root V (combo A B i) r = root V A r + phase i • root V B r := by
  change Finsupp.linearCombination ℂ (fun w => bud V w r) (_+_ • _) = _; rw [map_add,map_smul]; rfl

variable (y : E4) (u : ℝ≥0)

/-- includes t+t undamping. E-i equals y time for spectral model; set
x,y a=... etc upstream reads. -/
def pack (a : Axis) (z : ℂ) (p : E4) : ℂ :=
    Semigroup.descent a ((u+u:ℝ≥0):ℝ) p • Paley.weight (fun p => p a) (fun p => plane p y) z p

theorem reads (z : ℂ) (he : z ∈ Paley.high) (A : Weight L) (hp : Lowered a A u) : Integrable
    (pack y u a z) (ν V A) ∧ V.flow.J y (root V A u) (root V A u) z = ∫ p, pack y u a z p ∂ν V A := by
  let x := root V A u
  let B := Paley.weight (fun p : E4 => p a) (fun p => plane p y) z
  let μ := Semigroup.transform a ((u+u:ℝ≥0):ℝ) (ν V A)
  have hb : Integrable B μ := by
    rw [show μ= _ from band V _ _ hp]
    exact Paley.ok _ _ (by fun_prop) (V.flow.bright _) _ (by unfold plane;fun_prop) (fun i => plane_norm _ y) z he
  constructor
  · exact (integrable_withDensity_iff_integrable_smul (Semigroup.measurable a _)).mp hb
  rw [V.flow.heat _ _ he, ← band V _ _ hp]
  exact integral_withDensity_eq_integral_smul (Semigroup.measurable a _) B

theorem reply (z : ℂ) (hz : z∈ Paley.high) (A B : Weight L) (hA : Lowered a A u) (hB : Lowered a B u) :
    fits V A B (pack y u a z) ∧ V.flow.J y (root V A u) (root V B u) z = cross V A B (pack y u a z) := by
  let Z : ℂ := z
  have hx i := reads V y u z hz (combo A B i) (meets_air A B u hA hB i)
  refine ⟨fun i => (hx i).1,?_⟩
  unfold cross; simp_rw [← (hx _).2,route]
  let W := V.flow
  let C := (W.unit.translation y).comp ((W.edge Z.re).comp (W.E Z.im.toNNReal))
  exact (identity (H := V.GNS.H) C _ _).symm
end YM.Row
