import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-!
# Which way do the normalizers go? Multiple actual depths

Works at any interval along a run, or on a single new step with the
stated positivity (e.g. can be asked as part of retain, or recovered
while actually shooting). No source-specific denominators. Scalars at
adjacent scales don't *both* pay for each intermediate depth: the
interacting stripped partition factors form a telescoping ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Shoot Wilson Lattice MeasureTheory Filter
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {c f n : Side}

/-- Actual field-independent factor accumulated in this pair. -/
def jump (E : Rep G c) (R : Rep G f) := E.scalar-R.scalar

/-- e.g., facing E eq. ledg3: the *only* multiplicative scalar the new
representation has (over e^{old×#fine sites}) is the interacting integral
below, evaluated at flat V. This already includes ALL tags, all K/E,
cutoffs and per-link normalization. Works even prior to establishing signs
of represented inputs if a transfer to Lawful output is proved. -/
theorem reveal (S : StepData c f) (R : Rep G f) (E : Rep G c) {σ C Λ δ w : ℝ}
    (hE : E.Lawful σ C Λ δ w) (h : E.eval = S.push R.beta R.eval) :
    S.push R.beta (stripped R) 1 = Real.exp (jump E R) := by
  have he := flat_density E hE; rw [h] at he
  have hp : (fun U => S.density R.beta U (1:Config G c) • stripped R U) =
      fun U => Real.exp (-R.scalar)*(S.density R.beta U 1 • R.eval U) := by
    funext U; simp only [smul_eq_mul,stripped]; ring
  rw [StepData.push,hp,integral_const_mul]
  rw [StepData.push] at he; rw [he,← Real.exp_add, jump]; congr 1; ring

/-- Unique readout, per-site (v is *not* a free knob once an
interacting integral and compatible representation is handed off). This
equality determines v; no corresponding uniqueness of kinetic term
claimed. -/
theorem update (S : StepData c f) (R : Rep G f) (E : Rep G c) {σ C Λ δ w : ℝ}
    (hE : E.Lawful σ C Λ δ w) (h : E.eval = S.push R.beta R.eval) :
    E.v = (S.patch.L.val:ℝ)^4 * R.v + Real.log (S.push R.beta (stripped R) 1) / sites c := by
  rw [reveal S R E hE h,Real.log_exp]
  have hp := site_pos c
  unfold jump Rep.scalar; change _ = _+(E.v*sites c-R.v*sites f)/_
  rw [sites_ratio S]; field_simp; ring







-- Includes signed, no hpos argument; cooled may then be a *signed*
-- density or junk via division by zero.








variable (A : History G) (N p : ℕ)

def burn (i : ℕ) := jump (A.rep N p i) (A.rep N p (i+1))
def receipt (i : ℕ) :=
    Real.log ((A.levels.clock.op i p).push (A.β N p (i+1)) (stripped (A.rep N p (i+1))) 1)





variable (h : A.Selected)
include h

lemma spent (m : ℕ) (hm : m<N) : burn A N p m = receipt A N p m := by
  rw [receipt,reveal _ _ _ (h.represents _ _ _ hm.le).good (h.steps N p m hm).1,Real.log_exp]; rfl

















end YM.SectorNext.Vacuum
