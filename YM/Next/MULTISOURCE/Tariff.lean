import YM.Next.MULTISOURCE.Birth
import YM.Next.MULTISOURCE.Off
import YM.Next.MULTISOURCE.Single
import YM.Next.MULTISOURCE.Stencil
import YM.Work.G08


/-!
# Canonical loads. Cost from `Makes`, no multi-perturbation invoice yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi

open RG Wilson Lattice Function Filter Finset Source Labels AxisShift Couples MeasureTheory Maquette
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

lemma potential_hat (A : Levels G) (i : ℕ) : 0 < A.clock.hatCoupling i ∧ A.clock.hatCoupling i ≤ (A.budget i).threshold := by
  have he := Real.sqrt_pos.mpr (lt_trans zero_lt_one (A.fits.delayed i)); have hp := inv_pos.mpr he
  refine ⟨hp,?_⟩
  change _ ≤ A.clock.hatCoupling i*Real.exp _; exact le_mul_of_one_le_right hp.le (Real.one_le_exp (sq_nonneg _))

def money (A : Levels G) (i : ℕ) := Real.sqrt (A.clock.forcedAllowance i)
lemma money_accepted (A : Levels G) (i : ℕ) : 0 < money A i ∧ money A i ≤ 1 := by
  refine ⟨Real.sqrt_pos.mpr (Real.exp_pos _),Real.sqrt_le_one.mpr ?_⟩
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))

namespace Single
variable (C : Family G) {d N p j : ℕ}

def coeff (N p j : ℕ) (v : C.label d) := (C.factory d N p).entries j ((C.factory d N p).terminal.symm v)

def cache (v : C.label d) (o : Site (C.side N p)) : Vessel G (C.side N p) where
  siteSet := (C.localSection d).footprint o
  tall := (coeff C N p N v).x 0
  seen := (C.localSection d).places ((C.labels.level d).scaled (C.path.levels.budget N).threshold⁻¹
    ((C.labels.level d).core (coeff C N p N v).x)) o

/-- Only at N use our explicit birth (may differ internally from factory
    tangent at N; local block hypothesis needs to respect this choice). -/
def one (N : ℕ) (v : C.label d) (o : Site (C.side j p)) : Pulse G (C.side j p) :=
    if h : j=N then h ▸ ((cache C v (p:=p) (N:=N) (h ▸ o)).birth (C.path.rep N p N))
    else carry o (BranchOne.center (coeff C N p j v) (C.localSection d) 0 (C.path.rep N p j))

def excess (d j : ℕ) : ℝ := (C.path.levels.clock.hatCoupling j)⁻¹ ^ maxgrade (C.labels.level d)

def kitty (d : ℕ) : ℝ := liftFee (C.localSection d).stencil.card * upper (C.localSection d)

def ankle (N p j : ℕ) (v : C.label d) : ℝ := upper (C.localSection d)*excess C d j *
    (C.labels.level d).coeffSize ((coeff C N p j v).x)

def stipend (j : ℕ) := Real.exp ((C.path.levels.params j).supportExponent+2)

/-- convenient reference tariff supplied to response estimate, not charging site/copy count -/
def tariff (N p j : ℕ) (v : C.label d) : ℝ :=
    let c := C.path.levels
    (1+(C.labels.level d).coeffSize ((coeff C N p j v).x)) * (c.params j).columns *
      stipend C j * excess C d j * (2 + kitty C d)

lemma excess_one (d j : ℕ) : 1 ≤ excess C d j := one_le_pow₀ ((one_le_inv₀ (potential_hat ..).1).mpr
    (((potential_hat ..).2).trans (C.path.levels.budget j).threshold_le))

lemma stipend_hi (j : ℕ) : 1 ≤ stipend C j := Real.one_le_exp (add_nonneg (C.path.levels.params j).price_pos.le (by norm_num))
lemma kitty_pos (d) : 0 < kitty C d := mul_pos (lift_pos _) (zero_lt_one.trans_le (purposes (C.localSection d) 0).1)

-- Applied to footprint even if base is about a copy root
lemma flows (v : C.label d) (N) (o : Site (C.side j p)) (he : room (C.localSection d) ≤ C.path.levels.clock.coverSize j) :
    let Y := (C.localSection d).footprint o
    let m := C.path.levels.budget j
    let x := (C.labels.level d).coeffSize (coeff C N p j v).x
    let k := (C.path.levels.params j).columns
    2*(stipend C j*x*k) ≤ tariff C N p j v ∧
    burn m 2 Y ≤ stipend C j ∧ liftFee (C.localSection d).stencil.card * (stipend C j*ankle C N p j v) ≤
      tariff C N p j v := by
  intro Y m x k
  have hu : 1 ≤ k := (C.path.levels.params _).columns_ge
  have hk := zero_le_one.trans hu
  have hp : 0 ≤ x := Work.G08.size_nonneg ..
  have hb := stipend_hi C j
  have hg := zero_le_one.trans hb
  have hv := excess_one C d j
  have hK : 0 ≤ kitty C d := (kitty_pos C d).le
  refine ⟨?_, ?_, ?_⟩
  · unfold tariff; dsimp only
    calc
      _ = (x * k * stipend C j * 1 * 2) := by ring
      _ ≤ (1+x)*k*stipend C j * excess C d j * (2+kitty C d) := by
        gcongr
        · simp
        linarith only [hK]
  · have h := hoist (C.localSection d) o _ he
    apply Real.exp_monotone
    have hf : 0 ≤ (m.supportExponent+2) := add_nonneg m.exponent_pos.le (by norm_num)
    exact mul_le_of_le_one_right hf (by exact_mod_cast (show coverNumber m.B _ ≤ 1 from h))
  · have hs : 0 ≤ liftFee (C.localSection d).stencil.card := (lift_pos _).le
    calc
      _ = x * 1 * stipend C j * excess C d j * kitty C d := by unfold ankle x kitty; ring
      _ ≤ (1+x)*k*stipend C j * excess C d j * (2+kitty C d) := by
        gcongr
        · simp
        simp
end Single
end YM.Multi
