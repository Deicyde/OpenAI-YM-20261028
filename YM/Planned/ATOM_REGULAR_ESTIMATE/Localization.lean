import YM.Extra.SOURCE_HISTORIES.LocalDebt
import YM.Planned.ATOM_REGULAR_ESTIMATE.Geometry
import YM.Planned.ATOM_REGULAR_ESTIMATE.Tests
import YM.Push.LOCAL_SPLITTING.Recovery


/-!
A remaining physical input to this proof, stated *below* the one-column
estimate. An exact localization of the unmarked block kernel as observed on
one declared fine support `X` (including its mask). Can be signed-sector
kernel data. `StepData.push` in the hypothesis is essential. No
approximate or sectorwise-renormalized kernel.

Think the separate principal bulk (possibly zero, as everywhere in these
dictionaries), a series of partner terms (log-expansion, companions etc.),
and measures at each forced output address read *inside* the gas. We don't
need a particular way of computing this expansion -- we spell out what is
needed on such a choice. These could be very hard or even false on an
insufficiently prepared history. In particular we do not derive the supplies
here from unmarked sums on a generic `Conv` or from analyticity of a tested
(no-flag) stationary action.

Estimates asked for are *on those kernel measures*: integral bounds on the
densities, their finite joint scores and motions of the sampled argument,
and summability of these BEFORE evaluating ANY regular atom (see `Sample.Built`,
`Coasting`, `Shoots`, `Judged`). These and the qualitative `Covered` clauses
provide domination for the calculus. They do not hypothesize estimates on
field responses, label jets at identity, projected coordinates, Taylor errors
of the branch after labelling etc. In particular the powers tested on leading
velocities are not operator estimates on projection-vanishing fields: even
sampling deterministically at such an argument gives no such estimate without
testing the actual higher jets and gauge-jet cancellations on f (contrast
running with nonvanishing Pi). They represent real physical hypotheses, notably
the filtered `S b`-type sensitivity PLUS paying its errors and fluctuations for
the principal kernel. Absolute controls apply to full support halo/covers and
indicators. Germs for `Measures` interpreted also at equality.

We use weak observables (`Feed`, functional form) for expressing
locality: need pre-mask global Borel/local, gauge-invariant extensions for
weak coefficients read at the indicated tests. This imposes NO derivative
price on f's integral. It works e.g. with measures in varying frames and
frozen steps. `positions` inclusion tests declarative stencil/support
(incl final flag reads); as elsewhere in B70 this is denotational, not
an algorithm-independence certificate for building the expansion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Lattice Wilson RG MeasureTheory Push.Local Next.Foundations Extra.Histories
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {m n : Side} {G : Gauge} {d : ℕ}

/-- Guard a forced output using this actual alphabet and projected input
reads (no relocation). -/
structure PackedKernel (S : Ratio m n) (X : Support n) (R : Rep G m) (i : ℕ) where
  sample : Sample G m n

namespace PackedKernel
-- extended samples on bad region, mask input f (not smooth there).
variable {S : Ratio m n} {X : Support n} {R : Rep G m} {i : ℕ}
variable (L : PackedKernel S X R i)
/-- Realized with inactive kernels zero-padded. This guard must not
change the claimed measure identity when supplied in an expansion. -/
def active (V : Config G m) : Prop :=
  (R.activities.forced i).eligible R.p.threshold V ∧ positions S X ⊆ (R.activities.forced i).support

def collect (B : BudgetPoint) (f : Config G n → ℂ) (V : Config G m) :=
  if PackedKernel.active (R:=R) (i:=i) (S:=S) (X:=X) V then
    ∫ z, L.sample.density z V * masked B.threshold X f (L.sample.link z V) ∂L.sample.μ
  else 0

structure Printed (B : BudgetPoint) (o : Site n) : Prop where
  link (V : Config G m) : active (R:=R) (i:=i) (S:=S) (X:=X) V → Measurable fun z => L.sample.link z V
  reads (f) : Permitted B o X f → UsesFinal R.p.threshold (R.activities.forced i).support (L.collect B f)
  borel (f) : Permitted B o X f → Measurable (L.collect B f)
  sym (f) : Permitted B o X f → GaugeInvariant (L.collect B f)

structure Prices (c : ℝ) : Prop where
  earn (V : Config G m) : active (R:=R) (i:=i) (S:=S) (X:=X) V →
    Integrable (fun z => L.sample.density z V) L.sample.μ ∧ (∫ z, ‖L.sample.density z V‖ ∂L.sample.μ) ≤ c


variable {L} {F : Config G n → ℂ} {B : BudgetPoint}





end PackedKernel

/-- Weak localized expansion on THESE measures (multiplication by `L^d`
not included yet). -/
structure Census (S : StepData m n) (B : BudgetPoint) (X : Support n) (R : Rep G m) where
  shape : ℕ → Support m
  gain : ℕ → Feed G m n
  fare : (i : ℕ) → PackedKernel S.ratio X R i

namespace Census
variable {S : StepData m n} {X : Support n} {Y : Rep G n} {R : Rep G m}

/-- No neighborhood price in this clause. Test the actual push distribution
at every coarse field. Inactive incidences and masks and vacuum partner
predicates/profiles must be restored in SAME history; addresses `Y` not
padded here. No claim of existence of these localized measures under just
`Selected`. -/
structure Calls (D : Census S Y.p X R) (o : Site n) : Prop where
  keeps i : positions S.ratio X ⊆ D.shape i
  bulk i : Shelled (D.gain i) Y.p o X (D.shape i)
  packet i : (D.fare i).Printed Y.p o
  actual (f : Config G n → ℂ) (h : Permitted Y.p o X f) (U : Config G m) :
    let A := fun i => masked R.p.threshold (D.shape i) (D.gain i f) U
    let F := fun i => gasMark R.p R.activities U i (fun j => (D.fare j).collect Y.p f)
    -- require no rearrangement into a junk tsum even in this test
    (Summable (fun i => ‖A i‖) ∧ Summable (fun i => ‖F i‖)) ∧
      S.push Y.beta (salary Y X f) U = (R.eval U : ℂ) * (∑' i, A i) +
        (Real.exp (R.exponent U):ℂ) * ∑' i, F i

/-- Loan ε in the delayed-cost, with post-L exponent e. Charge for counting
attachments, differentiated weights using multiple integrals, etc. can use
also a share of the pre-L *input* exponential. E.g. do **not** ask for
only polynomial costs in unbounded s_X when counting all overlaps.
Absorb both parts later on the rest of this flight. -/
def loss (B : BudgetPoint) (X : Support n) (δ : ℝ) (e : ℕ) :=
    Real.exp (B.supportExponent/4* coverNumber B.B X) * (δ * (((coverNumber B.B X):ℝ)+1)^e)

/-- Extra actual measure tickets. `Income` here is requested NOT on
insertions after integrating/moving masks, but densities and their weight-times-
velocity moments in the unmarked expansion. In bulk, price relative to halo,
allowing for every overlap needed past it. δ (tail on costs with unmarked
partners) & ε (into pre-stage principal cost C, e.g. higher velocities on
large supports) are funded jointly with post-L powers `e`. `v` is
sqrt of OUTGOING forced allowance in the application.
-/
structure Covers (D : Census S Y.p X R) (o : Site n) (d e r : ℕ) (C ε δ v : ℝ) : Prop where
  pays : D.Calls o
  rim : D.shape 0 ⊆ skirt R.p r S.ratio X
  -- all of these before numerical testing by any insertion
  cost : let Y' := D.shape 0
         let x := S.ratio.parent o
         let w := C+loss Y.p X ε e
         let L := S.ratio.count
         (Small Y.p L X → Sample.Rolling (D.gain 0) Y.p R.p o x X Y' w d L) ∧
           (¬ Small Y.p L X → Sample.Eased (D.gain 0) Y.p R.p o x X Y' w)
  receive : ∃ h k : ℕ → ℝ,
    (∀ i, 0 ≤ h i) ∧ (∀ i, 0 ≤ k i) ∧
      (SumBudget (fun i => relative R.p (skirt R.p r S.ratio X) (D.shape (i+1)) (h i)) (loss Y.p X δ e)) ∧
      (SumBudget (fun i => relative R.p (skirt R.p r S.ratio X) (Push.Local.patch R.activities i) (k i)) (v * loss Y.p X δ e)) ∧
      ∀ i, Sample.Eased (D.gain (i+1)) Y.p R.p o (S.ratio.parent o) X (D.shape (i+1)) (h i) ∧ (D.fare i).Prices (k i)

end Census
end YM.Planned.AtomRegular
