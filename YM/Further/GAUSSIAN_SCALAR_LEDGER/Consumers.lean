import YM.Further.GAUSSIAN_SCALAR_LEDGER.Local
import YM.SectorNext.VACUUM_NORMALIZATION.Clinic


set_option warningAsError false

/-!
# Pay at the downstream interfaces

Counter adapter still needs the real addresses and term identities
AND budgets at V. It accepts them on the resulting integrands,
not free-series coefficients. Reaching `Issues` from those inputs
does not pay `Rates.kin` or selected history, nor say the RAdvances
invoice is affordable. The Selected track separately prices at an
actual adjacent pair in any such history, retaining its clock etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar.Use

open Matrix Function Filter Precision SectorNext.Vacuum Lattice
open MeasureTheory Wilson RG Tree Pressure Push.SectorMeasure Next.Fluctuations.Sector
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge}
section service
variable {c f : Side} {S : StepData c f} {O : ChartRatio G} {F : Forest S.ratio} {x W : ℝ}
    {ι : Type*} [Fintype ι]
    {R : Rep G f} {B0 : Wall (Key F G)} {G0 : Config G c→ℝ} {d : Allocation G S x W}
    {v : Stores S → S.Choices → Config G c → Fiber F O ι}
local notation "Dkt" => Finset ℕ × Finset ℕ

def takeAway {ι : Type*} [Fintype ι] (P : Fiber F O ι) (Y : Frozen P.H G)
    (f : VV (Bits G P.H) → ℝ) := ∫ z, f z ∂fieldLaw (P.C Y)

/-- Hypotheses if handing off to first-integrated-gas Counter. The
servable primitive integrates REAL Z&Y here. `note`, `compiled` below
read Q(activity addresses) in the same order as Counter; `Fragments`
is still a genuinely physical hypothesis about that organization of the
cut sector.
-/
structure Fragments (R : Rep G f) (B0 : Wall (Key F G)) (G0 : Config G c→ℝ) (d : Allocation G S x W)
    (v : Stores S → S.Choices → Config G c → Fiber F O ι)
    (X : ℕ→Support c) (b : BudgetPoint) (E : ℕ→Config G c→ℝ) (m : Activities G c) where
  content : (P : Stores S) → (k : S.Choices) → (V : Config G c) → Dkt → (Y : Frozen (v P k V).H G) → VV (Bits G (v P k V).H) → ℝ
  money P k V i Y : Integrable (content P k V i Y) (fieldLaw ((v P k V).C Y))
  splits P k V Y z : HasSum (fun i => content P k V i Y z)
      (Real.exp ((v P k V).chargeOut B0 R.beta Y) *
        (v P k V).visit d P k V (G0 V) R.beta (pressureRows k V R) Y z)
  scores P k V Y : Summable fun i => takeAway (v P k V) Y (fun z => ‖content P k V i Y z‖)
  payable P k V : Summable fun i => ∫ Y, ‖takeAway (v P k V) Y (content P k V i Y)‖ ∂bins (v P k V).H G
  awake P k V i : Integrable (fun Y => takeAway (v P k V) Y (content P k V i Y)) (bins (v P k V).H G)
  compiled P Q V :
      ∑ a, ∑ k, tagRef k * (∫ Y,takeAway (v a k V) Y (content a k V (Q,P) Y) ∂bins (v a k V).H G) =
        m.gasOccurrence b Q V * ReLog.note X (ReLog.herald X b E V) (Finset.univ \ ReLog.pad m Q) P

variable {X : ℕ → Support c} {b : BudgetPoint} {E : ℕ→Config G c→ℝ} {m : Activities G c}
  (H : Fragments R B0 G0 d v X b E m)





include H


end service

/-- Take the priced scanner on this fitted calendar pair (conditional,
recovers its prices on this output and input trajectory using the same
history). Expose local error qualification at adjacent station, explicitly
separate from `Kin.Planned`. -/
theorem installed (A : History G) (h : A.Selected) (N p m : ℕ) (hm : m<N) (O : ChartRatio G) (hO : LocalRatio O)
    (q : Expense) {n : Side} (r : ℝ) (hp : q.low ≤ q.high) (ht : Timing q r) {ι : Type*} [Fintype ι] (x W : ℝ) :
    let S := A.levels.clock.op m p
    let R := A.rep N p (m+1)
    ∀ (F : Forest S.ratio) (B0 : Wall (Key F G)) (Z : Lens (Key F G)) (G0 : Config G _ → ℝ)
      (l : Key F G → Site n) (d : Allocation G S x W) (w : Stores S → S.Choices → Config G _ → Fiber F O ι),
    RawPrice q l B0 → (∀ P k V Y, RawPrice q l ((w P k V).sigma Y)) → Z.Outside l r →
    (∀ P k V, Opened O (w P k V).veil d P k V) →
    let u := fun P k V => (w P k V).screen Z
    let I := liftedTally R B0 G0 d u
    let B := commonBill F O B0 R.beta
    (∀ V, 0 < I V ∧ (A.rep N p m).eval V = Real.exp (R.scalar+B)* Real.exp (-G0 V) * I V) ∧
    receipt A N p m = B-G0 1 + Real.log (I 1) ∧
    ∀ P k V Y,
      (u P k V).chargeOut B0 R.beta Y = -∑ _∈(u P k V).H,Real.log (gaussLink O R.beta) +
        ∑ i, ((u P k V).nearby q Z B0 Y i + (u P k V).trailPrice Z B0 Y i) ∧
      ∀ i, |(u P k V).nearby q Z B0 Y i| ≤ Panel.amount q.low q.high ∧
        |(u P k V).trailPrice Z B0 Y i| ≤ q.fog r := by
  intro S R F B0 Z G0 l d v hM hw hr hu u I B
  have ht := activeScanner Z B0 q d v hp hM hw ht hr hu
  have hl := (A.levels.blocks m p).branches
  have he := (h.represents N p (m+1) hm).good
  have hy : 0<R.beta := beta_positive A h N p (m+1) hm
  have hE : (A.rep N p m).eval=S.push R.beta R.eval := (h.steps N p m hm).1
  have hf := (records R B0 G0 d u hO ht hl he hy (A.rep N p m) (h.represents N p m hm.le).good hE).2.1
  refine ⟨fun V => ?_, ?_, fun P k V Y => ?_⟩
  · rw [hE]; exact ⟨(logarithms R B0 G0 d u hO ht hl he hy
      (fun U => (strictly A h N p (m+1) hm U).le) V).1,(collects R B0 G0 d u hO ht hl he hy V).2⟩
  · rw [← spent A N p h m hm]; exact hf
  exact Fiber.in_book (u P k V) q Z B0 hp (hw P k V) hM hr ‹Timing q r› (fun Y => rfl) Y _
end YM.Further.GaussianScalar.Use
