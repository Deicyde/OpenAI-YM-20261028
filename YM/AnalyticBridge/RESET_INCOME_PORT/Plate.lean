import YM.Push.CUTOFF_PROJECTORS.Along
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Service

set_option warningAsError false

/-!
# Exact integrals used to prepare scalar-income tests

Units: `outside` is a NATURAL LOG (extensive), `cost` is the remaining
log cost of a matched allocation Store/choice. `value` still uses the
literal potentially SIGNED sleeves, not a positive majorant and not a
formal power series. No log of it is taken here. We use one forest, one
flat cost with a fixed choice `tag`, one book, one radius and the exact
window prescription of `SectorChange.committed`. There is never a log of
a determinant of a mismatched entry on the RHS of the pricing identity.
Nothing is asserted about thermodynamic cost, field analyticity, a
subsequent cluster expansion or output representations here. The legal
hypotheses are produced from the Directed/Ringing/Cosmos inputs below.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange
open Input RG.Supply RG.Shoot Pressure.Testing
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}

/-- References for *one* actual sector formula, held even across the two
probes (including the same flat price in both readings). -/
structure Plate (G : Gauge) {c f : Side} (S : StepData c f) where
  x : ℝ
  w : ℝ
  tube : Tube G S
  forest : Forest S.ratio
  book : Allocation G S x w
  chart : ChartRatio G
  chip : Chi
  point : BudgetPoint  -- output point, for conversion sieve↔banker
  d : ℝ
  tag : S.Choices   -- the flat price

variable {S : StepData c f}
namespace Plate
variable (e : Plate G S) (R : Rep G f) (A : Stores S) (V : Config G c) (k : S.Choices)

abbrev Cov := fog A e.forest e.tube e.x V k
abbrev Gram := Rows.gram e.tube e.x V k (shots S e.x) A e.forest
abbrev center := meanLog A e.forest e.tube e.x V k e.chip e.d
abbrev Flat := Native.kinetic e.tube e.forest e.tag e.x
abbrev Sample := LinkArray G (Frozen A e.x e.forest) × Prices G (Active A e.x e.forest)
def law : Measure (e.Sample A) := (piHaar G (Frozen A e.x e.forest)).prod
    (Gaussian.cloud (e.Cov A V k))

def color : e.Sample A → ℝ := uncurry
    (sleeves e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip e.chart e.d e.point (e.Cov A V k) (e.center A V k))
def matched := A.flags = RG.flags (temp e.x) V

/-- In particular the incoming per-site
`Rep.v` is multiplied by INcoming volume. -/
def debit := R.v * Fintype.card (Site f) + Real.log (prefactor S G R.beta) +
    Fintype.card e.forest.Free * Real.log (spare e.chart R.beta) - (1/2) * Real.log e.Flat.det

/-- The outside factor includes the full Banker, with tail already
returned *inside* `color`. -/
def outside := Real.log (banker e.tube e.point V R.beta) + e.debit R

/-- No need to say that
`Gram * Cov - 1` is symmetric (or that a TrLog series applies). -/
def cost := -(Fintype.card (Frozen A e.x e.forest) : ℝ) * Real.log (spare e.chart R.beta) -
    (1/2) * (Real.log (e.Gram A V k).det - Real.log e.Flat.det) +
    (1/2) * Real.log (1 + (e.Gram A V k * e.Cov A V k - 1)).det

def value : ℝ := if e.matched A V then
    Real.exp (e.cost R A V k) * ∫ z, e.color R A V k z ∂(e.law A V k) else 0

def head (I : Finset (Stores S)) := ∑ A ∈ I, ∑ k, e.value R A V k

/-- Only the actual finite-volume geometry and measure hypotheses. No price
on the *size* of signed integrals! -/
structure Receipt (e : Plate G S) (R : Rep G f) : Prop where
  solvent : e.Flat.PosDef
  radius : e.point.threshold = temp e.x
  ratio : LocalRatio e.chart
  bp : 0 < R.beta
  matchPos : ∀ A V, e.matched A V → ∀ k,
    (e.Gram A V k).PosDef ∧
    Permitted e.x V k A e.forest e.book e.chart e.d R.beta (e.Cov A V k) (e.center A V k)
  licenses : ∀ A V k, Licenses e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip
      e.chart e.d (e.Cov A V k) (e.center A V k)

variable {e R A V k}
lemma outside_exp (h : e.Receipt R) (V : Config G c) :
    Real.exp (e.outside R V) = banker e.tube e.point V R.beta *
      (Real.exp (R.v * Fintype.card (Site f)) * prefactor S G R.beta *
        spare e.chart R.beta ^ Fintype.card e.forest.Free * (Real.sqrt e.Flat.det)⁻¹) := by
  have hf := h.solvent.det_pos
  have hx := spare_pos e.chart h.ratio h.bp
  have ht : 0 < banker e.tube e.point V R.beta := Real.exp_pos _
  unfold outside debit
  rw [show 1/2*Real.log e.Flat.det = Real.log (Real.sqrt e.Flat.det) by rw [Real.log_sqrt hf.le]; ring,
    Real.exp_add,Real.exp_sub,Real.exp_add,Real.exp_add, Real.exp_log ht, Real.exp_log (Real.sqrt_pos.mpr hf),
    Real.exp_log (prefactor_pos R.beta), Real.exp_nat_mul, Real.exp_log hx]
  rw [div_eq_mul_inv]



lemma wrong (he : ¬e.matched A V) (U : Config G f) (k : S.Choices) : e.book.bill A k U V = 0 :=
  not_not.mp fun hh => he (e.book.actual _ _ _ _ hh).exactFlags

/-- Licensed even with mismatched flags (zero). -/
lemma integrable_color (h : e.Receipt R) (A : Stores S) (V : Config G c) (k : S.Choices) :
    Integrable (e.color R A V k) (e.law A V k) := by
  by_cases hv : e.matched A V
  · obtain ⟨hg,hp⟩ := h.matchPos A V hv k
    exact (full_price e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip e.chart e.d e.point h.radius
      _ _ _ h.solvent hp.nativePos hg h.ratio h.bp (h.licenses A V k)).2.1
  have hz : e.color R A V k = 0 := by funext u; simp [color,sleeves,wrong hv,uncurry]
  rw [hz]; exact integrable_zero ..

lemma cut_eq (h : e.Receipt R) (A : Stores S) (V : Config G c) :
    cutEntry e.book e.forest e.tube R A V = Real.exp (e.outside R V) * ∑ k, e.value R A V k := by
  unfold cutEntry Allocation.column tagTotal
  rw [Finset.mul_sum,Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases he : e.matched A V
  · rw [value,if_pos he, outside_exp h]
    obtain ⟨hg,hp⟩ := h.matchPos A V he k
    have hh := (full_price e.tube e.x V k A R (shots S e.x) e.forest e.book e.chip e.chart e.d e.point h.radius
      _ _ _ h.solvent hp.nativePos hg h.ratio h.bp (h.licenses A V k)).2.2
    unfold law; rw [integral_prod _ (integrable_color h A V k),hh,mul_assoc]; rfl
  simp [value,he, Allocation.portion,wrong he]

lemma cut_sum (h : e.Receipt R) (I : Finset (Stores S)) (V : Config G c) :
    ∑ A ∈ I, cutEntry e.book e.forest e.tube R A V = Real.exp (e.outside R V) * e.head R V I := by
  unfold head; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun A _ => cut_eq h A V


end Plate

section live
variable {B : Sheet G} {D : Rolls B} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (b : Directed G I Z K P)

/-- Tightly bound to the committed prices. -/
def assigned (N m p : ℕ) (g a : ℕ → ℕ → ℝ)
    (F : Forest (b.a.clock.op m p).ratio) (χ : Chi)
    (u : Allocation G (b.a.clock.op m p) (b.a.clock.hatBeta m) (g (b.a.clock.J (m+1)) (b.a.clock.J m)))
    (k : (b.a.clock.op m p).Choices) : Plate G (b.a.clock.op m p) :=
  ⟨_,_,ships b N m p,F,u,Z,χ,b.a.budget m,a (b.a.clock.J (m+1)) (b.a.clock.J m) * b.a.clock.threshold (m+1), k⟩

variable {N m p : ℕ} {g a E : ℕ → ℕ → ℝ}
variable (F : Forest (b.a.clock.op m p).ratio) (χ : Chi)
    (u : Allocation G (b.a.clock.op m p) (b.a.clock.hatBeta m) (g (b.a.clock.J (m+1)) (b.a.clock.J m)))
    (k : (b.a.clock.op m p).Choices)

lemma purchased (hW : Ringing K g W) (hh : Cosmos Z K W g a E) (hm : m < N) (R : Rep G (b.a.S.side (m+1) p))
    (hl : Lives b.bake N (m+1) p R) (hb : R.beta ∈ band b.a (m+1)) :
    (assigned b N m p g a F χ u k).Receipt R := by
  let e := assigned b N m p g a F χ u k
  obtain ⟨_,hd,hr,hZ,hE,hJ,hP,κ,hκ,H⟩ := committed b hW hh N m p hm R hl hb
  obtain ⟨hU,hG,hQ⟩ := H u F χ
  have hp := proceeds b N m p hm
  have hy := Client.funded b hW hh N m p hm
  constructor
  · change (Native.kinetic _ F k _).PosDef
    obtain ⟨η,hη,h⟩ := Gap.stood G (b.a.clock.op m p).patch _
    rw [← Native.ground_gram _ F k _ (funds_branch hp)]
    apply Matrix.PosDef.submatrix ?_ (Native.lineEquiv ..).injective
    exact Gap.solvent _ _ _ F _ 1 k _ hη (h _ _ rfl hy.2.1 hy.2.2 hp _ _ F k)
  · rfl
  · exact b.ratio
  · exact hP
  · intro A V hv k
    obtain ⟨h',h'',-⟩ := hG A k V
    obtain ⟨hg,hA,-⟩ := h'' hv
    refine ⟨hA,⟨hg,hP,(meanLog_cont _ _ _ _ _ _ _ _ hp hd hr).measurable,fun u hu hf i => ?_,b.ratio,hd,hZ⟩⟩
    obtain ⟨a,ha,hx,-,hc,-⟩ := h' u hu hf i.val (Or.inl i.property)
    exact ⟨a,ha,hx,hc⟩
  intro A V k; exact (hG A k V).2.2
end live
end YM.AnalyticBridge.ResetIncome
