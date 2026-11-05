import YM.Next.MULTISOURCE.Tariff

/-!
# Precise producer prerequisites

`Responsive`: local estimate at adjacent scales, on *unrescaled individual
variation directions*, on the RPaper path. Think producer wishing to export
some analytic component estimates from the unmarked/singleton step to Fields.
Keeps `Z` the same response for all its uses on this list of directions. In
particular singleton directions arrive in the same presentation from reference
history (at cutoff they use the explicit commodity `birth`). Don't assert it
holds for a Paper that didn't make compatible choices. It does
**not** require the quantitative part of JMara in E as stated there: no small
aggregate/root norm input, no price bound on the simultaneously summed output
at positive radii after simultaneously evaluating multi perturbations
required here. It DOES ask for exponential support reserve and probes the
jet at every order, incl integral on all the corresponding
product terms: this uniform susceptibility estimate is *red*. Here proven
given the ordinary vacuum stability gate (Curves). Single
response and eligibility commitments on the same chosen alphabet.

`Addresses`: mild bookkeeping side and **unmarked** K exponent/top bound. Need
buy in tandem with `Makes` and all other costs. Not claiming `Makes` without
these contextual and analytic receipts would suffice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Marker Function Filter Finset MeasureTheory Source Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

def neighboring (C : Family G) (j : ℕ) := Real.exp ((C.path.levels.clock.coverSize j:ℝ)/256)

def touch (C : Family G) (d j : ℕ) := ((C.S.block j).val : ℝ)^d
lemma touch_pos (C : Family G) (d j : ℕ) : 0<touch C d j := by unfold touch; positivity

def Adjoining (C : Family G) (d j : ℕ) := ∀ N p, j<N → ∀ (V : Type) [Fintype V] [DecidableEq V] (R : Census V)
    (o : V→Site (C.side j p)), Spaced o (C.path.levels.clock.coverSize j) →
    let A := C.path.levels
    let X := C.path.rep N p j
    let Y := C.path.rep N p (j+1)
    let S := A.clock.op j p
    ∀ (v : V → C.label d) (D : Hot R → Pulse G (C.side (j+1) p)) (k : Hot R → ℝ),
      (∀ i, Credit Y.p 0 (money A (j+1)) (i.sites.image (fun j => S.ratio.embed (o j))) (D i) (k i)) →
      (∀ i,D (Hot.one R i)=Single.one C (d:=d) N (v i) (j:=j+1) (S.ratio.embed (o i)) ∧
        k (Hot.one R i)=Single.tariff C N p (j+1) (d:=d) (v i)) →
      ∃ Z, (∀ i,(touch C d j:ℂ) • Z (Hot.one _ (Hot.one R i))=Single.one C N (v i) (o i)) ∧
        ∀ q,2 ≤ (unionOfHot q).sites.card → Raw S X Y Z D (neighboring C j) (money A j) k o q

def Responsive (C : Family G) (d : ℕ) := ∀ᶠ j in atTop, Adjoining C d j

def Addresses (C : Family G) := (∀ᶠ N : ℕ in atTop, ∀ p : ℕ, Mint (C.path.rep N p N) 2
    (money C.path.levels N)) ∧ (∀ᶠ j : ℕ in atTop, ∀ N p, j≤N → Room (C.path.rep N p j))
end YM.Multi
