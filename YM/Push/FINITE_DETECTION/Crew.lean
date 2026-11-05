import YM.Push.FINITE_DETECTION.Roots
import YM.Push.FINITE_DETECTION.Spin


/-! An actual unrooted `Cells.Columns` via the free calculation, with a
whole comparison/detection scheme using all its rows at common pair positions.
Selector can use the original graded frame: real combinations and unit
require no later dimension guess. `GridScheme` here is a sufficient
optional port for both the detector AND further `RankWidths` work at those
exact columns. No claim its `PaidGrid` budgets have already been realized. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection
open Function Set Filter Extraction Next.Extract Dash Cells Lattice
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G)

abbrev H := Free.Hyper.comparatorSpin C.labels

lemma basis_real (d : ℕ) : ∃ n, ∃ β : Module.Basis (Fin (n+1)) ℂ (Model C d), β 0 = (Standard C).unit d ∧
    ∀ i, ∃ j : Coord C d, β i = (Standard C).project d (Pi.single j 1) := by
  classical
  let T := Standard C
  let E (j : Coord C d) := T.project d (Pi.single j 1)
  have he : T.unit d = E 0 := by change T.project d (((1:ℝ) : ℂ)^d • (Pi.single 0 (1 : ℂ) : Coord C d → ℂ)) = E 0; rw [Complex.ofReal_one,one_pow,one_smul]; rfl
  have hi : LinearIndepOn ℂ id {T.unit d} := (linearIndepOn_singleton_iff _).mpr (T.alive d (Maxwell.table_regular _))
  obtain ⟨p,hp,hU,hsp,hli⟩ := exists_linearIndepOn_id_extension hi (show {T.unit d} ⊆ range E from singleton_subset_iff.mpr ⟨0,he.symm⟩)
  have ht : ⊤ ≤ Submodule.span ℂ p := by
    intro x _
    obtain ⟨v,rfl⟩ := T.onto d x
    have hv : ∑ i, v i • E i = T.project d v := by
      simp only [E,← map_smul,← map_sum,← Pi.single_smul',smul_eq_mul,mul_one,Finset.univ_sum_single]
    rw [← hv]; exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hsp ⟨i,rfl⟩))
  let b : Module.Basis p ℂ (Model C d) := Module.Basis.mk (show LinearIndependent ℂ (Subtype.val : p → Model C d) from hli.linearIndependent_restrict) (by simpa using ht)
  haveI : Finite p := Module.Finite.finite_basis b
  let u : p := ⟨T.unit d,hU (mem_singleton _)⟩
  haveI : Nonempty p := ⟨u⟩
  letI := Fintype.ofFinite p
  let n := Fintype.card p - 1
  let f : p ≃ Fin (n+1) := (Fintype.equivFin p).trans (finCongr (by have := Fintype.card_pos (α := p); unfold n; omega))
  let w := f.trans (Equiv.swap (f u) 0)
  have ha x : b.reindex w (w x) = x.val := by simp [b]
  refine ⟨n,b.reindex w, (show w u = 0 by simp [w]) ▸ ha u, fun i => ?_⟩
  obtain ⟨x,rfl⟩ := w.surjective i; obtain ⟨j,hj⟩ := hp x.property
  exact ⟨j,(ha x).trans hj.symm⟩

structure Crew (C : Family G) (d : ℕ) where
  n : ℕ
  β : Module.Basis (Fin (n+1)) ℂ (Model C d)
  unit : β 0 = (Standard C).unit d
  single (i) : ∃ j : Coord C d, β i = (Standard C).project d (Pi.single j 1)
  target : Points 2
  generic : target ∈ YM.generic 2
  full : Injective (freeMatrix β target)

def crew (d : ℕ) : Crew C d :=
  let he := basis_real C d
  let β := he.choose_spec.choose
  let hh := generic_free β
  ⟨_,β,he.choose_spec.choose_spec.1,he.choose_spec.choose_spec.2,hh.choose,hh.choose_spec.1,hh.choose_spec.2⟩

variable {C} {d : ℕ}
namespace Crew
variable (Y : Crew C d)

abbrev Index := Fin (Y.n+1)
lemma realBasis (i) : (Standard C).conj (H C) d (Y.β i) = Y.β i := by
  obtain ⟨j,hj⟩ := Y.single i
  rw [hj,Table.conj_project]; congr 1; funext k; by_cases h : k = j
  · subst k; simp
  simp [Pi.single_eq_of_ne h]

def row (i : Y.Index) : SampleRow Y.Index := ⟨1,le_rfl,fun _ => i, Y.target,Y.generic⟩
lemma at_row (v i) : (Y.row i).tests (Standard C) Y.β v = freeMatrix Y.β Y.target v i := by
  unfold SampleRow.tests Table.useAt
  let t := (Fin.cons (α := fun _ => (Standard C).Tag) ⟨d,v⟩ (fun _ : Fin 1 => ⟨d,Y.β i⟩))
  have ht : t = fun i' : Fin 2 => ⟨d,(![v,Y.β i] : Fin 2 → Model C d) i'⟩ := by funext j; fin_cases j <;> rfl
  change ((Standard C).classMoment (Standard C) (fun j => (t j).1) Y.target fun j => (t j).2) = _
  rw [ht]; rfl

def columns (T : Table C.book) : Columns C T d where
  dim := Y.n
  H := H C
  basis := Y.β
  realBasis := Y.realBasis
  initial := Y.unit
  amount := Y.n+1
  row := row Y
  full _ _ h := Y.full (funext fun i => ((Y.at_row _ i).symm.trans (congr_fun h i)).trans (Y.at_row _ i))
end Crew

/-- Common arrays specialized to a Crew's pair template. -/
structure GridScheme (Y : Crew C d) where
  depth : Sequence
  width : Sequence
  window k : width k ≤ depth k
  scale : ℕ → ℝ
  positive k : 0 < scale k
  zoom : Tendsto scale atTop (𝓝 0)
  mark : ℕ → Fin 2 → Cover
  lift : ℕ → ℕ → ℕ → Y.Index → C.label d
  gap : ℕ → ℝ
  allowed k : 0 ≤ gap k
  small : Tendsto gap atTop (𝓝 0)

namespace GridScheme
variable {Y : Crew C d} (Z : GridScheme Y) (f : Extraction.Order)

def physical (k) := Order.grid C (Z.depth k) (Z.mark k)
def testAt k := scaledGrid C (Z.depth k) (Z.mark k) (Z.scale k)
def actualLift k (u : ℕ×ℕ) := Z.lift k u.1 u.2



/-- Remaining placement/plateau requirements if also producing `Trials.Valid`
on these rows. No column limits or span identity assumed. Keep centered link
budget at origin (same T as below); the marks may depend on rounded radius.
`bounded` buys eventual affordable lifts separately at each period with common
levelwise cost. -/
structure PaidGrid : Prop where
  ratios : ∃ b : ℝ, 0 < b ∧ ∀ k, Z.scale k = C.S.a (Z.depth k) * ((C.path.levels.clock.monitor (Z.depth k))^b)
  same_stage k m (hq : Z.width k ≤ m) (hN : m ≤ Z.depth k) :
    C.path.levels.clock.J m=C.path.levels.clock.J (Z.depth k)
  scale_down : StrictAnti Z.scale
  conjugate (k N p i) : star (Z.lift k N p i) = Z.lift k N p i
  unit (k N p) : Z.lift k N p 0 = C.refUnit d
  bounded (k : ℕ) : ∃ A : ℝ, ∀ p, ∀ᶠ j : ℕ in atTop, ∀ i, ‖Z.lift k (f.mesh j) p i‖ ≤ A
  tuned : Tendsto Z.testAt atTop (𝓝 Y.target)
  seams : ∃ η : ℝ, 0 < η ∧ ∀ k j a, |Z.physical k j a| ≤ C.S.a (Z.width k)*((2:ℝ)⁻¹-η)
  generic (k) : Z.physical k ∈ YM.generic 2
  cheap (k : ℕ) (ε : ℝ) (he : 0 < ε) : f.late fun N p => ∃ h : Z.depth k ≤ N,
    let T := center C.S p ((Z.window k).trans h) 0
    ∀ i j, Budget T (C.beta N p)
      (atGrid C (Z.depth k) (Z.mark k 0) d (N,p) (Z.lift k N p i)) (atGrid C (Z.depth k) (Z.mark k 1) d (N,p) (Z.lift k N p j))
      (pointOne (Z.testAt k 0) (Y.β i)) (pointOne (Z.testAt k 1) (Y.β j)) (pointPair C d (Z.testAt k) (Y.β i) (Y.β j)) (Z.gap k+ε)

variable {Z f}
lemma PaidGrid.paid (h : PaidGrid Z f) : Paid Y.β f Z.depth Z.mark Z.scale Z.gap Z.actualLift := by
  exact Eventually.of_forall fun k ε he => (f.fused _).mpr ((h.cheap k ε he).mono fun _ ha => ha.mono fun _ ⟨h,H⟩ => ⟨_,H⟩)
lemma PaidGrid.bill (h : PaidGrid Z f) (k : ℕ) : ∃ A : ℝ, 0 < A ∧ ∀ p, ∀ᶠ j : ℕ in atTop, ‖Z.lift k (f.mesh j) p‖ ≤ A := by
  obtain ⟨A,hA⟩ := h.bounded k; refine ⟨|A|+1, by positivity, fun p => ?_⟩
  filter_upwards [hA p] with i hi; exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => (hi j).trans (by simp [le_trans (le_abs_self A) (show |A| ≤ |A|+1 by simp)])
lemma PaidGrid.cost (h : PaidGrid Z f) (k) : cost f (Z.actualLift k) := by
  obtain ⟨A,hA,hw⟩ := h.bill k
  exact ⟨A,hA,(f.fused _).mpr (Eventually.of_forall fun _ => hw _)⟩


variable (Z) (T : Table C.book) (later : ℕ → Y.Index → C.label d)






variable {Z}

end GridScheme
end YM.Push.FiniteDetection
