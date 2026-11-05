import YM.Push.SECTOR_MEASURE.Oriented
import YM.UVNext.PRICED_KERNELS.Assembly



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Immediate physical costs on the wired kernel (no path interactions yet)

Only the Φ,T Rows (and compatible choice of ell paths from the cover) and
no cubic/quartic/etc correction kernels are needed for one nontrivial physical
consumer of this bridge, the sector payment/assembly before any Directed or
Kin exists. Exhibit the use on these actual path choices/Fields (no iterated
transfer result; any number of single-step costs wherever Rows chosen like this),
and the corresponding conditional results on generated Paths with actual nonlinear
correction estimates still to be proved. Uses the SAME hat beta/tag conventions
and Allocation, not e.g. paying overlapping indicators as a partition. No
assumption branches outputs independent! Nothing on whether resulting charge
suffices to bound nonlinear continuation expenses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure
open Pressure.Stores Tree Push.PriceCompiler Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

/-- Base paths, noninteracting correction atoms. Useful BEFORE generating the
nonlinear paths: e.g. obtain Teller's offer on these actual Beds/Tubes and
path ell reads *as-is*, retaining the true layout cost; this is not a claim
this R series has the required Wilson/next-match properties (not even of the
top path). The correction atoms in the full construction will incur their
own (yet unfunded!) costs. No simplification of fields, groups, or volumes in
these estimates.
-/
def dormant (G : Gauge) (k : ℕ) : Atom G k := ⟨fun _ => Canonical.slot ⟨(0,1),by decide⟩ 0,0⟩

def basePath (G : Gauge) (H : Bed) : PathData G := ⟨Canonical.row H,fun _ => dormant _ _,fun _ => dormant _ _,fun _ => dormant _ _⟩

lemma dormancy (k : ℕ) {σ C : ℝ} (hp : 0 ≤ C) : (dormant G k).Invariant ∧ SumBudget (fun _ : ℕ => (dormant G k).budget σ) C :=
  ⟨by simp [dormant,Atom.Invariant, Atom.poly], by simp only [dormant,Atom.budget,Atom.magnitude,Pi.zero_apply, abs_zero,Finset.sum_const_zero, zero_mul]; simpa only [tsum_zero] using
    (show SumBudget (fun _ : ℕ => (0:ℝ)) C from ⟨fun _ => le_rfl,summable_zero,(Eq.trans_le tsum_zero hp)⟩)⟩

lemma base_atoms (H : Bed) {σ two C : ℝ} (ha : 0 ≤ two) (hb : 0 ≤ C) : Atoms σ two C C (basePath G H) :=
  ⟨(dormancy (G:=G) (σ:=σ) 2 ha).2,(dormancy (G:=G) (σ:=σ) 3 hb).2,(dormancy (G:=G) (σ:=σ) 4 hb).2, fun _ =>
    ⟨(dormancy (G:=G) (σ:=σ) 2 ha).1,(dormancy (G:=G) (σ:=σ) 3 hb).1,(dormancy (G:=G) (σ:=σ) 4 hb).1⟩,
    by simp [PathData.loop_jets,PathData.loop_coeff,dormant,basePath]⟩

section Step
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G} (h : Permit M I a) {V : Horizon a} (hv : Motor P a V)

def base (V : Horizon a) (N m : ℕ) := basePath G (V.H N m)
include h hv



lemma ticket_to_measure {Q : ℕ → ℕ → PathData G} (hi : Installed P a V Q) (N m p : ℕ) (hm : m < N) :
    let j := a.clock.J (m+1); let i := a.clock.J m; let x := a.clock.hatBeta m
    let S := a.clock.op m p; let Z := Permit.tube V Q N m p
    Teller.Funds (Testing.query (P.sheet G f) (P.frozen G) j i) S Z ∧
      PointCharge Z x (M.w j i) (M.rate j) ∧ Charged Z x (M.w j i) (M.rate j) := by
  obtain ⟨he,hh⟩ := h.tickets hi.prices hv.finalCosts (fun N m hk => (hi.linear _ _ hk).placed) N m p hm
  intro j i x S Z
  have hl : fiery G x S.patch.L = a.clock.threshold (m+1) := by
    change temp _=temp _
    rw [beta_eq h.paid m,← block_eq h.paid m]; rfl
  have h₁ : PointCharge Z x (M.w j i) (M.rate j) := fun F A U k X hs hx => by
    rw [hl]; exact hh A U k X F hs hx
  exact ⟨he,h₁,h₁.charged he⟩


end Step
end YM.UVNext.PricedKernels
