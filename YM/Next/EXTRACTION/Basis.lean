import YM.Next.EXTRACTION.Tails
import YM.Org.Theatre
import YM.Work.B04
import YM.Work.B06

/-!
# It suffices to estimate a finite basis at every level for RRaw / ROnecap

This is a route to the centered estimates used in `common` which does not
need to deal with an uncountable list of real/complex coefficients.

Establish
also that this basis version asks for no extra periodic uniformity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Set Function Filter MeasureTheory Extraction Wilson Lattice Cells
open scoped Topology BigOperators

section Root
variable {n : Side} {G : Gauge} (T : Tiling n) (β : ℝ)

/-- Complex scaling of the real nonnegative root budget. The replicated
copies conjugate the scaling coefficient when specified by the tiling, which
must be accounted for *before* taking this norm. -/
theorem root_smul (F : Config G n → ℂ) (c : ℂ) : T.rootTest β (c • F) = ‖c‖ * T.rootTest β F := by
  classical
  let w (i : T.Cell) := if T.hand i then star c else c
  have ht (i U) : T.copy i (c • F) U = w i * T.copy i F U := by
    unfold Tiling.copy w
    split_ifs <;> simp
  have hw : ‖∏ i, w i‖ = ‖c‖ ^ Fintype.card T.Cell := by
    rw [norm_prod]
    have hh (i : T.Cell) : ‖w i‖ = ‖c‖ := by unfold w; split <;> simp
    simp [hh]
  have he := T.cells_positive
  apply (pow_left_inj₀ (T.root_nonneg β (c • F)) (mul_nonneg (norm_nonneg c) (T.root_nonneg β F)) he.ne').mp
  rw [T.powering,mul_pow,T.powering]
  unfold Tiling.rootPower Tiling.fullAt moment
  simp_rw [ht,Finset.prod_mul_distrib,integral_const_mul,norm_mul,hw]

/-- Estimate linear combinations of true cylinder entries in the centered
root. Interior includes dependence only in the strict chamber sites, gauge
invariance, measurability and a finite pointwise bound. Empty sum covered. -/
theorem rooted {ι : Type*} (h : Seam G n β) (I : Finset ι) (F : ι → Config G n → ℂ) (c : ι → ℂ)
    (H : ∀ i ∈ I, Interior (T.chamber 0) (F i)) :
    Interior (T.chamber 0) (∑ i ∈ I, c i • F i) ∧
    T.rootTest β (∑ i ∈ I, c i • F i) ≤ ∑ i ∈ I, ‖c i‖ * T.rootTest β (F i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,Finset.sum_empty]
    refine ⟨Interior.constant _ _,?_⟩
    have he := root_smul T β (0 : Config G n → ℂ) 0
    simp only [smul_zero,norm_zero,zero_mul] at he
    exact he.le
  | @insert i I hi ih =>
    obtain ⟨he,hc⟩ := ih fun j hj => H j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hm : Interior (T.chamber 0) (c i • F i) := (H i (Finset.mem_insert_self _ _)).scale _
    refine ⟨hm.plus he,(h.semi T _ _ hm he).trans ?_⟩
    rw [root_smul]
    gcongr
end Root

section AtLevel
variable {G : Gauge} {C : Family G} {ι : Type*} [Fintype ι] {d : ℕ}




end AtLevel

section AtPort
variable {G : Gauge} {C : Family G} {ι : ℕ → Type*} [∀ d, Fintype (ι d)] {f : Extraction.Order}

/-- Suffices to estimate the actual cylinders on an ordinary choice of basis
at each finite weight level. Need both quantifier patterns, based on strict
centered link tilings for each m tested (all positions, interior and
normalized root on the Wilson law). Uniform constants here only across the
finite basis at that level, not across d.

In `.per` a fresh bound is allowed for fixed period p and fixed m, on the
*common* f.mesh. In `.power` exponent has arbitrarily small addition ε to d
as requested by `CellHyp`. The estimate only uses ordered tails once m is
fixed and with another η slack in the bound. Thus no assertion that the power
bound must cover every p. -/
structure BasisBudget (C : Family G) (B : ∀ d, Module.Basis (ι d) ℂ (C.label d)) (f : Extraction.Order) : Prop where
  per (d p : ℕ) : ∀ᶠ m in atTop, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j : ℕ in atTop, ∀ i,
    centeredBudget C ⟨d,B d i⟩ D m (f.mesh j) p
  power (d : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ m₀ : ℕ, C.ref d ≤ m₀ ∧ ∃ D : ℝ, 0 ≤ D ∧
    ∀ m ≥ m₀, ∀ η : ℝ, 0 < η → f.late fun N p => ∀ i, centeredBudget C ⟨d,B d i⟩
      (D * (C.S.a m)^(-(d:ℝ)-ε) + η) m N p

variable {B : ∀ d, Module.Basis (ι d) ℂ (C.label d)}




end AtPort
end YM.Next.Extract
