import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.LocalJet



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Cost of overlapping log neighborhoods. Also exponential version for
Gram. Distances from coarse parents; sums in real link indices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.LocalJet
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open YM.Work.F01
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f n : Side} {S : StepData c f}

def members (S : StepData c f) (x : Site c) (r : ℕ) := univ.filter (fun i : Bond f => separation x (S.ratio.parent i.1) ≤ r)

def grain (r : ℕ) : ℝ := ((r+r+1)^4 : ℕ)

def chips (S : StepData c f) (r : ℕ) : ℝ := Fintype.card (Site S.patch.L) * (grain r * Fintype.card Axis)

lemma saves (S : StepData c f) (x : Site c) (r : ℕ) : ((members S x r).card:ℝ) ≤ chips S r := by
  let Z := halo r {x}
  have he (e : Site c) : separation x e ≤ r ↔ e∈Z := by simp [Z, halo_spec]
  have hx : (Z.card:ℝ) ≤ grain r := by unfold grain; exact_mod_cast
    (show Z.card ≤ _ by simpa using Lattice.Corona.halo_size ({x}:Support c) r)
  let t (e : Bond c) : ℝ := if e.1 ∈ Z then 1 else 0
  calc
    _ = ∑ i : Bond f, t (S.ratio.parent i.1,i.2) := by
      unfold members t; simp_rw [he, ← sum_filter]; simp
    _ = _ := sum_parent_bond S.ratio t
    _ = (Fintype.card (Site S.patch.L):ℝ)*(Z.card * Fintype.card Axis) := by
      unfold t; rw [Fintype.sum_prod_type,sum_comm]
      dsimp only
      have ht : (∑ i : Site c, if i ∈ Z then (1:ℝ) else 0) = Z.card := by rw [← sum_filter]; simp
      simp_rw [ht]; simp [mul_comm]; exact Or.inl rfl
    _ ≤ _ := by unfold chips; gcongr

lemma spends (y : Site c) (r : ℕ) : (∑ i : Site c, if separation i y ≤ r then (1:ℝ) else 0) ≤ grain r := by
  have he (x : Site c) : separation x y ≤ r ↔ x∈halo r {y} := by rw [separation_comm]; simp [halo_spec]
  simp_rw [← sum_filter,he]
  rw [sum_const,nsmul_eq_mul,mul_one,filter_mem_eq_inter,univ_inter]
  unfold grain
  exact_mod_cast (show (halo r ({y}:Support c)).card ≤ _ by simpa using Lattice.Corona.halo_size ({y}:Support c) r)

def powerCost (a : Directions G f) := ∑ i : Bond f, ‖a i‖^2

/-- Site-indexed version. Need a multiplicity to use on Body rows. -/
lemma samples (S : StepData c f) (a : Directions G f) (r : ℕ) :
    (∑ x : Site c, (settle S x r a)^2) ≤ (chips S r * grain r)*powerCost a := by
  unfold settle powerCost
  let t (x : Site c) (i : Bond f) : ℝ := if separation x (S.ratio.parent i.1) ≤ r then 1 else 0
  have he (x : Site c) : settle S x r a ^ 2 ≤ chips S r * ∑ i, t x i * ‖a i‖^2 := by
    have hi := Finset.sum_mul_sq_le_sq_mul_sq (R:=ℝ) (members S x r) (fun _ => 1) (fun i => ‖a i‖)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hi
    unfold t
    simp_rw [ite_mul,one_mul,zero_mul, ← sum_filter]
    exact hi.trans (mul_le_mul_of_nonneg_right (saves _ _ _) (sum_nonneg fun i _ => sq_nonneg _))
  refine (sum_le_sum (fun i _ => he i)).trans ?_
  rw [← mul_sum,sum_comm]
  have hp : 0 ≤ chips S r := by unfold chips grain; positivity
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hp
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right (spends _ _) (by positivity)
end YM.Next.SectorChange.LocalJet
