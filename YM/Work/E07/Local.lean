import YM.Corona.Fill
import YM.Work.E07.Columns
import YM.Work.E07.Scale

/-!
# Paying a coarse face from only local hypotheses

Freeze which fine plaquettes and noise bonds may pay excess. Inside the
specified halo all other fine and noise contributions are small; on a coarse
face propagate these bounds through the macro charge lemma, at honest
multiplicity even on the torus. Columns of the macro stencil on the physical
period are priced by MacroStore (E01); row size, needed only in the small term,
can cost L. Constants never grow with torus size for fixed L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E07
open Lattice RG Finset Wilson Pressure Pressure.Stores Bid
open scoped BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {Q V : Config G c} {U : Config G f} {k : S.Choices} {A : Stores S}
    {x t W D : ℝ} {N : ℕ}

lemma dome_extend {i j : Site c} {r d b : ℕ} (hi : i ∈ A.dome r)
    (h : separation i j ≤ d) (hh : r + d ≤ b) : j ∈ A.dome b := by
  obtain ⟨z, hz, hzi⟩ := halo_spec.mp hi
  exact halo_spec.mpr ⟨z, hz, (separation_triangle z i j).trans ((add_le_add hzi h).trans hh)⟩

lemma separation_plank (i : Site c) (y : Cover) {n : ℕ} (hy : y ∈ box n) :
    separation i (plank i y) ≤ n := by
  obtain ⟨h, h'⟩ := box_test.mp hy
  rw [separation_comm, separation, plank, add_sub_cancel_right]
  apply Finset.sup_le; intro j _
  apply (Corona.lap y j).trans
  have := h j; have := h' j; omega

lemma plot_usable (hp : Stores.Plot A U k V x W) (i : Site c)
    (hi : i ∈ A.dome (3 * radiusB x)) (hB : 1 ≤ radiusB x) : usable S U i k :=
  fun y hy => hp.list _ (dome_extend hi (separation_plank i y hy) (by omega))

/-- Keep the full sizes on this Finset. -/
def picked {α : Type*} (s : Finset α) (g : α → ℝ) (i : α) := if i ∈ s then g i else 0

lemma picked_nonneg {α : Type*} (s : Finset α) {g : α → ℝ} (hg : ∀ i, 0 ≤ g i) (i : α) :
    0 ≤ picked s g i := by unfold picked; split <;> simp [hg]

lemma picked_sum {α : Type*} [Fintype α] (s : Finset α) (g : α → ℝ) :
    ∑ i, picked s g i = ∑ i ∈ s, g i := by
  rw [← sum_subset (subset_univ s) (fun _ _ h => by simp [picked, h])]
  exact sum_congr rfl fun _ h => by simp [picked, h]

lemma toll_split (hp : Stores.Plot A U k V x W) (p : Cell f)
    (h : S.ratio.parent p.1 ∈ A.dome (5 * radiusB x)) :
    let u := fiery G x S.patch.L
    toll U p ≤ u + picked (A.swell U u) (toll U) p := by
  intro u
  have hu : 0 ≤ u := temp_nonneg _
  unfold picked
  split
  · exact le_add_of_nonneg_left hu
  next hn =>
    rw [add_zero]
    by_cases h' : p ∈ A.costs
    · exact le_of_not_gt fun ht => hn (mem_filter.mpr ⟨h', ht⟩)
    have hv : ¬ Disjoint (A.dome (5 * radiusB x)) (startPos S p) := fun H =>
      disjoint_left.mp H h (mem_image_of_mem _ (show p.1 ∈ touched p by simp [touched, square_corners]))
    exact ((hp.consumes p hv).2 h').trans (show u / 2 ≤ u by linarith only [hu])

lemma wire_split (hp : Stores.Plot A U k V x W) (hW : 0 ≤ W) (p : Bond c)
    (h : p.1 ∈ A.dome (5 * radiusB x)) :
    wire (S.prediction U k) V p ≤ 2 * W * fiery G x S.patch.L +
      picked A.aisles (wire (S.prediction U k) V) p := by
  unfold picked
  split
  · exact le_add_of_nonneg_left (mul_nonneg (by positivity) (temp_nonneg _))
  next hn =>
    rw [add_zero]
    exact (hp.drive p (fun H => disjoint_left.mp H h (show p.1 ∈ pinPos p by simp [pinPos]))).2 hn

/-- Uniform bound AFTER L on number of inputs, sufficient for small-input estimate. -/
def macroSize (j : ℕ) (L : Side) : ℝ :=
    Fintype.card PlaqAxes * ((box ((j + 3) * L.val + 4 * L.val)).card : ℝ)

lemma mcharge_row (i : Site c) :
    ∑ p : Cell f, (mcharge S i p : ℝ) ≤ macroSize S.patch.J S.patch.L := by
  let s := box (macroR S.patch)
  have hh (p : Cell f) : (mcharge S i p : ℝ) ≤
      ∑ z ∈ s, if wrap f z + S.ratio.embed i = p.1 then (1 : ℝ) else 0 := by
    unfold mcharge
    rw [sum_boole]
    apply Nat.cast_le.mpr
    apply card_le_card
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1, (mem_filter.mp hz).2.1⟩
  apply (sum_le_sum (s := (univ : Finset (Cell f))) (fun p _ => hh p)).trans_eq
  rw [sum_comm]
  have he (z : Cover) : (∑ p : Cell f, if wrap f z + S.ratio.embed i = p.1 then (1 : ℝ) else 0) =
      (Fintype.card PlaqAxes : ℝ) := by
    unfold Cell Face; rw [Fintype.sum_prod_type, sum_comm]; simp
  simp_rw [he, sum_const, nsmul_eq_mul]
  rw [mul_comm]
  rfl

/-- Sum *all four* boundary noise charges at the specified face. -/
def fourBonds (F : Bond c → ℝ) (p : Cell c) : ℝ :=
    F (p.1, p.2.val.1) + F (p.1 + Lattice.step p.2.val.1, p.2.val.2) +
      F (p.1 + Lattice.step p.2.val.2, p.2.val.1) + F (p.1, p.2.val.2)

lemma fourBonds_nonneg (F : Bond c → ℝ) (hF : ∀ b, 0 ≤ F b) (p : Cell c) : 0 ≤ fourBonds F p := by
  exact add_nonneg (add_nonneg (add_nonneg (hF _) (hF _)) (hF _)) (hF _)

lemma fourBonds_total (F : Bond c → ℝ) (hF : ∀ b, 0 ≤ F b) :
    ∑ p : Cell c, fourBonds F p ≤ 4 * Fintype.card PlaqAxes * ∑ b, F b := by
  -- For each fixed type, each of the four maps is injective (including on the periodic lattice).
  have hi (g : Site c → Bond c) (hg : Function.Injective g) : ∑ x, F (g x) ≤ ∑ b, F b := by
    rw [← sum_image (s := univ) hg.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun b _ _ => hF b)
  have hh (p : PlaqAxes) : ∑ x : Site c, fourBonds F (x, p) ≤ 4 * ∑ b, F b := by
    unfold fourBonds; simp_rw [sum_add_distrib]
    apply le_trans (add_le_add (add_le_add (add_le_add
      (hi (fun x => (x, p.val.1)) (fun _ _ he => (Prod.mk.inj he).1))
      (hi (fun x => (x + Lattice.step p.val.1, p.val.2)) (fun _ _ he => add_right_cancel (Prod.mk.inj he).1)))
      (hi (fun x => (x + Lattice.step p.val.2, p.val.1)) (fun _ _ he => add_right_cancel (Prod.mk.inj he).1)))
      (hi (fun x => (x, p.val.2)) (fun _ _ he => (Prod.mk.inj he).1)))
    exact le_of_eq (by ring)
  unfold Cell Face; rw [Fintype.sum_prod_type, sum_comm]
  exact (sum_le_sum (fun p _ => hh p)).trans_eq (by rw [sum_const, card_univ, nsmul_eq_mul]; ring)

/-- This is the small-input multiplier on toll V. -/
def macroSmall (j : ℕ) (D : ℝ) (L : Side) (W : ℝ) :=
    8 * W + D / (L.val : ℝ)^2 * macroSize j L

/-- The excess on a V face is propagated from fine tolls and predictor-output wires. -/
def macroExcess (S : StepData c f) (D : ℝ) (E : Cell f → ℝ) (F : Bond c → ℝ) (p : Cell c) :=
    fourBonds F p + D / (S.patch.L.val : ℝ)^2 * ∑ z, mcharge S p.1 z * E z

lemma macroSmall_nonneg (j : ℕ) (hD : 0 ≤ D) (L : Side) (hW : 0 ≤ W) :
    0 ≤ macroSmall j D L W := by unfold macroSmall macroSize; positivity

lemma macroExcess_nonneg (S : StepData c f) (hD : 0 ≤ D) {E : Cell f → ℝ}
    {F : Bond c → ℝ} (hE : ∀ i, 0 ≤ E i) (hF : ∀ i, 0 ≤ F i) (p : Cell c) :
    0 ≤ macroExcess S D E F p := by
  unfold macroExcess
  exact add_nonneg (fourBonds_nonneg F hF p) (mul_nonneg (by positivity)
    (sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hE _)))

/-- Sum the excess across the torus with PRE-L constants. -/
def macroLarge (N : ℕ) (D : ℝ) :=
    4 * (Fintype.card PlaqAxes : ℝ) + D * Fintype.card PlaqAxes * N

lemma macroExcess_total (H : MacroStore S G N) (hD : 0 ≤ D) {E : Cell f → ℝ} {F : Bond c → ℝ}
    (hE : ∀ i, 0 ≤ E i) (hF : ∀ i, 0 ≤ F i) :
    ∑ p, macroExcess S D E F p ≤
        macroLarge N D * ((∑ i, E i) / (S.patch.L.val : ℝ)^2 + ∑ i, F i) := by
  have hc (z : Cell f) : ∑ p : Cell c, (mcharge S p.1 z : ℝ) ≤ (Fintype.card PlaqAxes : ℝ) * N := by
    unfold Cell Face; rw [Fintype.sum_prod_type]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← Finset.mul_sum]; gcongr
    exact_mod_cast H.count z
  unfold macroExcess
  rw [sum_add_distrib, ← Finset.mul_sum]
  apply (add_le_add (fourBonds_total F hF) (mul_le_mul_of_nonneg_left
    (excess_sum (fun (p : Cell c) z => (mcharge S p.1 z : ℝ)) univ (fun _ _ => by positivity) hc hE)
    (show 0 ≤ D / (S.patch.L.val : ℝ)^2 by positivity))).trans
  let a : ℝ := Fintype.card PlaqAxes
  let fsum : ℝ := (∑ i, E i) / (S.patch.L.val : ℝ)^2
  have hsum : 0 ≤ fsum := div_nonneg (sum_nonneg fun i _ => hE i) (by positivity)
  calc
    _ = 4 * a * (∑ i, F i) + D * a * N * fsum := by unfold fsum a; ring
    _ ≤ 4 * a * (fsum + ∑ i, F i) + D * a * N * (fsum + ∑ i, F i) := by
      unfold a; gcongr
      · exact le_add_of_nonneg_left hsum
      exact le_add_of_nonneg_right (sum_nonneg fun i _ => hF i)
    _ = _ := by unfold macroLarge a fsum; ring

lemma coarse_split (H : MacroStore S G N) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hp : Stores.Plot A U k V x W) (hB : 1 + N ≤ radiusB x) (p : Cell c)
    (hi : p.1 ∈ A.dome (3 * radiusB x))
    (hq : usable S U p.1 k → toll V p ≤ fuel (S.prediction U k) V p.1 p.2 +
          D / (S.patch.L.val : ℝ)^2 * port S p.1 U) :
    let u := fiery G x S.patch.L
    toll V p ≤ macroSmall S.patch.J D S.patch.L W * u + macroExcess S D
      (picked (A.swell U u) (toll U)) (picked A.aisles (wire (S.prediction U k) V)) p := by
  let u := fiery G x S.patch.L
  let Q := S.prediction U k
  let F := picked A.aisles (wire Q V)
  let E := picked (A.swell U u) (toll U)
  have hf : fuel Q V p.1 p.2 ≤ 8 * W * u + fourBonds F p := by
    have he : p.1 ∈ A.dome (5 * radiusB x) := Corona.halo_mono (by omega) (Subset.refl A.place) hi
    have hs (j : Axis) : p.1 + Lattice.step j ∈ A.dome (5 * radiusB x) := by
      apply dome_extend hi _ (d := 1) (by omega)
      rw [separation_comm, separation, add_comm, add_sub_cancel_right]; exact pdist_step _
    let i := p.2.val.1
    let j := p.2.val.2
    unfold fuel
    apply (add_le_add (add_le_add (add_le_add (wire_split hp hW (p.1, i) he)
        (wire_split hp hW (_, j) (hs i))) (wire_split hp hW (_, i) (hs j)))
        (wire_split hp hW (p.1, j) he)).trans_eq
    unfold u fourBonds F Q i j
    ring
  have hh : port S p.1 U ≤ macroSize S.patch.J S.patch.L * u + ∑ z, mcharge S p.1 z * E z := by
    rw [H.funded]
    refine small_sum (fun _ => Nat.cast_nonneg _) (mcharge_row p.1) (temp_nonneg _) ?_
    intro z hz
    exact toll_split hp z (dome_extend hi (H.maps _ _ (by exact_mod_cast hz)) (by omega))
  dsimp only
  apply (hq (plot_usable hp p.1 hi (by omega))).trans
  apply (add_le_add hf (mul_le_mul_of_nonneg_left hh (show 0 ≤ D / (S.patch.L.val : ℝ)^2 by positivity))).trans_eq
  unfold macroSmall macroExcess F Q E u
  ring

end YM.Work.E07
