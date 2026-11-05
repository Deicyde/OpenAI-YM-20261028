import YM.Extraction.Round
import YM.Extraction.Limits

/-!
# Exact step integration
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter MeasureTheory Lattice
open scoped Topology BigOperators
variable {S : Schedule} {n : ℕ}

abbrev Var (S : Schedule) (n N p : ℕ) := Fin n → Site (S.side N p)

def bucket (N p : ℕ) (x : Points n) : Var S n N p := fun i => wrap _ (address (S.a N) x i)

theorem found {N p} {x : Points n} (hx : x ∈ Fund S p n) :
    x ∈ segment (S.a N) (fun i => lift (bucket N p x (S := S) i)) := by
  obtain ⟨r,hr,_⟩ := corners (N := N) hx
  have he : bucket N p x = r := by
    ext1 i
    change wrap _ _ = _; rw [congr_fun (show address (S.a N) x = _ from hr) i]; exact wrap_lift _
  rw [he]; exact hr

open scoped Classical in
def stair (S : Schedule) {n N p} (F : Var S n N p → ℂ) : Points n → ℂ := (Fund S p n).indicator
  fun x => F (bucket _ _ x)

lemma by_tile {N p} (F : Var S n N p → ℂ) : stair S F =
    ∑ r : Var S n N p, (segment (S.a N) (fun i => lift (r i))).indicator (fun _ => F r) := by
  classical
  funext x
  rw [Finset.sum_apply]
  by_cases hx : x ∈ Fund S p n
  · rw [stair,indicator_of_mem hx, Finset.sum_eq_single (bucket (S := S) N p x), indicator_of_mem (found hx)]
    · intro b _ hn
      refine indicator_of_notMem ?_ _
      intro ht
      exact hn ((corners hx).unique ht (found hx))
    simp
  · rw [stair,indicator_of_notMem hx]
    exact (Finset.sum_eq_zero fun b _ => indicator_of_notMem (fun he => hx (tile_in b he)) _).symm

lemma full_box (S : Schedule) (p n : ℕ) : MeasurableSet (Fund S p n) ∧ volume (Fund S p n) < ⊤ := by
  rw [show Fund S p n = ⋃ r : Var S n 0 p, segment (S.a 0) (fun i => lift (r i)) by
    ext x; rw [mem_iUnion]; exact ⟨fun h => ⟨_,found h⟩, by rintro ⟨r,hr⟩; exact tile_in r hr⟩]
  refine ⟨MeasurableSet.iUnion fun i => measurable_segment (S.a_pos _) _,?_⟩
  apply lt_of_le_of_lt (measure_iUnion_le _)
  simp_rw [cell_volume (S.a_pos 0)]
  rw [tsum_fintype]; exact ENNReal.sum_lt_top.mpr fun i _ => ENNReal.ofReal_lt_top

lemma cell_integrable {N p} (F : Var S n N p → ℂ) (r : Var S n N p) :
    Integrable ((segment (S.a N) (fun i => lift (r i))).indicator (fun _ => F r)) := by
  rw [integrable_indicator_iff (measurable_segment (S.a_pos _) _)]
  refine integrableOn_const ?_ (by finiteness)
  rw [cell_volume (S.a_pos _)]; exact ENNReal.ofReal_ne_top

lemma stair_int {N p} (F : Var S n N p → ℂ) : Integrable (stair S F) := by
  rw [by_tile]
  exact integrable_finsetSum' _ fun r _ => cell_integrable F r

theorem stair_integral {N p} (F : Var S n N p → ℂ) :
    (∫ x : Points n, stair S F x) = (S.a N : ℂ)^(4*n) * ∑ r, F r := by
  rw [by_tile]
  simp_rw [Finset.sum_apply]
  rw [integral_finsetSum _ fun r _ => cell_integrable F r, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  rw [integral_indicator (measurable_segment (S.a_pos _) _), setIntegral_const, measureReal_def,
    cell_volume (S.a_pos N), ENNReal.toReal_ofReal (pow_nonneg (S.a_pos N).le _), Complex.real_smul,
    Complex.ofReal_pow]

variable {G : Gauge} (C : Family G)
def densityCell (N p : ℕ) (v : Fin n → C.book.Token) (f : Test n) :=
  stair C.S fun r : Var C.S n N p => f (Order.cells C N p r) * C.numeric N p v r

theorem exactSmear (N p : ℕ) (v : Fin n → C.book.Token) (f : Test n) :
    (∫ x, densityCell C N p v f x) = Order.smears C N p v f := stair_integral _

theorem stepped (N p : ℕ) {x : Points n} (hx : x ∈ Fund C.S p n) (v : Fin n → C.book.Token) (f : Test n) :
    densityCell C N p v f x = f (tag (C.S.a N) (address (C.S.a N) x)) *
    C.numeric N p v (bucket N p x) := by
  rw [densityCell,stair,indicator_of_mem hx]
  congr 2
  apply PiLp.ext
  intro i
  have h := congr_fun (show address (C.S.a N) x = _ from found (N := N) hx) i
  simp only [Order.cells,points_apply, tag, Schedule.place]
  exact congr_arg (C.S.gridPoint N) h.symm
end YM.Extraction
