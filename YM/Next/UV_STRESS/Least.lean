import YM.Next.UV_STRESS.Annulus
import YM.Next.UV_STRESS.Birth


/-!
# Counterterm may also be paid by genuine branch-station estimates
- bounded at birth → bounded at ref (for that station's comparisons)
- geometry includes offsets/seam.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Measure Analysis Extraction Table Ward Cells Lattice Wilson Overlay Marker RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {F : Extraction.Order}
variable {N p ℓ k h m d D : ℕ} (P : C.Makes)

/-- Use only at **fixed** birth time. Product here not claimed uniform/subexponential
as birth approaches UV. -/
def quota (d k N p : ℕ) (x : C.book.Ref d) := (C.labels.level d).coeffSize
    ((C.factory d N p).entries k ((C.factory d N p).terminal.symm x)).x
include P

lemma quota_stop {k : ℕ} (h : C.ref D≤k) : ∃ a : ℝ, 0≤a ∧ ∀ N p (x : C.book.Ref D), k ≤ N →
    ‖x‖ ≤ a*quota C D k N p x := by
  induction k,h using Nat.le_induction with
  | base =>
    refine ⟨1,zero_le_one,fun N p x h => ?_⟩
    rw [one_mul, quota]; rw [show ((C.factory D N p).entries _ _).x = x from C.normalized P h x]
    apply (pi_norm_le_iff_of_nonneg (show 0 ≤ _ from Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
    intro i; exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  | succ k h ih =>
    obtain ⟨a,ha,hA⟩ := ih
    let c := (C.path.levels.params (k+1)).columns * ((C.path.S.block k).val : ℝ)^D
    have hx : 0<c := mul_pos (zero_lt_one.trans_le (C.path.levels.params _).columns_ge) (pow_pos (by exact_mod_cast (C.path.S.block k).property) _)
    refine ⟨a*c,mul_nonneg ha hx.le,fun N p x he => ?_⟩
    have hu := Nat.le_trans (Nat.le_succ _) he
    calc
      _ ≤ _ := hA _ _ x hu
      _ ≤ a*(c*quota C D (k+1) N p x) := mul_le_mul_of_nonneg_left
        ((P.calibrated D N p (h.trans hu)).front k h he _) ha
      _ = _ := by ring

section seam

omit P in
private lemma staying {v : ℕ} : ∀ᶠ i : ℕ in atTop, ∀ (hn : v + 1 ≤ i) (p : ℕ),
    C.S.a v / 4 ≤ C.S.a i * (((terrace C.S v hn p).side.val/3:ℕ):ℝ) := by
  have hf := C.S.a_pos v
  filter_upwards [C.S.shrinks.eventually (ge_mem_nhds (by linarith : (0:ℝ) < C.S.a v/20))] with i hi hn p
  let t := terrace C.S v hn p
  have hT : (t.side.val:ℝ) ≤ 3*((↑(t.side.val/3):ℝ)) + 2 := by exact_mod_cast (show t.side.val ≤ 3*(t.side.val/3)+2 by omega)
  have hz := C.S.embeds_scale t.units
  change _ ≤ C.S.a i * (((t.side.val/3:ℕ)):ℝ)
  nlinarith [mul_le_mul_of_nonneg_left hT (C.S.a_pos i).le]


end seam
end YM.Next.UVStress
