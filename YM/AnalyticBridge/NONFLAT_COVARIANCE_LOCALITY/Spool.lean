import Mathlib.Data.Set.Finite.List
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine


/-!
# Condense cut path lists for a single D calculation

Only the length is cut in `faceKick`. There may really be infinitely many
occurrences in the definition of *the same* installed D. Charge every one,
then for finite-order estimates it suffices to price the germs in a finite
list (coalescing *identical* cover slots only). No identification required
between the different sector components / tag choices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Lattice RG Precision Wilson Pressure Next.SectorChange
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {f : Side} {p : Clip} {σ C Λ : ℝ}

private lemma finite_spool (r : ℕ) : Set.Finite {s : RG.Slot | s.length ≤ r} := by
  let e (s : RG.Slot) := (s.walk, s.plaq)
  letI : Finite Step := Finite.of_injective (fun x : Step => (x.dir,x.neg))
    (by rintro ⟨a,b⟩ ⟨c,d⟩ h; cases Prod.mk.inj h; congr)
  have he : Function.Injective e := by rintro ⟨a,b⟩ ⟨c,d⟩ h; cases Prod.mk.inj h; congr
  refine (((List.finite_length_le Step r).prod (Set.finite_univ (α:=PlaqAxes))).preimage he.injOn).subset ?_
  intro i hi
  refine ⟨?_, Set.mem_univ _⟩
  change i.walk.length+4 ≤ r at hi
  change i.walk.length ≤ r
  omega

def spool (r : ℕ) := (finite_spool r).toFinset
lemma on_spool (r : ℕ) (s : RG.Slot) : s∈spool r ↔ s.length ≤ r := Set.Finite.mem_toFinset _

variable (T : PathData G)

private def copied_price (b : PlaqAxes) (s : RG.Slot) (i : ℕ) : ℝ :=
  if s=(T.row b i).2 then (T.row b i).1 else 0

def condensed (b : PlaqAxes) (s : RG.Slot) := ∑' i, copied_price T b s i

private lemma price_sum (h : T.Bounds p σ C Λ) (b : PlaqAxes) (s : RG.Slot) :
    Summable (copied_price T b s) := by
  refine Summable.of_norm_bounded (Work.F03.row_abs_summable T h b) ?_
  intro i; unfold copied_price; split
  · exact le_rfl
  rw [norm_zero]; exact abs_nonneg _

/-- Actual kernel on *all* numerical inputs (no positivity needed). -/
lemma barrel_on_spool (h : T.Bounds p σ C Λ) (r : ℕ) (U : Config G f)
    (b : LogArray G (Cell f)) (i : Cell f) :
    barrel T r U b i = ∑ s ∈ spool r, condensed T i.2 s •
      G.adjoint (travel U i.1 s.walk) (b (Work.F03.slotFace s i.1)) := by
  let H (s : RG.Slot) := G.adjoint (travel U i.1 s.walk) (b (Work.F03.slotFace s i.1))
  have hh := hasSum_sum (f:=fun s n => copied_price T i.2 s n • H s)
    (s:=spool r) fun s _ => (price_sum T h i.2 s).hasSum.smul_const (H s)
  refine Eq.trans ?_ hh.tsum_eq
  unfold barrel
  apply tsum_congr; intro n
  simp only [copied_price,ite_smul,zero_smul,Finset.sum_ite_eq',on_spool,H]



end YM.AnalyticBridge.NonflatCovarianceLocality
