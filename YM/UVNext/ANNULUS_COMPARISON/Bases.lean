import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.SpanQ
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression






set_option warningAsError false

/-!
# Matching at an actual blocking offset

Work on the given cutoff hierarchy `C`, without moving the test to the parent site.
Coordinates for an advanced basis may themselves be quoted *at that offset*.
Construct cutoff columns and counterterms by inverse coordinate transfer at admitted
intermediate stops. The hypothetical transfers at non-origin offsets here must be for
actual literal cylinders in the unmodified top section and true pushes; the inverse
arguments don't produce those trajectories. See Invoice for the additional many-marked
estimates required there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {c d N p k : ℕ}

/-- Relative to the *same bare section*, not necessarily the same intermediate
coordinates as the factory, even for a translate of the same literal field. -/
structure Native (C : Family G) (d N p : ℕ) where
  point (m : ℕ) : Site (C.side m p)
  run (m : ℕ) (v : C.label d) : Source.Coefficient (C.labels.level d) (C.side m p)

abbrev size (C : Family G) (d : ℕ) (x : C.label d) : ℝ := (C.labels.level d).coeffSize x

lemma size_nonneg (v : C.label d) : 0 ≤ size C d v := Finset.sum_nonneg fun _ _ => norm_nonneg _



lemma size_eq_zero {v : C.label d} (h : size C d v ≤ 0) : v=0 := by
  funext i; apply norm_le_zero_iff.mp
  exact le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)) h

namespace Native
variable (A : Native C d N p)

structure Progress (A : Native C d N p) (o : Site (C.side N p)) (c : ℕ) : Prop where
  fits : c ≤ N
  placement : A.point N=o
  ancestry m : c ≤ m → m < N → (operation C p m).ratio.parent (A.point (m+1))=A.point m
  based m v : c ≤ m → m ≤ N →
    (A.run m v).Format (A.point m) C.params (C.path.rep N p m) ∧
      (A.run m v).remBound (A.point m) (C.path.rep N p m) (Real.sqrt (C.path.levels.clock.forcedAllowance m))
        ((C.path.levels.params m).columns * (C.labels.level d).coeffSize ((C.labels.level d).core (A.run m v).x))
  bare v U : (A.run N v).density (A.point N) (C.localSection d) (C.path.rep N p N) U =
    ((C.S.a N : ℂ)^d) * ((C.path.rep N p N).eval U : ℂ) * Source.initial (C.localSection d) C.path N p v o U
  coordinate v : (A.run N v).x=v
  transfer m : c ≤ m → m < N → ∀ v,
    (A.run m v).density (A.point m) (C.localSection d) (C.path.rep N p m) =
      ((C.S.block m).val : ℂ)^d • (operation C p m).push (C.path.β N p (m+1))
        ((A.run (m+1) v).density (A.point (m+1)) (C.localSection d) (C.path.rep N p (m+1)))
  linear m : c ≤ m → m ≤ N → IsLinearMap ℂ (fun v => (A.run m v).x)
  back m v : c ≤ m → m < N → size C d (A.run (m+1) v).x ≤
    (C.path.levels.params (m+1)).columns * size C d (A.run m v).x

variable {A} {o : Site (C.side N p)}

theorem Progress.back_budget (h : A.Progress o c) (x : C.label d) {s m : ℕ} (hcs : c ≤ s) (hs : s ≤ m) (hm : m ≤ N) :
    size C d (A.run m x).x ≤ Real.exp (Work.D01.columnLogs C.path.levels m) * size C d (A.run s x).x := by
  induction m, hs using Nat.le_induction with
  | base => exact le_mul_of_one_le_left (size_nonneg _) (Real.one_le_exp (Work.D01.columnLogs_nonneg ..))
  | succ m hs ih =>
    have hx := (C.path.levels.params (m+1)).columns_ge
    rw [Work.D01.columnLogs_succ, Real.exp_add, Real.exp_log (zero_lt_one.trans_le hx)]
    refine (h.back m x (hcs.trans hs) hm).trans ((mul_le_mul_of_nonneg_left (ih (by omega)) (zero_le_one.trans hx)).trans_eq ?_)
    ring

theorem Progress.bijective (h : A.Progress o c) (hck : c ≤ k) (hkN : k ≤ N) : Bijective (fun v => (A.run k v).x) := by
  let f := (h.linear k hck hkN).mk' (fun v => (A.run k v).x)
  have hinj : Injective f := LinearMap.ker_eq_bot.mp <| LinearMap.ker_eq_bot'.mpr (fun v hv => by
    apply size_eq_zero
    have he := h.back_budget v hck hkN le_rfl
    rw [show (A.run k v).x=0 from hv,h.coordinate] at he; simpa only [size, Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,
      Finset.sum_const_zero,mul_zero] using he)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

variable (A)
open scoped Classical in
/-- At bad cutoffs irrelevant; keep total map by arbitrary padding. Avoids any
assumption except on the specified tails when using it. -/
def basisAt (k : ℕ) : C.label d ≃ₗ[ℂ] C.label d :=
  if h : IsLinearMap ℂ (fun v => (A.run k v).x) ∧ Bijective (fun v => (A.run k v).x) then
    LinearEquiv.ofBijective (h.1.mk' _) h.2 else LinearEquiv.refl _ _

variable {A}
lemma Progress.at_eq (h : A.Progress o c) (hck : c≤k) (hkN : k≤N) (v : C.label d) :
    A.basisAt k v = (A.run k v).x := by
  unfold basisAt; rw [dif_pos ⟨h.linear k hck hkN, h.bijective hck hkN⟩]; rfl

variable (C d N p) in
def home : Native C d N p := ⟨fun _ => 0,(C.factory d N p).entries⟩



end Native







/-- Supplied in weak comparison before product births. `coeff` is at `c` and site is
an input in fine coordinates (so the associated actual ancestors vary). No offset chosen
a posteriori by moving the node. -/
structure Bank4 (C : Family G) where
  atSite (N p : ℕ) (o : Site (C.side N p)) : Native C 4 N p
  coeff (N p : ℕ) (o : Site (C.side N p)) : Entry C →ₗ[ℂ] C.label 4

namespace Bank4
variable (Y : Bank4 C)

def raw (c : ℕ) (o : Site (C.side N p)) :=
  (((Y.atSite N p o).basisAt c).symm.toLinearMap).comp (Y.coeff N p o)





lemma budget (o : Site (C.side N p)) (h : (Y.atSite N p o).Progress o c) (hm : c ≤ k) (hk : k ≤ N) (j : Entry C) :
    size C 4 ((Y.atSite N p o).run k (Y.raw c o j)).x ≤
      Real.exp (Work.D01.columnLogs C.path.levels k)* size C 4 (Y.coeff N p o j) := by
  unfold raw; refine (h.back_budget _ le_rfl hm hk).trans_eq ?_
  rw [← h.at_eq le_rfl h.fits, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

structure Opened (F : Extraction.Order) (c : ℕ) : Prop where
  moves : F.late fun N p => ∀ o, (Y.atSite N p o).Progress o c
  fee : ∃ A : ℝ, 1 ≤ A ∧ F.late fun N p => ∀ o (j : Beans C), size C 4 (Y.coeff N p o (pod C j)) ≤ A

end Bank4
end YM.UVNext.Annulus
