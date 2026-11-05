import YM.Source.Local
import YM.RG.History

/-!
# Exact reference-scale readout and normalized cylinders

eq:Jma, eq:pcone. Store *one choice* of exact
inserted-density representation (with estimates) at origin, all coords
and remainder entries. This is coefficient reading, **not** fitting a
conditional expectation at the next scale. Translates use origin's coefficients.

Keep exact equality of full λ coefficient on same history with same unmarked
branch. Equality is denotational; no unique presentations demanded and no
term-rewriting algorithm prescribed. Pad alphabet with unused addresses as needed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Source

open Labels RG Lattice Wilson Function Set
open MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {n : Side} {G : Gauge} {d : ℕ} {F : Frame G d}

structure Coefficient (F : Frame G d) (n : Side) where
  x : F.Coeff
  support : ℕ → Support n
  regular : ℕ → Config G n → ℂ
  forced : ℕ → Config G n → ℂ

namespace Coefficient
variable (P : Coefficient F n)

def maskedTerm (R : Rep G n) (i : ℕ) := masked R.p.threshold (P.support i) (P.regular i)

def exponentialEntry (o : Site n) (C : SectionData F) (R : Rep G n) (U : Config G n) : ℂ :=
  P.x 0 + masked R.p.threshold (C.footprint o)
    (C.places (F.scaled (R.p.threshold)⁻¹ (F.core P.x)) o) U + ∑' i, P.maskedTerm R i U

open scoped Classical in
def marked (R : Rep G n) (b : Finset ℕ) (U : Config G n) : ℂ :=
  if R.activities.admissible R.p U b then
    ∑ i ∈ b, P.forced i U * ∏ j ∈ b.erase i, (R.activities.K j U : ℂ)
  else 0

/-- eq:Jma spelled out with `λ²=0`; constant is `R.eval`. -/
def density (o : Site n) (C : SectionData F) (R : Rep G n) (U : Config G n) : ℂ :=
  (R.eval U : ℂ) * P.exponentialEntry o C R U +
    ((Real.exp (R.exponent U)) : ℂ) * ∑' b, P.marked R b U

structure Format (o : Site n) (A : Hol G) (R : Rep G n) : Prop where
  smooth (i : ℕ) : R.p.Regular (P.support i) (P.regular i)
  origin (i : ℕ) : o ∈ P.support i
  identity_null (i : ℕ) : P.regular i 1 = 0
  projects (i : ℕ) : Nonwrapping (P.support i) o → A.PiVanish d o (P.regular i)
  forcing (i : ℕ) (U : Config G n) : P.forced i U ≠ 0 → (R.activities.forced i).eligible R.p.threshold U
  carried (i : ℕ) : P.forced i ≠ 0 → o ∈ (R.activities.forced i).support
  invariant (i : ℕ) : GaugeInvariant (P.forced i)
  supported (i : ℕ) : UsesFinal R.p.threshold (R.activities.forced i).support (P.forced i)
  borel (i : ℕ) : Measurable (P.forced i)

def remBound (o : Site n) (R : Rep G n) (varkappa budget : ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a+b ≤ budget ∧ 0 < varkappa ∧
    (∃ e : ℕ → ℝ, SumBudget (fun i ↦ R.p.mass (P.support i) (e i)) a ∧
      ∀ i, R.p.supBounds o (P.support i) (P.regular i) (e i)) ∧
    (∃ e : ℕ → ℝ, SumBudget (fun i ↦ R.p.mass (R.activities.forced i).support (e i)) (varkappa*b) ∧
      ∀ i, 0 ≤ e i ∧ ∀ U, ‖P.forced i U‖ ≤ e i)
end Coefficient

/-- One family of transfers at cutoff `(N,p,d)`. All placements down to ref
stem from the origin. -/
structure TransferData (F : Frame G d) (H : RG.History G) (N p : ℕ) where
  entries : ∀ m, F.Coeff → Coefficient F (H.S.side m p)
  terminal : F.Coeff ≃ₗ[ℂ] F.Coeff

def initial (C : SectionData F) (H : RG.History G) (N p : ℕ) (v : F.Coeff)
    (o : Site (H.S.side N p)) : Config G (H.S.side N p) → ℂ :=
  ((H.S.a N : ℂ)^d)⁻¹ • C.places (F.scaled (H.levels.clock.threshold N)⁻¹ v) o

/-- Vector of the physical unit at level m. -/
def unitVec (F : Frame G d) (H : RG.History G) (m : ℕ) := ((H.S.a m : ℂ)^d) • F.e0

namespace TransferData
variable {H : RG.History G} {N p : ℕ} (T : TransferData F H N p)

def cylinder (C : SectionData F) (v : F.Coeff) := initial C H N p (T.terminal.symm v)

structure Based (A : Hol G) (C : SectionData F) (r : ℕ) : Prop where
  ref : r ≤ N
  format : ∀ m, r ≤ m → m ≤ N → ∀ v, (T.entries m v).Format 0 A (H.rep N p m)
  cap : ∀ m, r ≤ m → m ≤ N → ∀ v,
    (T.entries m v).remBound 0 (H.rep N p m) (Real.sqrt (H.levels.clock.forcedAllowance m))
      ((H.levels.params m).columns * F.coeffSize (F.core (T.entries m v).x))
  back : ∀ m, r ≤ m → m < N → ∀ v,
    F.coeffSize (T.entries (m+1) v).x ≤ (H.levels.params (m+1)).columns * F.coeffSize (T.entries m v).x
  front : ∀ m, r ≤ m → m < N → ∀ v,
    F.coeffSize (T.entries m v).x ≤ (H.levels.params (m+1)).columns * ((H.S.block m).val : ℝ)^d *
      F.coeffSize (T.entries (m+1) v).x
  linear : ∀ m, r ≤ m → m ≤ N →
    IsLinearMap ℂ (fun v => (T.entries m v).x) ∧ IsLinearMap ℂ (fun v => (T.entries m v).regular) ∧
    IsLinearMap ℂ (fun v => (T.entries m v).forced) ∧ ∀ v, (T.entries m v).support = (T.entries m 0).support
  bare_coord v : (T.entries N v).x = v
  bare_germ v : (T.entries N v).regular = 0
  encode v U : (T.entries N v).density 0 C (H.rep N p N) U =
    ((H.S.a N : ℂ)^d) * ((H.rep N p N).eval U : ℂ) * initial C H N p v 0 U
  unnormalized m : r ≤ m → m < N → ∀ v,
    (T.entries m v).density 0 C (H.rep N p m) =
      ((H.S.block m).val : ℂ)^d • (H.levels.clock.op m p).push (H.β N p (m+1))
        ((T.entries (m+1) v).density 0 C (H.rep N p (m+1)))
  reads v : (T.entries r v).x = T.terminal v
  unit_coord m : r ≤ m → m ≤ N → (T.entries m (unitVec F H N)).x = unitVec F H m
  realForm v : T.terminal (star v) = star (T.terminal v)
  orients (k : Signed) v : T.terminal (F.act k.ortho v) = F.act k.ortho (T.terminal v)

/-- Literal translate, no covariance in a changed auxiliary hierarchy
needed for this. -/
theorem cylinder_shift (C : SectionData F) (v : F.Coeff) (o b : Site (H.S.side N p)) U :
    T.cylinder C v (o+b) U = T.cylinder C v o (translate b U) := by simp [cylinder,initial]

theorem origin_unit {A : Hol G} {C : SectionData F} (h : C.Sound A) (r : ℕ) (hb : T.Based A C r)
    (b : Site (H.S.side N p)) : T.cylinder C (unitVec F H r) b = 1 := by
  have he : T.terminal.symm (unitVec F H r) = unitVec F H N := calc
    _ = T.terminal.symm (T.terminal (unitVec F H N)) := congr_arg _
      (((hb.unit_coord r le_rfl hb.ref).symm).trans (hb.reads _))
    _ = _ := T.terminal.symm_apply_apply _
  rw [cylinder,he,initial,unitVec,map_smul,F.scaled_unit]
  funext U
  rw [Pi.smul_apply, SectionData.places, C.eval_linear.map_smul]
  simp [h.unit, (H.S.a_pos N).ne']
end TransferData
end YM.Source
