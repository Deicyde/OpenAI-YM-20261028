import YM.Push.CUTOFF_PROJECTORS.Spectral
import YM.Work.D01

/-!
# Lift the actual step-kernel candidates on budget

Optional gates for the estimates needing equation columns. Use the
singular-value gate with the *unscaled* equation parameter norm, pass
from the actual `Bid.dollar` on this Family, including for arbitrary
(unbounded) admissible rows. Also see what the budget hypotheses used
earlier to obtain the margin through `Compares` give in terms of propagation
bounds on the very same signed discrepancy Duet. This is at the origin; not
a construction of Duet, all required offsets, or the decisive `close`
replica estimates for Relay from these propagation costs. Keep rates on
ordered tails; no stronger period uniformity from a dollar estimate. In
particular we don't assert the step preserves dollar!
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors
open Filter Function Extraction Next.Extract Bid RG Labels Wilson
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {A : Campaign C} {d N p : ℕ} {f : Order}

/-- Sub-exponential price on ordered tails. -/
def Subexp (C : Family G) (f : Order) (K : ℕ → ℕ → ℝ) := ∀ ε : ℝ, 0 < ε → f.late fun N p =>
  K N p ≤ Real.exp (ε * C.S.scale N)

variable {K L : ℕ → ℕ → ℝ}

lemma Subexp.mono (h : Subexp C f K) (he : f.late fun N p => L N p ≤ K N p) : Subexp C f L := by
  intro ε hε
  exact ((h ε hε).and he).mono fun i hi => (hi.1.and hi.2).mono fun j hj => hj.2.trans hj.1

lemma Subexp.mul (h : Subexp C f K) (he : Subexp C f L) (hl : ∀ N p, 0 ≤ L N p) :
    Subexp C f fun N p => K N p * L N p := by
  intro ε hε
  refine ((h _ (half_pos hε)).and (he _ (half_pos hε))).mono fun i hi =>
    (hi.1.and hi.2).mono fun j hj => (mul_le_mul hj.1 hj.2 (hl _ _) (Real.exp_pos _).le).trans_eq ?_
  rw [← Real.exp_add]; congr 1; ring

lemma subexp_const (C : Family G) (f : Order) (c : ℝ) : Subexp C f (fun _ _ => c) := by
  intro ε hε
  have h := (Real.tendsto_exp_atTop.comp (C.S.divergent.const_mul_atTop hε)).eventually_ge_atTop c
  exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually h

abbrev rates (C : Family G) (N : ℕ) : ℝ := (C.path.levels.params N).columns

/-- Column comparison uses the calendar on the very same C. -/
lemma subexp_columns (C : Family G) (f : Order) : Subexp C f fun N _ => 1 + rates C N := by
  let K := rates C
  have hk i : 1 ≤ K i := (C.path.levels.params i).columns_ge
  have h : Subexp C f fun N _ => K N := by
    intro ε hε
    have hh : ∀ᶠ N : ℕ in atTop, K N ≤ Real.exp (ε*C.S.scale N) := by
      filter_upwards [eventually_ge_atTop 1, Work.D01.columnLogs_le C.path.levels ε hε] with N hN hL
      cases N with
      | zero => omega
      | succ n =>
        have hu : Real.log (K (n+1)) ≤ ε*C.S.scale (n+1) := by
          rw [Work.D01.columnLogs_succ] at hL
          exact le_trans (le_add_of_nonneg_left (Work.D01.columnLogs_nonneg C.path.levels n)) hL
        exact (Real.exp_log (lt_of_lt_of_le zero_lt_one (hk _))) ▸ Real.exp_le_exp.mpr hu
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually hh
  have he := (subexp_const C f 2).mul h (fun N _ => zero_le_one.trans (hk _))
  refine he.mono (Eventually.of_forall fun i => Eventually.of_forall fun j => ?_)
  change 1+K _ ≤ 2*K _
  linarith [hk (f.mesh j)]

namespace Campaign

/-- Rows of expansion coefficients. -/
abbrev Descriptions (C : Family G) (d : ℕ) := (u : ℕ × ℕ) → equationSpace (C.labels.level d)

def fromRow (A : Campaign C) (w : Descriptions C d) : Bid.Rowe C d :=
  fun u => (A.packet d u.1 u.2).reference (w u)

def costAt (A : Campaign C) (w : Descriptions C d) (N p : ℕ) : C.label d :=
  (A.packet d N p).costMatrix (w (N,p))

def equationTrial (A : Campaign C) (w : Descriptions C d) : Extraction.Lease.Trial C :=
  fun N p o U => (A.packet d N p).J (w (N,p)) o U









/-- Top bound from the comparison budgets; in fact this part doesn't
use the singular value bound. -/
theorem top_budget {W : Worth} (hb : Bank W C.path.levels) (he : roomCost C.path.levels W)
    (hh : f.late fun N p => (A.packet d N p).Compares W) (w : Descriptions C d)
    (h : Bid.dollar C f (A.fromRow w)) : Subexp C f fun N p =>
      (C.labels.level d).coeffSize ((A.packet d N p).topEquation (w (N,p))) := by
  let F := C.labels.level d
  have hr : Subexp C f (fun N p => ‖A.costAt w N p‖) := h
  refine ((subexp_const C f (2*(Fintype.card F.Index : ℝ))).mul hr (fun _ _ => norm_nonneg _)).mono ?_
  refine hh.mono fun k hk => hk.mono fun j hj => ?_
  let N := f.mesh j
  let p := f.per k
  let T := (A.packet d N p).topEquation (w (N,p))
  let M := A.costAt w N p
  have ht := hj.smaller hb he A.cutoff (w (N,p))
  change F.coeffSize (M-T) ≤ F.coeffSize T/2 at ht
  rw [Work.G08.size_sub_rev F] at ht
  change F.coeffSize T ≤ 2*(Fintype.card F.Index : ℝ)*‖M‖
  have hu := Packet.size_le_norm F M
  linarith [Work.G08.size_triangle F T M]


end Campaign
end YM.Push.CutoffProjectors
