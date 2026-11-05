import YM.Next.FOUNDATIONS.SU2
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Work.G08
import YM.Work.G09

/-!
# Optional quantitative gate for using the same equation projectors

This is NOT needed to prove the norm bound (`affordable`). But subsequent
steps may have to take a vector *in* the finite kernel and use it as a
combination of the equation columns with control on the coefficients. Rank
also requires more than projector boundedness.

Give a precise *sufficient*
finite singular-value estimate in the reference frame of this family, with
the **top cost** (`terminal.symm` as in `dollar`) on the output. Derive it
under top-matrix and signed transfer hypotheses. These are missing
estimates. In particular the smallness of the signed top coordinate
difference is NOT assumed here from the equality of bottom coordinates. Use
Duet on the *actual* family with its `direction` and bank estimates; state
the precise Woke budget needed, then use the cone and cost theorems. Not a
construction of Woke data!
-/

set_option autoImplicit false
noncomputable section

namespace YM.Push.CutoffProjectors
open Function Filter Next.Extract Extraction Lattice RG Bid Labels MeasureTheory
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {N p d : ℕ}

namespace Packet
variable (E : Packet C d N p)

/-- Exact quantitative hypothesis on the finite matrix,
`σ_min(top PRIMARY coordinates as function of equation parameters) ≥ c`,
in the fixed Hermitian metric from Frame. Norms inside chart are ℓ².
Meant even if I_d = 0 (inequality vacuous). Γ costs in Woke (and in the
cutoff norm estimates for `dollar`) are in different norms; compare below.
No assertion that an arbitrary presentation's reference step has singular
values bounded away from degeneracy in any other coordinates. -/
def Separation (c : ℝ) : Prop := 0 < c ∧ ∀ x : equationSpace (C.labels.level d),
    c * ‖chart (C.labels.level d) (x : C.label d)‖ ≤ ‖chart (C.labels.level d) (E.costMatrix x)‖

variable {E}

/-- Directly useful in RelayCosts.mark (measure the top cost). -/
theorem Separation.lift_bound {c : ℝ} (h : E.Separation c) (x : equationSpace (C.labels.level d)) :
    ‖x‖ ≤ (fee (C.labels.level d)/c) * ‖(C.factory d N p).terminal.symm (E.reference x)‖ := by
  let F := C.labels.level d
  have ht : ‖chart F (x:F.Coeff)‖ ≤ ((1+‖chart F‖) * ‖E.costMatrix x‖)/c := by
    rw [le_div_iff₀ h.1, mul_comm]; exact (h.2 x).trans (chart_norm_le F _)
  calc
    _ ≤ _ := norm_chart F (x : F.Coeff)
    _ ≤ (1+‖unchart F‖) * (((1+‖chart F‖) * ‖E.costMatrix x‖)/c) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by
      change _ = (fee F/c) * ‖E.costMatrix x‖
      unfold fee; ring

theorem Separation.injective {c : ℝ} (h : E.Separation c) : Injective E.reference := by
  intro u v huv
  have hb := h.lift_bound (u-v)
  rw [map_sub, huv, sub_self, map_zero, norm_zero, mul_zero] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))



abbrev Couple (C : Family G) (d N p : ℕ) := Duet C.path (C.labels.level d) N p (C.ref d) N

/-- State the actual signed comparison (including equality of functions on
links, not just numbers). Sign primary minus J. E's subtraction of the
representation itself may and will need more receipts than this, notably for
mixing & cost of masks. -/
def Subtracts (E : Packet C d N p) (P : Couple C d N p) (x : equationSpace (C.labels.level d)) :=
  ∀ m : ℕ, C.ref d ≤ m → m ≤ N →
  let r := C.path.rep N p m
  let B := C.localSection d
  let Q := (C.factory d N p).entries m (E.costMatrix x)
  let J := E.chain m x
  P.atPoint m = 0 ∧ (P.voice m).density 0 B r = Q.density 0 B r - J.density 0 B r ∧
    (P.voice m).x = Q.x - J.x

/-- Exact demand, for origin mapping at N,p. Budget ties to J's own top
coordinate norm; the coefficient 8 chosen to allow an explicit 1/2 result.
`columns` here is the actual purchased price. This is a version where
**choosing** pre/post L & columns, etc. must really pay enough for Woke.
Not asserting sufficiency of E's scheduling. -/
def Compares (E : Packet C d N p) (W : Worth) := ∀ x : equationSpace (C.labels.level d),
    ∃ (P : Couple C d N p) (b : ℝ), E.Subtracts P x ∧ P.Woke C.params W (C.localSection d) b ∧
      0 ≤ b ∧ b ≤ 8 * (1 + (C.path.levels.params N).columns) *
        (C.labels.level d).coeffSize (E.topEquation x)

/-- From Woke & Bank on THIS signed transfer. -/
theorem Compares.smaller {W : Worth} (h : E.Compares W) (hb : Bank W C.path.levels)
    (hr : roomCost C.path.levels W) (hm : C.Makes) (x : equationSpace (C.labels.level d)) :
    let F := C.labels.level d
    F.coeffSize (E.costMatrix x-E.topEquation x) ≤ F.coeffSize (E.topEquation x)/2 := by
  let A := (C.path.levels.params N).columns
  obtain ⟨P,b,hP,he,hv,hh⟩ := h x
  have H := he.basic.1
  have htop : (P.voice N).x = E.costMatrix x - E.topEquation x := by
    have ht := (hP N H le_rfl).2.2
    rw [ht]
    rw [(hm.calibrated d N p H).bare_coord]
    rfl
  let F := C.labels.level d
  have hA : 1 ≤ A := (C.path.levels.params _).columns_ge
  have h0 : 0 < 32*(1+A)^2 := by nlinarith
  have ht := ((Work.G09.cone_cost hr hb he N H le_rfl).1).trans (Work.G09.cost_finest hr hb he)
  rw [htop] at ht
  apply le_of_mul_le_mul_left _ h0
  calc
    _ ≤ 2*(1+A) * b := ht
    _ ≤ 2*(1+A)*(8*(1+A)*F.coeffSize (E.topEquation x)) := mul_le_mul_of_nonneg_left hh (by linarith)
    _ = _ := by ring

/-- The corresponding least-value bound on `topEquation` would not by
itself tell us the rank of *reference*. Need the comparison. `δ` here uses
actual sup norms (not chart norm). -/
def TopFloor (E : Packet C d N p) (δ : ℝ) := 0 < δ ∧
    ∀ x : equationSpace (C.labels.level d), δ * ‖x‖ ≤ ‖E.topEquation x‖

section Sizes
open Work.G08

variable (F : Labels.Frame G d)

theorem norm_le_size (x : F.Coeff) : ‖x‖ ≤ F.coeffSize x := by
  apply (pi_norm_le_iff_of_nonneg (size_nonneg F x)).2
  exact fun i => Finset.single_le_sum (f:=fun i => ‖x i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem size_le_norm (x : F.Coeff) : F.coeffSize x ≤ (Fintype.card F.Index : ℝ) * ‖x‖ := by
  simpa only [Labels.Frame.coeffSize, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G := fun _ : F.Index => ℂ) x

/-- Constant for converting a TopFloor value. -/
def loss : ℝ := (2:ℝ) * (Fintype.card F.Index : ℝ) * fee F

lemma loss_pos : 0 < loss F := by
  have he : 1 ≤ fee F := fee_one_le F
  unfold loss; have : 0 < fee F := lt_of_lt_of_le zero_lt_one he
  positivity

theorem TopFloor.separation {δ : ℝ} {W : Worth} (h : E.TopFloor δ) (hh : E.Compares W)
    (hb : Bank W C.path.levels) (hr : roomCost C.path.levels W) (hm : C.Makes) :
    E.Separation (δ / loss (C.labels.level d)) := by
  let F := C.labels.level d
  let n : ℝ := Fintype.card F.Index
  refine ⟨div_pos h.1 (loss_pos _), fun x => ?_⟩
  have htop := hh.smaller hb hr hm x
  let M := E.costMatrix x
  let T := E.topEquation x
  have ht : F.coeffSize T ≤ 2 * F.coeffSize M := by
    change F.coeffSize (M-T) ≤ F.coeffSize T/2 at htop
    rw [size_sub_rev F] at htop
    linarith [size_triangle F T M]
  have hu : 0 ≤ 2*n := by dsimp [n]; positivity
  have H : δ*‖x‖ ≤ 2*n*((1+‖unchart F‖)*‖chart F M‖) := calc
    δ*‖x‖ ≤ F.coeffSize T := (h.2 x).trans (norm_le_size F T)
    _ ≤ _ := ht
    _ ≤ 2*n*‖M‖ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (size_le_norm F M) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_chart F M) hu
  change _ * ‖chart F (x:F.Coeff)‖ ≤ ‖chart F M‖
  rw [div_mul_eq_mul_div, div_le_iff₀ (loss_pos F)]
  calc
    _ ≤ δ * ((1+‖chart F‖)*‖x‖) := mul_le_mul_of_nonneg_left (chart_norm_le F x) h.1.le
    _ = (1+‖chart F‖)*(δ*‖x‖) := by ring
    _ ≤ (1+‖chart F‖)*(2*n*((1+‖unchart F‖)*‖chart F M‖)) := mul_le_mul_of_nonneg_left H (by positivity)
    _ = ‖chart F M‖ * loss F := by unfold loss fee; dsimp [n]; ring
end Sizes

end Packet

/-!
A common stronger way to certify TopFloor: top initial read near a fixed
triangular model T. Include triangularity in the coefficient frame, no
assumption about *interacting* continuum dimension.
-/

abbrev Model (F : Labels.Frame G d) := equationSpace F →L[ℂ] F.Coeff

def triangular {F : Labels.Frame G d} (T : Model F) := ∀ x : equationSpace F, ∀ i,
    (∀ j : F.Index, (F.grades j).1 < (F.grades i).1 → (x : F.Coeff) j = 0) → T x i = (x : F.Coeff) i

lemma triangular_injective {F : Labels.Frame G d} (T : Model F) (h : triangular T) : Injective T := by
  have hu x (hx : T x = 0) : x = 0 := by
    have he (n : ℕ) : ∀ i, (F.grades i).1 = n → (x:F.Coeff) i = 0 := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro i hi
        exact (h x i (fun j hj => ih _ (hi ▸ hj) j rfl)).symm.trans (congr_fun hx i)
    exact Subtype.ext (funext fun i => he _ i rfl)
  intro x y he
  exact sub_eq_zero.mp (hu (x-y) (by rw [map_sub, he, sub_self]))

def Floor {F : Labels.Frame G d} (T : Model F) (c : ℝ) := 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖

theorem has_floor {F : Labels.Frame G d} (T : Model F) (hi : Injective T) : ∃ c, Floor T c := by
  obtain ⟨B,hB⟩ := LinearMap.exists_leftInverse_of_injective T.toLinearMap (LinearMap.ker_eq_bot.mpr hi)
  let P := B.toContinuousLinearMap
  have he (x) : P (T x) = x := LinearMap.congr_fun hB x
  let c := 1+‖P‖
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c⁻¹,(inv_pos.mpr hc), fun x => ?_⟩
  rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hc, mul_comm]
  nth_rw 1 [← he x]
  exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith) (norm_nonneg _))

lemma Floor.perturb {E : Packet C d N p} {c : ℝ} {T : Model (C.labels.level d)}
    (h : Floor T c) (he : ‖E.topEquation - T‖ ≤ c/2) : E.TopFloor (c/2) := by
  refine ⟨half_pos h.1, fun x => ?_⟩
  have hi := ((E.topEquation - T).le_opNorm x).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  change ‖E.topEquation x - T x‖ ≤ _ at hi
  rw [norm_sub_rev] at hi
  linarith [norm_sub_norm_le (T x) (E.topEquation x), h.2 x]
end YM.Push.CutoffProjectors
