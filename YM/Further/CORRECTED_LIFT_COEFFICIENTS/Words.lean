import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Original
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Wick
import YM.Push.FINITE_DETECTION.Generators
import YM.Push.FINITE_DETECTION.Variables

/-!
# `CellBank` price side: the finite Wick calibration reads of these sources

All p and all supplied matrices indexed literally by face (torus!) and
color in the physical conventions of C. P_0 construction itself not
part of this operation, which works with ANY such matrix. Application to
free propagation and actual Estimate producers will of course need the
correct one, installed on exactly these N,p, not pretending independence
across holonomy slots that have the same suppressed curvature read. No
precision/vector inverse on a changing rank.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Source Source.Drops Labels Next.Extract Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {d m p N t l : ℕ}

namespace Loop



end Loop

abbrev Dial (G : Gauge) (n : Side) := Face (Per n) × G.ColorIndex

structure Copper (G : Gauge) (n : Side) where
  P : Dial G n → Dial G n → ℝ
  symm a b : P a b=P b a

namespace Screen
variable (B : Screen C m p t)

def wireLeg (b : B.Bit) : Dial G (C.side m p) :=
    ((wrap _ (B.leg b.1).offset,(B.leg b.1).plaq), b.2)

variable (Q : Copper G (C.side m p))

def cost (w : B.Word l) (a : Loop.Pair l) : ℂ := Q.P (B.wireLeg (w a.1)) (B.wireLeg (w a.2))

def toll (N : ℕ) (w : B.Word l) (a : Loop.Pair l) : ℂ := (ratio C m N p:ℂ)^2 * B.cost Q w a

-- Evaluate ordinary tensor as linear-array polynomial in Y = k/g
-- (this is after all transports are suppressed).




/-- Linear cells tested on *all* Snap directions. Construct Pol by
expanding ramp with singleton slot, no projection quotient used. -/
def line (d : ℕ) (b : B.Bit) := (EuclideanSpace.proj b.2).comp (Blurb C.params d (B.leg b.1))

def slotPoly (d : ℕ) (b : B.Bit) : Pol G :=
    ∑ j : Fin (d-1), Push.FiniteDetection.Generators.leg ((B.line d b).toLinearMap.comp (LinearMap.single ℝ (fun i : Fin (d-1) => Taylor G i.val) j))

lemma read_slot (b : B.Bit) (d : ℕ) (J : Jet G) : Labels.read J (B.slotPoly d b) =
    (↑(B.line d b (trunk d J)) : ℂ) := by
  unfold slotPoly; rw [map_sum]
  simp_rw [Push.FiniteDetection.Generators.leg_at]; rw [← Complex.ofReal_sum]
  congr 1
  let T (i : Fin (d-1)) := LinearMap.single ℝ (fun j : Fin (d-1) => Taylor G j.val) i
  change ∑ j : Fin (d-1), (B.line d b) (T j (J j.val))= _
  rw [←map_sum]; apply congr_arg (B.line d b); ext1 i; simp [Finset.sum_apply,T,trunk]



def string (d : ℕ) (q : ℝ) (w : B.Word l) (A : Loop.Pairs l) : Pol G :=
    ∏ i∈Loop.loose Finset.univ A, (q:ℂ) • B.slotPoly d (w i)

def meters (q : ℝ) (d N : ℕ) (w : B.Word l) : Pol G :=
    ∑ A∈Loop.joins (Finset.univ (α:=Fin l)), (∏ a∈A, B.toll Q N w a) • B.string d q w A

def rows (q : ℝ) (v : C.label d) (N : ℕ) : Pol G := ∑ w : B.All, notes B v N w.2 • B.meters Q q d N w.2

def mapper (h : C.Makes) (e : Resolution C d N B) (q : ℝ) : C.label d →ₗ[ℂ] Pol G :=
    ∑ w : B.All, (LinearMap.toSpanSingleton ℂ _ (B.meters Q q d N w.2)).comp
      (B.record h e (Nat.le_of_lt_succ w.1.isLt) w.2).toLinearMap

lemma scanned (h : C.Makes) (e : Resolution C d N B) (q : ℝ) (v : C.label d) :
    B.mapper Q h e q v = B.rows Q q v N := by
  unfold mapper; rw [LinearMap.sum_apply]; exact Finset.sum_congr rfl fun w _ => rfl

-- raw read WITHOUT the threshold weights. By occurrence degree,
-- tested normalization of the assigned Wick inputs.



theorem rows_unit (h : C.Makes) (e : Resolution C d N B) (r : ℝ) : B.rows Q r (C.refUnit d) N=1 := by
  classical
  let f : B.Word 0 := Fin.elim0
  let w : B.All := ⟨0,f⟩
  unfold rows; rw [Finset.sum_eq_single w]
  · rw [unit_coefficient h e (Nat.le_of_lt_succ w.1.isLt) w.2,if_pos (show w.1.val=0 from rfl),one_smul]
    unfold meters; rw [Finset.sum_eq_single ∅]
    · change (_ : ℂ) • B.string d r f ∅=_
      simp [string]
    · intro b _ hb; exact (hb ((show (b : Loop.Pairs 0)=∅ from Subsingleton.elim (α:=Loop.Pairs 0) b ∅))).elim
    exact fun he => False.elim (he (Loop.empty_in _))
  · rintro ⟨l,F⟩ _ hl
    rw [unit_coefficient h e (Nat.le_of_lt_succ l.isLt)]
    rw [if_neg,zero_smul]
    intro hh
    obtain rfl : l=0 := Fin.ext hh
    exact hl (congr_arg (Sigma.mk 0) (show F=f from Subsingleton.elim (α:=B.Word 0) F f))
  simp
end Screen
end YM.Further.CorrectedLift
