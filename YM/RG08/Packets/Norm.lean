import YM.Pert.Bulk.Stacks -- `Folded` is the concrete arity packet predicate of this snapshot
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sup-root absolute prices

`Ticket` uses ENNReal stagewise (do not use bare real tsum without summability: it default-zeros
on nonsummable). On real analytic packets this is definally the fixed-order kernel estimate
`YM.Pert.Bulk.Folded`. It does not bind a norm on arbitrary physical densities.
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk
open scoped Topology ENNReal

set_option autoImplicit false
universe v w u
variable {J : Type v} {X : J → Type w} {Y : Type u} [NormedAddCommGroup Y]

abbrev Expense (X : J → Type w) := (j:J)→X j→ℝ
abbrev Sheet (X : J → Type w) (Y : Type u) := (j:J)→X j→Y

def stamp (y : Y) (x : ℝ) := ENNReal.ofReal (‖y‖*Real.exp x)

def earning (e : Expense X) (K : Sheet X Y) (j : J) := ∑'x:X j, stamp (K j x) (e j x)

def Ticket (e : Expense X) (K : Sheet X Y) (p : ℝ) := ∀ j, earning e K j ≤ ENNReal.ofReal p

/-- Sup-root numerical bill. Finite only on packets with a `Ticket`. Used in formal uniform
recurrences once that is shown. -/
def amount (e : Expense X) (K : Sheet X Y) := ENNReal.toReal (⨆ j:J, earning e K j)

variable {e e' : Expense X} {K T : Sheet X Y} {p q : ℝ}

theorem Ticket.uses (h : Ticket e K p) : Ticket e K (amount e K) := by
  intro j
  have he : (⨆ j:J, earning e K j) ≤ ENNReal.ofReal p := iSup_le h
  unfold amount
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top he)]
  exact le_iSup (earning e K) j

theorem Ticket.amount_le (h : Ticket e K p) (hp : 0 ≤ p) : amount e K ≤ p := by
  have he : (⨆ j:J, earning e K j) ≤ ENNReal.ofReal p := iSup_le h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal hp)

theorem amount_nonneg (e : Expense X) (K : Sheet X Y) : 0 ≤ amount e K := ENNReal.toReal_nonneg

theorem stamp_real (x t : ℝ) : stamp x t = bill x t := by rw [stamp, Real.norm_eq_abs]; rfl

theorem Ticket.point (h : Ticket e K p) (hp : 0 ≤ p) (j : J) (x : X j) : ‖K j x‖ * Real.exp (e j x) ≤ p := ENNReal.ofReal_le_ofReal_iff hp |>.mp ((ENNReal.le_tsum x).trans (h j))

theorem Ticket.below (h : Ticket e K p) (hp : 0 ≤ p) (he : ∀ j x, 0 ≤ e j x) (j : J) (x : X j) : ‖K j x‖ ≤ p :=
  (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (he j x))).trans (h.point hp j x)

theorem Ticket.norm_sum (h : Ticket e K p) (j : J) : Summable (fun x=> ‖K j x‖ * Real.exp (e j x)) := by
  have hh := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h j)
  exact (ENNReal.summable_toReal hh).congr fun x=> ENNReal.toReal_ofReal (by positivity)

theorem Ticket.unweighted (h : Ticket e K p) (he : ∀ j x, 0 ≤ e j x) (j : J) : Summable fun x=> ‖K j x‖ :=
  (h.norm_sum j).of_nonneg_of_le (fun _=> norm_nonneg _) fun x=> le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (he j x))

theorem Ticket.sum (h : Ticket e K p) (he : ∀ j x, 0 ≤ e j x) [CompleteSpace Y] (j : J) : Summable (K j) := (h.unweighted he j).of_norm

theorem Ticket.gives (h : Ticket e K p) (hp : 0 ≤ p) (j : J) :
    YM.RG.SumBudget (fun x => ‖K j x‖ * Real.exp (e j x)) p := by
  have he := h j
  unfold earning stamp at he
  have hh (x) : 0 ≤ ‖K j x‖ * Real.exp (e j x) := by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hh (h.norm_sum j)] at he
  exact ⟨hh,h.norm_sum j,(ENNReal.ofReal_le_ofReal_iff hp).mp he⟩

theorem stamp_mono {a b : Y} {u z : ℝ} (h : ‖a‖ ≤ ‖b‖) (he : u ≤ z) : stamp a u ≤ stamp b z := by unfold stamp; gcongr

theorem Ticket.mono (h : Ticket e K p) (he : e' ≤ e) (hT : ∀ j x, ‖T j x‖ ≤ ‖K j x‖) (hp : p ≤ q) : Ticket e' T q :=
  fun j=> (ENNReal.tsum_le_tsum fun x=>stamp_mono (hT j x) (he j x)).trans ((h j).trans (by gcongr))

theorem zero_ticket (e : Expense X) {p : ℝ} : Ticket e (fun _ _=> (0:Y)) p := fun j=> by simp [earning,stamp]

theorem stamp_add (a b : Y) (u : ℝ) : stamp (a+b) u ≤ stamp a u+stamp b u := by
  unfold stamp
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ‖a‖ * Real.exp u) (by positivity), ← add_mul]
  gcongr; exact norm_add_le a b

theorem Ticket.add (h : Ticket e K p) (ht : Ticket e T q) (hp : 0 ≤ p) (hq : 0 ≤ q) : Ticket e (fun j x=> K j x + T j x) (p+q) := by
  intro j
  calc earning .. ≤ ∑'x, (stamp (K j x) (e j x)+stamp (T j x) (e j x)) := ENNReal.tsum_le_tsum fun x=>stamp_add ..
       _ ≤ ENNReal.ofReal p+ENNReal.ofReal q := by rw [ENNReal.tsum_add]; exact add_le_add (h j) (ht j)
       _ = _ := (ENNReal.ofReal_add hp hq).symm

theorem Ticket.neg (h : Ticket e K p) : Ticket e (fun j x=> -K j x) p := h.mono (fun _ _=> le_refl _) (by simp) le_rfl

theorem Ticket.sub (h : Ticket e K p) (ht : Ticket e T q) (hp : 0 ≤ p) (hq : 0 ≤ q) : Ticket e (fun j x=> K j x - T j x) (p+q) := by
  simpa only [sub_eq_add_neg] using h.add ht.neg hp hq

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 Y]

theorem Ticket.smul (h : Ticket e K p) (c : 𝕜) : Ticket e (fun j x=> c • K j x) (‖c‖*p) := by
  intro j
  unfold earning stamp
  simp_rw [norm_smul, mul_assoc, ENNReal.ofReal_mul (norm_nonneg c), ENNReal.tsum_mul_left]
  gcongr
  exact h j

variable {α : Type} {r : ℕ}

def charge (α : Type) (r : ℕ) (σ : ℝ) : Expense (J:=Market α) (fun _=> Fin r →Market α) := fun j x=> σ * expense j x

theorem charge_nonneg {σ : ℝ} (hs : 0 ≤ σ) (j : Market α) (x : Fin r→Market α) : 0 ≤ charge α r σ j x := mul_nonneg hs (expense_nonneg ..)

theorem ticket_folded (σ p : ℝ) (K : Packet r α) : Ticket (charge α r σ) K p ↔ Folded σ K p := by simp only [charge,Folded,Ticket,earning,stamp_real]

end YM.RG08.Packets
