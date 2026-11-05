import YM.WilsonBulk.Heat.Devices
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Conditioning by unit-time Gaussian flow (cover omits the scalar)

Power of heat time = number of internal pairings; no continuous PDE is
solved in code. Coefficientwise ∂t equation gives a triangular recursion.
`receive` with X any type for per-volume comparisons. `cashless=true` discards
constants even at initialization; at X=infinite and translation-invariant
this prevents *every* evaluation of a volume-infinite scalar sum as an
operation in the prescription. For finite X, `cashless=false` recovers all
the interaction scalar jets too. Even though a discarded step may be
formalized using an `ite`, we never norm-estimate absolute summability of
such cover rank-zero scalars or use their `.ite` others.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Finset Lattice Laurent Bloch Filter
variable {X α : Type} {n m i j e : ℕ}

abbrev Split (e : ℕ) := {p // p ∈ antidiagonal e}
abbrev l {e : ℕ} (p : Split e) := p.val.1
abbrev r {e : ℕ} (p : Split e) := p.val.2
lemma parts (p : Split e) : l p + r p=e := mem_antidiagonal.mp p.property
lemma left_small (p : Split e) : l p ≤ e := by have he:= parts p; omega
lemma right_small (p : Split e) : r p ≤ e := by have he:= parts p; omega

abbrev Frames (X : Type) := (n:ℕ)→Page X n
abbrev Record (X : Type) := ℕ→ Frames X -- coupling powers first
def torpedo (G : Page X 2) (E : ℕ→ Record X) (d e n : ℕ) (i : Split e) (j : Split d) (k : Split n) : Page X n :=
    escort (finCongr (parts k)) (bridge G (E (l j) (l i) (l k+1)) (E (r j) (r i) (r k+1)))

def immerse (G : Page X 2) (I : Record X) (cashless : Bool) : ℕ→ Record X
| 0,e,n => if n=0 ∧ cashless then 0 else I e n
| t+1,e,n => if n=0 ∧ cashless then 0 else ((t+1:ℕ):ℝ)⁻¹ • (
      lap G (immerse G I cashless t e (n+2)) +
      ∑ i : Split e,∑ j : Split t,∑ k : Split n, escort (finCongr (parts k)) (bridge G
        (immerse G I cashless (l j) (l i) (l k+1)) (immerse G I cashless (r j) (r i) (r k+1))))
termination_by t _ _ => t
decreasing_by all_goals first| exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (left_small _) | exact Nat.lt_succ_of_le (right_small _)

def spend (e : ℕ) := Finset.range (3*e+1)
def receive (G : Page X 2) (I : Record X) (cashless : Bool) : Record X := fun e n=>
  ∑ t∈spend e, immerse G I cashless t e n
section contract
variable (G : Page X 2) {I : Record X} (cashless : Bool)
-- efficient API to reduce repetitive heartbeats
@[simp] lemma start (e n : ℕ) : immerse G I cashless 0 e n= if n=0 ∧ cashless then 0 else I e n := by rw [immerse]
lemma restore (d e n : ℕ) : immerse G I cashless (d+1) e n=
    if n=0 ∧ cashless then 0 else ((d+1:ℕ):ℝ)⁻¹ • (lap G (immerse G I cashless d e (n+2))+∑ i : Split e,∑ j : Split d,∑ k : Split n,torpedo G (immerse G I cashless) d e n i j k) := by
  rw [immerse]; rfl
lemma cashless_at (d e : ℕ) : immerse G I true d e 0=0 := by cases d <;> simp [restore]
lemma noCash (e : ℕ) : receive G I true e 0=0 := by simp [receive,cashless_at]

lemma congr_through {I' : Record X} (p : ℕ) (hi : ∀ e ≤ p,∀ n>0,I e n=I' e n) (b : Bool) (t e n) (he : e ≤ p) (hn : n≠0) :
    immerse G I cashless t e n=immerse G I' b t e n := by
  induction t using Nat.strong_induction_on generalizing e n with
  | h t ih =>
     cases t with
     | zero => simp only [start,hn,false_and,↓reduceIte]; exact hi e he n (by omega)
     | succ t =>
        rw [restore, restore]; simp only [hn,false_and,↓reduceIte]
        rw [ih t (by omega) e (n+2) he (by omega)]; congr 2 -- may descend too far
        refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> sum_congr rfl fun k _=> ?_
        unfold torpedo; rw [ih (l j) ((left_small j).trans_lt (by omega)) _ _ ((left_small i).trans he) (by omega), ih (r j) ((right_small j).trans_lt (by omega)) _ _ ((right_small i).trans he) (by omega)]

-- no order zero interaction and rank cap
def Free (I : Record X) := (∀ n,I 0 n=0)
def FrameBound (I : Record X) := ∀ e n,e+2<n→ I e n=0
def Based (I : Record X) := ∀ e n,Regular (I e n)
def Alternating (I : Record X) := ∀ e n, e % 2 ≠ n % 2 → I e n=0
-- conditional no-usage truncation
lemma query {U V : Frames X} {G : Page X 2} {h : ℕ} (e : Split h) :
    (l e+r e=h) ∧ (U (l e+1)=0 ∨ V (r e+1)=0 → escort (finCongr (parts e)) (bridge G (U (l e+1)) (V (r e+1)))=0) :=
  ⟨parts e, fun H=> by rcases H with h|h <;> simp [h]⟩
lemma torpedo_zero {E : ℕ→ Record X} (i : Split e) (j : Split n) (k : Split m)
    (h : E (l j) (l i) (l k+1)=0 ∨ E (r j) (r i) (r k+1)=0) :
    torpedo G E n e m i j k=0 := by rcases h with h|h <;> simp [torpedo,h]
lemma immerse_free (hf : Free I) (t : ℕ) : Free (immerse G I cashless t) := by
  intro e
  induction t using Nat.strong_induction_on generalizing e with
  | h t ih =>
     cases t with
     | zero => simp [hf e]
     | succ t =>
        have ht : ∀ i j k,torpedo G (immerse G I cashless) t 0 e i j k=0 := by
          intro i j k; apply torpedo_zero; left; rw [eq_bot_iff.mpr (left_small i)]; exact ih (l j) (by have hk:= left_small j; omega) _
        simp [restore,ht,ih t (by omega)]
lemma immerse_bounded (hi : FrameBound I) (t : ℕ) : FrameBound (immerse G I cashless t) := by
  induction t using Nat.strong_induction_on with
  | h t ih=>
     intro e n hn
     cases t with
     | zero => simp [hi e n hn]
     | succ t =>
        have ht : ∀ i j k,torpedo G (immerse G I cashless) t e n i j k=0 := by
          intro i j k; apply torpedo_zero; by_cases h : l i+2<l k+1
          · exact Or.inl (ih (l j) (by have hv:= left_small j; omega) (l i) _ h)
          exact Or.inr (ih (r j) (by have hv:= right_small j; omega) (r i) _ (by have hi:=parts i; have hk:=parts k; omega))
        simp [restore,ht,ih t (by omega) e (n+2) (by omega)]
lemma immerse_time (hi : FrameBound I) (hf : Free I) (d e n : ℕ) (h : 3*e < n+2*d) : immerse G I cashless d e n=0 := by
  induction d using Nat.strong_induction_on generalizing e n with
  | h d ih=>
    cases d with
    | zero => cases e with
       | zero => simp [hf n]
       | succ e => simp [hi (e+1) n (by omega)]
    | succ d=>
       have ht : ∀ i j k,torpedo G (immerse G I cashless) d e n i j k=0 := by
         intro i j k; apply torpedo_zero; by_cases he : 3*l i < l k + 1 + 2*l j
         · exact Or.inl (ih (l j) (by have hv:= left_small j; omega) (l i) _ he)
         exact Or.inr (ih (r j) (by have hv := right_small j; omega) (r i) _ (by have hi:=parts i; have hj:=parts j; have hk:=parts k; omega))
       simp [restore,ht,ih d (by omega) e (n+2) (by omega)]
lemma immerse_parity (hI : Alternating I) (t : ℕ) : Alternating (immerse G I cashless t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
     intro e n hn
     cases t with
     | zero => simp [hI e n hn]
     | succ t=>
        have ht : ∀ i j k,torpedo G (immerse G I cashless) t e n i j k=0 := by
          intro i j k; apply torpedo_zero; by_cases h : l i %2 ≠ (l k+1)%2
          · exact Or.inl (ih (l j) (by have hv:= left_small j; omega) (l i) _ h)
          exact Or.inr (ih (r j) (by have hv:= right_small j; omega) (r i) _ (by have hi:=parts i; have hk:=parts k; omega))
        simp [restore,ht,ih t (by omega) e (n+2) (by omega)]
lemma immerse_regular (hI : Based I) (t : ℕ) : Based (immerse G I cashless t) := by
  intro e n
  cases t with
  | zero => simp only [start]; split; · exact Regular.zero
            exact hI e n
  | succ t=>
     rw [restore]; split; · exact Regular.zero
     refine Regular.scaled ((Regular.lap _ _).plus (Regular.summed fun i _=> Regular.summed fun j _=> Regular.summed fun k _=> ?_)) _
     exact Regular.rank_cast _ _ (Regular.bridge _ _ _)

lemma siteLimits (hI : FrameBound I) (hf : Free I) (hr : Based I) :
    FrameBound (receive G I cashless) ∧ Based (receive G I cashless) ∧ Free (receive G I cashless) :=
  ⟨fun e n h=> sum_eq_zero fun t _=> immerse_bounded G cashless hI t e n h,
     fun e n=> Regular.summed fun i _=> immerse_regular G cashless hr i e n,
     fun n=> sum_eq_zero fun t _=> immerse_free G cashless hf t n⟩
lemma receive_parity (ha : Alternating I) : Alternating (receive G I cashless) := fun e n h=> sum_eq_zero fun t _=> immerse_parity G cashless ha t e n h
lemma receive_congr {I' : Record X} (p : ℕ) (hi : ∀ e ≤ p,∀ n>0,I e n=I' e n) (b : Bool) (e n) (he : e ≤ p) (hn : n≠0) :
    receive G I cashless e n=receive G I' b e n := sum_congr rfl fun i _=> congr_through G cashless p hi b i e n he hn
end contract
end Sheet
end YM.WilsonBulk
