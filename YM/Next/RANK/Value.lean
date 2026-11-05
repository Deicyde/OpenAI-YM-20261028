import YM.Cells.Proximity
import YM.Next.RANK.Array
import YM.Slice.Sequence

/-!
# Local value-order estimates needed for short comparisons

This is *not* a change in the laws at `C.Makes`, readout or label
normalization. It's an estimate surface on the exact density after propagation.
E around 13698: don't require an ordinary-schedule transfer with its
regular coefficient estimates at this (value) order or these radii. We will
always require exact equality of the complete polynomial of Wilson insertions;
unmarked density still comes also with its own `Rep` constraints. Marked estimates
use the same threshold, flags and unmarked exponent. No tying a signed mark to
a quotient. Each occurrence here can be just one monomial (force alternatives
with the same support will be exclusive in the gas because supports have to be
disjoint and they're nonempty). Include even marker-free K in prices.

This value port uses finite address families on every finite torus, with
no bound on number of addresses in the port. If obtaining these estimates by
grouping possibly infinite histories by support, inventory etc, must prove all
those identities/locality with absolute convergence. Extra internal predicates
can be paid in the coefficient. This port by itself doesn't assert anything
about genealogy or allow transforming an estimate on one marked polynomial or
inventory into estimates on other choices. Keep labels unchanged. One-step reuse
of budgets on this path must always be justified separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Value
open RG Marker Glyph Lattice Wilson MeasureTheory Set Function
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] [Fintype V]

/-- Monomial in the marked *exponent*. For Estimates `value` can be a value-only
representative, not taking even a claimed smoothness across branch choices. -/
structure SourceAt (G : Gauge) (ζ : V → Site n) where
  extent : Support n
  fires : modes V
  chosen : fires.val.Nonempty
  remembers i : i∈fires.val → ζ i ∈ extent
  value : Config G n → ℂ
  meas : Measurable value
  loc : LocalOn extent value
  inv : GaugeInvariant value

/-- A labelled K occurrence. All geometry and flags still checked. -/
structure Lifted (G : Gauge) (ζ : V → Site n) (τ : ℝ) where
  extent : Support n
  inventory : Support n
  needed : inventory.Nonempty
  records : inventory ⊆ extent
  fires : modes V
  remembers i : i∈fires.val → ζ i∈ extent
  value : Config G n → ℂ
  meas : Measurable value
  flag U : value U≠0 → extent∩ flags τ U=inventory
  only : UsesFinal τ extent value
  inv : GaugeInvariant value

variable {P : Rep G n} {ζ : V → Site n}

-- Compatibility key (all flag data charged, support incl dependencies). Use the
-- complete unchanged vacuum gas list in Steps, blank-zero padded as needed.
abbrev addressKey (n : Side) := { q : Support n × Support n // q.2.Nonempty ∧ q.2⊆q.1 }

def meterAddress (i : ForcedAddress G n) : addressKey n := ⟨(i.support,i.inventory),i.inventory_ne,i.inventory_sup⟩
def Archive (A : Activities G n) (i : addressKey n) (U : Config G n) := ∑' j, if meterAddress (A.forced j)=i then A.K j U else 0

def column {ι : Type*} [Fintype ι] {τ : ℝ} (K : ι → Lifted G ζ τ) (i : addressKey n) (U : Config G n) :=
    ∑ j, if (K j).fires=quiet V ∧ ((K j).extent,(K j).inventory)=i.val then (K j).value U else 0

/-- Require agreement of the actual K representations by identical compatibility
key. Stronger than same evaluated vacuum gas. All K labels still retain their
UsesFinal support tests and Ward field functions (on every field, not on-domain
resampling); can coalesce within a key before applying vacuum calculus to
identical background list. Sum against `Archive` used together with Lawful
(summability). -/
def Background (P : Rep G n) {ι : Type*} [Fintype ι] (K : ι → Lifted G ζ P.p.threshold) := ∀ i U,column K i U=(Archive P.activities i U:ℂ)

-- support cost; may be asked with spare exponent e larger than current.
def charge (p : BudgetPoint) (e : ℝ) (l : Support n) := Real.exp (e * coverNumber p.B l)
lemma charged (p : BudgetPoint) (e : ℝ) (he : 0 ≤ e) (l : Support n) : 1 ≤ charge p e l := Real.one_le_exp (by positivity)

def SourceAt.amount (b : SourceAt G ζ) (t : ℝ) (U) := Poly.send b.fires (masked t b.extent b.value U)
def Lifted.amount {τ : ℝ} (b : Lifted G ζ τ) (U) := Poly.send b.fires (b.value U)

def Lifted.gather {ι : Type*} {τ : ℝ} (K : ι → Lifted G ζ τ) (p : Finset ι) (U : Config G n) :=
    (p:Set ι).PairwiseDisjoint (fun i => (K i).extent) ∧ p.biUnion (fun i => (K i).inventory) = flags τ U

open scoped Classical in
def Lifted.pack {ι : Type*} {τ : ℝ} (K : ι → Lifted G ζ τ) (p : Finset ι) (U) :=
    if Lifted.gather K p U then ∏ i ∈ p,(K i).amount U else 0

def dust {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Rep G n) (H : ι → SourceAt G ζ) (K : κ → Lifted G ζ P.p.threshold)
    (U : Config G n) : veil V :=
  (Real.exp (P.exponent U) : ℂ) • (Poly.pass (∑ i, (H i).amount P.p.threshold U)* ∑ p : Finset κ, Lifted.pack K p U)

/-- Per-address weights at *current* radius. Put the exponential weight in each
bound. In particular, the regular bound is only on its good mask; K is the full-torus
sup, constrained to the indicated inventory. At higher powers/use conventional
factorials separately. -/
def SourceAt.pays (b : SourceAt G ζ) (p : BudgetPoint) (r : V → ℝ) (e c : ℝ) :=
    0 ≤ c ∧ ∀ U : Config G n, Healthy p.threshold b.extent U → charge p e b.extent *
      Poly.toll r b.fires * ‖b.value U‖ ≤ c

def Lifted.pays (p : BudgetPoint) (b : Lifted G ζ p.threshold) (r : V → ℝ) (e c : ℝ) :=
    0 ≤ c ∧ ∀ U : Config G n, charge p e b.extent * Poly.toll r b.fires * ‖b.value U‖ ≤ c

structure Light {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Rep G n) (H : ι → SourceAt G ζ) (K : κ → Lifted G ζ P.p.threshold)
    (r : V → ℝ) (e l L : ℝ) : Prop where
  bulk : ∃ c : ι → ℝ,(∀ i,(H i).pays P.p r e (c i)) ∧
    ∀ i : V,(∑ j, if i∈ (H j).fires.val then c j else 0) ≤ l
  forced : ∃ c : κ → ℝ,(∀ i,(K i).pays P.p r e (c i)) ∧
    ∀ x : Site n,(∑ j, if x∈ (K j).extent then c j else 0) ≤ L

-- Prop-only existence, but no loss of budgets: depends on exact unnormalized density,
-- and actual current vacuum rep exponent.
def Notice (P : Rep G n) (ζ : V → Site n) (u : Config G n → veil V) (r : V → ℝ) (e l L : ℝ) :=
    ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ), ∃ H : ι → SourceAt G ζ,
      ∃ K : κ → Lifted G ζ P.p.threshold, u=dust P H K ∧ Background P K ∧ Light P H K r e l L

private lemma find_total {s ι : Type*} [DecidableEq s] [Fintype s] [Fintype ι] (Q : ι → Finset s) (hq : ∀ i,(Q i).Nonempty)
    (c : ι → ℝ) (p : ℝ) (h : ∀ i,0 ≤ c i) (hp : ∀ i : s,(∑ j,if i∈ Q j then c j else 0) ≤ p) : ∑ i,c i ≤ (Fintype.card s:ℝ)*p := by
  calc
    _ ≤ ∑ i,∑ j : s, if j∈Q i then c i else 0 := Finset.sum_le_sum fun i _ => by
      obtain ⟨j,hj⟩ := hq i
      have ht := (Finset.single_le_sum (f:=fun a : s => if a∈Q i then c i else 0)
        (fun a _ => by split; exact h _; exact le_rfl) (Finset.mem_univ j))
      rw [if_pos hj] at ht; exact ht
    _ = _ := Finset.sum_comm
    _ ≤ ∑ _ : s,p := Finset.sum_le_sum fun i _ => hp i
    _ = _ := by simp

lemma Notice.price {u : Config G n → veil V} {r : V → ℝ} {e l L : ℝ} (h : Notice P ζ u r e l L)
    (hr : ∀ i,0 < r i) (he : 0 ≤ e) (U : Config G n) :
    Poly.price r (u U) ≤ Real.exp (P.exponent U+(Fintype.card (Site n):ℝ)*L+(Fintype.card V:ℝ)*l) := by
  classical
  obtain ⟨ι,κ,hι,hκ,H,K,rfl,_,⟨⟨c,hc,C⟩, ⟨a,ha,A⟩⟩⟩ := h
  let D := Fintype.card V
  let q := Fintype.card (Site n)
  have hH : Poly.price r (Poly.pass (∑ i,(H i).amount P.p.threshold U)) ≤ Real.exp (D*l) := by
    refine (Poly.pass_budget hr _).trans (Real.exp_monotone ((Poly.batch hr _ _).trans
      ((Finset.sum_le_sum fun i _ => ?_).trans (find_total (fun i => (H i).fires.val) (fun i => (H i).chosen) c l (fun i => (hc i).1) C))))
    rw [SourceAt.amount,Poly.solo]
    by_cases hx : Healthy P.p.threshold (H i).extent U
    · rw [masked_eq _ _ _ _ hx]; apply le_trans _ ((hc i).2 U hx); rw [mul_assoc]
      apply le_mul_of_one_le_left (mul_nonneg (Poly.worth hr _).le (norm_nonneg _)) (charged _ _ he _)
    rw [masked_ne _ _ _ _ hx,norm_zero,mul_zero]; exact (hc i).1
  have ha' (p : Finset κ) : Poly.price r (Lifted.pack K p U) ≤ ∏ i∈p,a i := by
    unfold Lifted.pack
    split_ifs
    · apply (Poly.multiple hr _ _).trans; refine Finset.prod_le_prod (fun i _ => Poly.nonnegative hr _) fun i _ => ?_
      rw [Lifted.amount,Poly.solo]; apply le_trans _ ((ha i).2 U); rw [mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg (Poly.worth hr _).le (norm_nonneg _)) (charged _ _ he _)
    rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _ => (ha i).1
  have hK : Poly.price r (∑ p : Finset κ,Lifted.pack K p U) ≤ Real.exp (q*L) := by
    apply (Poly.batch hr _ _).trans
    calc
      _ ≤ ∑ i : Finset κ,∏ j∈i,a j := Finset.sum_le_sum fun i _ => ha' i
      _ = ∏ j, (a j + 1) := by simpa using! (Fintype.prod_add a (fun _ => 1)).symm
      _ ≤ ∏ j, Real.exp (a j) := Finset.prod_le_prod (fun i _ => add_nonneg ((ha i).1) zero_le_one) (fun i _ => Real.add_one_le_exp _)
      _ ≤ _ := by
        rw [← Real.exp_sum]; exact Real.exp_monotone (find_total (fun i => (K i).extent)
          (fun i => (K i).needed.mono (K i).records) a L (fun i => (ha i).1) A)
  unfold dust
  rw [Poly.adapted,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left (Poly.multiplication hr _ _) (Real.exp_pos _).le).trans ?_
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hH hK (Poly.nonnegative hr _) (Real.exp_pos _).le) (Real.exp_pos _).le).trans
  simp only [Real.exp_add,q,D]; exact le_of_eq (by ring)

end YM.Next.Rank.Value
