import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intake
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paths
import YM.Push.RELAY_DIFFERENCE.Rolling


/-!
# Expose the actual inherited multipliers (before Gaussian substitution)

`pairTail` computed in each orientation on the indicated level;
output factor distinguished is the TRUE clipped base at threshold
`temp x`, not just its truncation. Thus include the extra coarse costs
with the proper positive sign. Inputs use original unconstrained and
constrained families (K addresses separate module for packet pricing),
not assumptions about a hypothetical RG output. At every U tagged or
not. No Taylor, integration or support-exclusion hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {n c f : Side} {S : StepData c f}

namespace Raw
abbrev Trans (n : Side) := Signed × Site n × ℕ
abbrev Pairs (n : Side) := Signed × PlaqAxes × Site n × (ℕ×ℕ)

/-- Ordered sum type, not collapsing addressed terms that happen to
have equal values. E, cubic, quartic, loop, input tail, output tail. -/
abbrev LogLetter (c f : Side) := ℕ ⊕ Trans f ⊕ Trans f ⊕ Trans f ⊕ Pairs f ⊕ Pairs c

def orientation : ℝ := (Fintype.card Signed:ℝ)⁻¹

lemma orientation_range : 0 < orientation ∧ orientation ≤ 1 := by
  have hp : 1 ≤ (Fintype.card Signed:ℝ) := by exact_mod_cast Fintype.card_pos (α:=Signed)
  exact ⟨inv_pos.mpr (zero_lt_one.trans_le hp),inv_le_one_of_one_le₀ hp⟩

def translateValue {d : ℕ} (p : BudgetPoint) (T : ℕ → Atom G d) (cost : ℝ) (U : Config G f) : Trans f → ℝ :=
  fun i => cost*(T i.2.2).placed p (pull i.1 0 U) i.2.1

def pairValue (T : PathData G) (C : Clip) (t : ℝ) (R d : ℕ) (cost : ℝ) (U : Config G n) (i : Pairs n) :=
    cost*pairTail T C R d t (i.2.2.1,i.2.1) (pull i.1 0 U) i.2.2.2

/-- Exponent after peeling truncated oriented bases and extracting the
true FULL output base. Applied to the very same U,V in every term. -/
def expo (T : Tube G S) (x : ℝ) (R : Rep G f) (U : Config G f) (V : Config G c) : LogLetter c f → ℝ :=
    let b := -orientation*R.beta
    let W := R.path
    Sum.elim (fun i => -R.activities.regularOccurrence R.p i U)
    (Sum.elim (translateValue R.p W.cubic b U)
    (Sum.elim (translateValue R.p W.quartic b U)
    (Sum.elim (translateValue R.p W.loop (-orientation) U)
    (Sum.elim (pairValue W R.clip R.p.threshold (till x) 1 b U)
        (pairValue T.down T.low (temp x) (till x) S.patch.L.val (-b) V)))))

/-- Volume primitive for extracting FULL distinguished output base. -/
def stone (T : Tube G S) (β x : ℝ) (V : Config G c) :=
   Real.exp (-β * (averaged fun s =>
     ∑ i : Cell c, (crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i +
       tails T.down T.low (till x) S.patch.L.val (temp x) i (pull s 0 V))))

theorem stone_full {x : ℝ} (T : Tube G S) (β : ℝ) (V : Config G c) (p : BudgetPoint)
    (h : p.threshold = temp x) : stone T β x V = Real.exp (-β * (averaged fun s =>
      ∑ i : Cell c, T.down.baseTerm T.low p (pull s 0 V) i)) := by
  unfold stone; congr! 3
  funext s
  apply Finset.sum_congr rfl; intro i _
  rw [← h, ← cuff_tails]; unfold cuff; ring

lemma finite_start {ι κ : Type*} [Fintype κ] (w : κ × ι → ℝ) (a : κ → ℝ) (h : ∀ i, HasSum (fun j => w (i,j)) (a i)) :
    HasSum w (∑ i, a i) := by
  have hw : Summable w := ((summable_prod_of_nonneg (show 0 ≤ (fun i => ‖w i‖) from fun _ => norm_nonneg _)).2
    ⟨fun i => (h i).summable.norm, (hasSum_fintype _).summable⟩).of_norm
  convert hw.hasSum using 1; rw [hw.tsum_prod,tsum_fintype]; simp_rw [(h _).tsum_eq]

lemma atomValue_sum {d : ℕ} (p : BudgetPoint) (T : ℕ → Atom G d) {σ v : ℝ} (cost : ℝ) (U : Config G f)
    (hp : 0 < σ) (h : SumBudget (fun i => (T i).budget σ) v) :
    HasSum (translateValue p T cost U)
      (∑ s : Signed, ∑ x : Site f, cost*PathData.atomSeries T p (pull s 0 U) x) := by
  refine finite_start _ _ fun s => finite_start _ _ fun x => ?_
  exact ((PathData.atom_dominated T p x hp h).summable (pull s 0 U)).hasSum.mul_left _

lemma pairValue_sum (T : PathData G) (p : Clip) (t : ℝ) (R d : ℕ) (cost : ℝ) (U : Config G n)
    {σ C Λ : ℝ} (h : T.Bounds p σ C Λ) :
    HasSum (pairValue T p t R d cost U) (∑ s : Signed, ∑ i : Cell n, cost * tails T p R d t i (pull s 0 U)) := by
  let Z := fun (s : Signed) (i : Cell n) => cost * tails T p R d t i (pull s 0 U)
  suffices H : HasSum (pairValue T p t R d cost U) (∑ s : Signed, ∑ i : PlaqAxes, ∑ x : Site n, Z s (x,i)) by
    have he : ∀ s : Signed, (∑ i : Cell n, Z s i) = ∑ i : PlaqAxes, ∑ x : Site n, Z s (x,i) := fun s =>
      (Fintype.sum_prod_type (Z s)).trans (Finset.sum_comm (f:=fun x i => Z s (x,i)))
    change HasSum _ (∑ s : Signed, ∑ i, Z s i)
    simp only [he]; exact H
  refine finite_start _ _ fun s => finite_start _ _ fun i => finite_start _ _ fun x => ?_
  exact HasSum.mul_left cost (pair_sum h R d t (x,i) (pull s 0 U))

/-- The sum appears multiplied by - on the input but on coarse T.down
with +, so that extracting the output factor reconstructs exactly. -/
def outTail (T : Tube G S) (x : ℝ) (V : Config G c) :=
    averaged fun s => ∑ i : Cell c, tails T.down T.low (till x) S.patch.L.val (temp x) i (pull s 0 V)

theorem income {P : Teller G} {T : Tube G S} {x : ℝ} {R : Rep G f} (hp : Intake P T x R)
    (U : Config G f) (V : Config G c) : HasSum (expo T x R U V)
    (-(averaged fun s => reduced R (till x) (pull s 0 U)) - R.activities.additive R.p U + R.beta*outTail T x V) := by
  let w := -orientation*R.beta
  let b := expo T x R U V
  have hT := hp.cap.paths
  have hE := (R.activities.ESeries (δ:=incomingE G S.patch.L x) (w:=incomingK G S.patch.L x) hp.cap.labels).summable U
  obtain ⟨_,_,_,hk⟩ := hp.ready.feeds
  rw [← hp.ready.low] at hk
  have H := HasSum.sum (f:=b) (a := -(R.activities.additive R.p U)) hE.hasSum.neg
    (HasSum.sum (atomValue_sum _ _ w U hT.width hT.three) (HasSum.sum (atomValue_sum _ _ w U hT.width hT.four)
    (HasSum.sum (atomValue_sum _ _ (-orientation) U hT.width hT.two)
    (HasSum.sum (pairValue_sum _ _ _ _ _ w U hT) (pairValue_sum _ _ _ _ _ (-w) V hk)))))
  unfold b at H
  convert H using 1
  unfold reduced outTail
  simp_rw [cuff_tails]; unfold averaged w orientation
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]; ring

theorem full_sieve (T : Tube G S) (β x : ℝ) (V : Config G c) : sieve T β x V =
    stone T β x V * Real.exp (β*outTail T x V) := by
  unfold sieve stone outTail
  simp_rw [← Real.exp_add,Finset.sum_add_distrib,av_add]; congr 1; ring



/-! ## Site addresses retained for estimates and patches -/

def scaleOne : Side := ⟨1, by decide⟩
def atOne (n : Side) : Ratio n n := ⟨scaleOne, Nat.mul_one _ |>.symm⟩
lemma parent_one (x : Site n) : (atOne n).parent x = x := by
  have he : (atOne n).embed x=x := by simp [Ratio.embed,atOne,scaleOne]
  simpa only [he] using ((atOne n).embed_parent x)

def atomFoot (p : Ratio c f) (l B : ℕ) {d : ℕ} (T : ℕ → Atom G d) (i : Trans f) :=
  (enlargement p l B (inspected ((T i.2.2).footprint i.2.1))).image (affine i.1 0)

def atomCharge {d : ℕ} (T : ℕ → Atom G d) (i : Trans f) := (T i.2.2).length

def bothFoot (p : Ratio c f) (l B : ℕ) (T : PathData G) (i : Pairs f) :=
    (enlargement p l B (pairFoot B T (i.2.2.1,i.2.1) i.2.2.2)).image (affine i.1 0)

def bothCharge (T : PathData G) (i : Pairs f) := length (duplex T i.2.1 i.2.2.2)

def regularFoot (p : Ratio c f) (l B : ℕ) (R : Rep G f) (i : ℕ) :=
    enlargement p l B (inspected (R.activities.reg i).support)

def forcedFoot (p : Ratio c f) (l B : ℕ) (R : Rep G f) (i : ℕ) :=
    enlargement p l B (inspected (R.activities.forced i).support)

/-- Working support (overtesting allowed by l; later reserve for flags
and eligibility must fit here). Does not define final V mask. -/
def space (T : Tube G S) (l B : ℕ) (R : Rep G f) : LogLetter c f → Support c :=
    let p := S.ratio
    Sum.elim (regularFoot p l B R) (Sum.elim (atomFoot p l B R.path.cubic)
      (Sum.elim (atomFoot p l B R.path.quartic) (Sum.elim (atomFoot p l B R.path.loop)
        (Sum.elim (bothFoot p l B R.path) (bothFoot (atOne _) l B T.down)))))

def regularExtra (R : Rep G f) (i : ℕ) := coverNumber R.p.B (R.activities.reg i).support
def forcedExtra (R : Rep G f) (i : ℕ) := coverNumber R.p.B (R.activities.forced i).support

/-- Keep actual true lengths as well as the spatial cover test. -/
def extra (T : Tube G S) (R : Rep G f) : LogLetter c f → ℕ :=
  Sum.elim (regularExtra R) (Sum.elim (atomCharge R.path.cubic) (Sum.elim (atomCharge R.path.quartic)
    (Sum.elim (atomCharge R.path.loop) (Sum.elim (bothCharge R.path) (bothCharge T.down)))))
end Raw
end YM.ConnectedActivityE6
