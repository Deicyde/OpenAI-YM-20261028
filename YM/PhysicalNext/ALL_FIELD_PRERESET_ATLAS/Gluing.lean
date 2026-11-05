import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.MaskMotion
import YM.Bid.Craft
import YM.Next.EXTRACTION.Tails
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Walls
import YM.SectorNext.RECONNECTED_LOCALITY.Weld
import YM.Work.H03



/-!
# Same `Depot` convention even after a mask correction

Expand `exp(call)` of each incident index with the repeated-powers convention (could
also use one address carrying `exp(call)-1`; here we keep the factorials). Then merge
on *all* overlap supports. Retain in the new addresses all older flags **and** extra
tests and the whole support graph. Proof engines `LogIdentity.Attach` &
`LogIdentity.MaskMotion`. This file concerns reading that engine at a `Depot`, not a
second proof of the merger from scratch.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson MeasureTheory Filter Function Finset
open Push.LogIdentity Push.AbsoluteSums Attach
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side}
namespace Depot
variable (X : Depot G n) (P : Slip n) (b : BudgetPoint)

/-- Output of `MaskMotion`. Complete union supports. Includes even legally or
geometrically unused addresses. -/
def combined : Depot G n := {
    letter := Species' X.range P.reach
    label := fun i => {
      support := zone X.range P.reach i
      inventory := hold X.range X.need P.reach i
      inventory_ne := hold_nonempty _ _ _ i (fun j => (X.label j).inventory_ne)
      inventory_sup := hold_zone _ _ _ i (fun j => (X.label j).inventory_sup)
      extraTest := fun V => ∀ j∈i.val.val.1.toLeft, (X.label j).eligible b.threshold V } }

/-- Ink not simplified by evaluating incompatible components. -/
def filled (K : X.Ink) (u : P.Ink G) : (X.combined P b).Ink := fun i V =>
    merged X.range X.range X.need P.reach P.reach (flags b.threshold V)
      (fun i => K i V) (fun i => u i V) i



/-- Unscaled expense on emitted entries, independent of field from any pointwise
prices on the two input banks. Hit budgets through these letters are a separate
application of `MaskMotion.remerge`; for unconditional-at-fixed-torus identity it
is enough that the *inputs* to this stage already have absolute sales certificates. -/
def mass (v : X.letter → ℝ) (u : P.letter → ℝ) (i : (X.combined P b).letter) :=
    MaskMotion.lexer X.range P.reach v u i





lemma affordable {v : X.letter → ℝ} {u : P.letter → ℝ} (hv : Summable v) (hu : Summable u) :
    Summable (X.mass P b v u) := by
  let f := Sum.elim v u
  have he : Summable f := Summable.sum _ hv hu
  exact (exponential f he.norm).1.of_norm.comp_injective
    (i:=fun i : (X.combined P b).letter => i.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)

/-- Even if the old actual flag checks are not disjoint on their external
one-plaquette read halos, they're still read on the same V and are paid on its
`UsesFinal` bank. `ink` includes every ancestor (the Borel or overlapping checks
beyond `extraTest` too). `Tenants` not an assertion of quotient covariance. -/
lemma sheltered {K : X.Ink} {u : P.Ink G} (h : X.Tenants b K) (hv : P.Vouched b u) :
    (X.combined P b).Tenants b (X.filled P b K u) := by
  let D := X.combined P b
  let inp (j : X.letter ⊕ P.letter) (V : Config G n) := j.elim (fun i => K i V) (fun i => u i V)
  have ho (i : D.letter) (j : X.letter ⊕ P.letter) (hj : j ∈ i.val.val.1) :
      j.elim X.range P.reach ⊆ D.range i := fun _ h => mem_biUnion.mpr ⟨_,hj,h⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i k V
    have hx : (fun j => K j (Lattice.gauge k V)) = (fun j => K j V) := funext fun j => h.gauge j k V
    have hy : (fun j => u j (Lattice.gauge k V)) = (fun j => u j V) := funext fun j => hv.gauge j k V
    unfold filled merged; rw [gauge_flags,hx,hy]
  · intro i k V
    change (∀ j∈i.val.val.1.toLeft, _) ↔ _
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    exact Work.H03.eligible_gauge b.threshold _ _ _ (h.testGauge _ _ _)
  · intro i V U he he'
    unfold filled merged
    rw [show zone X.range P.reach i ∩ flags b.threshold V = zone X.range P.reach i ∩ flags b.threshold U from he']
    split
    next _ =>
      unfold Attach.bill; split
      next _ =>
        unfold Multiple.manyW; apply prod_congr rfl
        intro j _
        have hX : inp j V = inp j U := by
          rcases j with ⟨j | j,hj⟩
          · exact Work.H03.reads_larger (show X.range j ⊆ D.range i from ho i (.inl j) hj)
              (h.usesInk j) V U he he'
          exact Work.H03.reads_larger (show P.reach j ⊆ D.range i from ho i (.inr j) hj) (hv.localizes j) V U he he'
        change inp j V ^ _ / _ = inp j U ^ _ / _
        rw [hX]
      rfl
    rfl
  · intro i V U he he'; apply propext
    change (∀ j ∈ i.val.val.1.toLeft, _) ↔ (∀ j ∈ i.val.val.1.toLeft, _)
    refine forall_congr' fun j => imp_congr_right fun h_ij => ?_
    exact Iff.of_eq (Work.H03.reads_larger
      (show X.range j ⊆ D.range i from ho i (.inl j) (mem_toLeft.mp h_ij))
      (Work.H03.eligible_reads b.threshold _ (h.usesProbe j)) V U he he')
  · intro i
    unfold filled merged
    have hm : MeasurableSet {V : Config G n | _} :=
      Work.H03.eligible_measurable b.threshold ({D.label i with extraTest := fun _ => True})
        (show MeasurableSet {V : Config G n | True} from MeasurableSet.univ)
    have hx (j : X.letter ⊕ P.letter) : Measurable (inp j) := by
      cases j <;> first | exact h.expenses _ | exact hv.expenses _
    apply Measurable.ite (?_) ?_ measurable_const
    · change MeasurableSet {V : Config G n | D.range i ∩ flags b.threshold V = D.need i}
      simpa only [ForcedAddress.eligible,and_true] using hm
    unfold Attach.bill
    split
    next _ => exact Finset.measurable_fun_prod _ (fun j _ => ((hx j.val).pow_const _).div_const _)
    exact measurable_const
  · intro i
    change MeasurableSet {V | ∀ j ∈ i.val.val.1.toLeft, (X.label j).eligible b.threshold V}
    simp only [Set.setOf_forall]
    exact MeasurableSet.biInter (countable_toSet _) (fun j _ => Work.H03.eligible_measurable _ _ (h.probes j))
  intro i V he
  unfold filled merged Attach.bill Multiple.manyW at he
  split at he
  next ht =>
    refine ⟨ht,?_⟩
    intro j hj
    apply h.permits j
    intro hK
    apply he
    split
    next _ =>
      let e : ↥(i.val.val.1) := ⟨Sum.inl j,Finset.mem_toLeft.mp hj⟩
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [e,hK]
    rfl
  contradiction

end Depot
end YM.PhysicalNext.PreAtlas
