import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.ColumnL
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Repaid

/-!
# Collect actual path contributions, with their masks
 Keep output PathData. This is before combination Hessian cancellations.
 In particular pricing this lead separately will be too dear for Local
 (cubic input/output together with β, cost g-ish). No held affine
 iteration conclusion from the existence of these prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Song
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration  WilsonStartup
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} (R : PathData G) (c : Clip) (p : BudgetPoint)

-- direct atom pieces: path section, all oriented canonical, including Laurent plane/cubic parameter
abbrev Stave := Seat n × ℕ
abbrev Tally (n : Side) := Seat n × Low
abbrev Songbook (n : Side) := (Tally n) ⊕ Stave (n:=n) ⊕ Stave (n:=n) ⊕ Stave (n:=n)
variable {l : ℕ} (A : ℕ→Atom G l) {σ C Λ : ℝ} (U : Config G n)

def pitch (i : Stave (n:=n)) : RegularAddress n := Seat.reg i.1 ((A i.2).footprint 0) (mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩)
def tuneAtom (β : ℝ) (i : Stave (n:=n)) : Config G n→ ℝ := (factor*β) • (fun U => (A i.2).unmasked (i.1.view U) 0)
def tuneLow (γ : ℝ) (i : Tally n) : Config G n → ℝ := (factor*γ) • (fun U => i.2.mark R c * i.2.plain R (0:Site n) (i.1.view U))
def strings (R : PathData G) (p : BudgetPoint) : Songbook n→ RegularAddress n := Sum.elim (lowEntry G R p) (Sum.elim (pitch R.cubic) (Sum.elim (pitch R.quartic) (pitch R.loop)))
def sounding (β γ : ℝ) : Songbook n→ Config G n → ℝ := Sum.elim (tuneLow R c (-γ)) (Sum.elim (tuneAtom R.cubic (-β)) (Sum.elim (tuneAtom R.quartic (-β)) (tuneAtom R.loop (-1))))
lemma coupon (γ : ℝ) (i : Tally n) : masked p.threshold (strings R p (Sum.inl i)).support (tuneLow R c γ i) U =
    γ*stack (fun d : Low=> d.maskedPlain R c 0 p) U i := by
  let θ := i.1; let a:=i.2; let F (V : Config G n):= a.mark R c * a.plain R 0 V
  change masked _ (θ.spread (a.home R p 0)) _ _=_
  rw [show masked _ _ (tuneLow R c γ i) U=_ from mask_mul (θ.spread (a.home R p 0)) p.threshold (factor*γ) U (F ∘ θ.view),θ.distribute]; change _*Low.maskedPlain R c a 0 p (θ.view U) = γ*(factor*_); ring
lemma couponA (β : ℝ) (i : Stave (n:=n)) : masked p.threshold (pitch A i).support (tuneAtom A β i) U = factor * β * (A i.2).placed p (i.1.view U) 0 := by
  let θ:= i.1; let a:=A i.2; let F (V : Config G n) := a.unmasked V 0
  change masked _ (θ.spread (a.footprint 0)) (fun V => factor * β * (F ∘ θ.view) V) U = _
  rw [show masked _ _ _ U = _ from mask_mul (θ.spread (a.footprint 0)) p.threshold (factor*β) U (F ∘ θ.view),θ.distribute]; rfl
lemma pasted (γ : ℝ) (h : R.Bounds c σ C Λ) : HasSum (fun i : Tally n=> masked p.threshold (strings R p (.inl i)).support (tuneLow R c γ i) U)
      (γ*Collection.receipt R c p U) := by
  simp_rw [coupon]; unfold Collection.receipt; rw [layer_total _ U (Low.maskedPlain_sum h p 0)]; exact (stack_series _ U (Low.maskedPlain_sum h p 0)).hasSum.mul_left _

def billOf := averaged fun i=> ∑ x : Site n, PathData.atomSeries A p (pull i 0 U) x

def splay (n : Side) : Equiv.Perm (Seat n) := Equiv.prodCongrRight fun i : Signed => (i.actEquiv.toEquiv : Equiv.Perm _)
lemma plumes (i : Seat n) (j : ℕ) : (A j).placed p ((splay n i).view U) 0=(A j).placed p (pull i.1 0 U) i.2 := by
  have he : (splay n i).view U = translate i.2 (pull i.1 0 U) := by rw [← Lattice.pull_one,pull_pull,mul_one,affine,add_zero]; rfl
  rw [he,Turn.validation,zero_add]
lemma allocated (β : ℝ) (hs : 0<σ) (h : SumBudget (fun i=> (A i).budget σ) C) : HasSum
    (fun i : Stave (n:=n)=> masked p.threshold (pitch A i).support (tuneAtom A β i) U) (β * billOf p A U) := by
  simp_rw [couponA];
  have hv (x : Seat n) := ((PathData.atom_dominated A p 0 hs h).summable (x.view U)).hasSum.mul_left (factor*β)
  have ht : HasSum (fun i : Stave (n:=n)=>factor*β * (A i.2).placed p (i.1.view U) 0) (∑ x : Seat n, factor*β*PathData.atomSeries A p (x.view U) 0) := Raw.finite_start _ _ hv
  unfold billOf; convert ht using 1; rw [← mul_sum, ← Equiv.sum_comp (splay n) (fun x => _),Fintype.sum_prod_type]
  simp_rw [PathData.atomSeries,plumes p A U]; unfold averaged; change _* (factor*_)=_; ring

lemma chan (β : ℝ) : R.inChannels c p β U=β*(averaged fun s=>∑ i:Pressure.Cell n,R.baseTerm c p (pull s 0 U) i)+
    (β*(billOf p R.cubic U+billOf p R.quartic U)+billOf p R.loop U) := by unfold PathData.inChannels PathData.principal billOf; simp_rw [sum_add_distrib, ← mul_sum, averaged]; simp_rw [sum_add_distrib]; ring

lemma literalScore (β γ : ℝ) (h : R.Bounds c σ C Λ) : HasSum
    (fun i=> masked p.threshold (strings R p (n:=n) i).support (sounding R c β γ i) U)
      (-(γ*Collection.receipt R c p U+(β*(billOf p R.cubic U+billOf p R.quartic U)+billOf p R.loop U))) := by
  let T (i : Songbook n):= masked p.threshold (strings R p i).support (sounding R c β γ i) U
  have hx := HasSum.sum (f:=T) (pasted R c p U (-γ) h) (HasSum.sum (f:=fun i=> T (.inr i)) (allocated p R.cubic U (-β) h.width h.three) (HasSum.sum (f:=fun i : Stave (n:=n) ⊕ Stave (n:=n)=> T (.inr (.inr i))) (allocated p R.quartic U (-β) h.width h.four) (allocated p R.loop U (-1) h.width h.two)))
  convert hx using 1; ring

-- single cost before β cancellation
lemma pitch_charge (i : Stave (n:=n)) (β : ℝ) (h : ∀ i,(A i).Invariant) :
    p.Regular (pitch A i).support (tuneAtom A β i) ∧ p.supBounds (pitch A i).site (pitch A i).support (tuneAtom A β i) (|factor*β| * (turnFee p* Wages.price p (A i.2))) := by
  let x:=A i.2
  have hx:= Derivs.canonical_regular x (0:Site n) p (h i.2)
  have ht:= Bill.sup (Wages.fin p x 0) (X:=x.footprint (0:Site n)) (fun _ h=> h)
  exact ⟨CouplingShape.reg_scale _ (i.1.regular hx), CouplingShape.sup_scale _ (Seat.sup i.1 hx ht)⟩

lemma tally_charge (i : Tally n) (γ : ℝ) (h : Decent c p) :
    p.Regular (strings R p (.inl i)).support (tuneLow R c γ i) ∧ p.supBounds i.1.2 (strings R p (.inl i)).support (tuneLow R c γ i) (|factor*γ| * (turnFee p*(|i.2.mark R c| * lowCost G p (i.2.length R)*p.threshold^2))) := by
  let d:= i.2; let o : Site n:= 0
  have hk:= d.plain_bill R c o h
  have hv := reg_bill hk (Low.plain_cont ..).measurable (Low.plain_local R d p h.radius o) (Low.plain_gauge R d o) -- inspect arity order
  have hp := Bill.sup hk (fun _ he=> he)
  have hl := CouplingShape.sup_scale (d.mark R c) hp
  refine ⟨CouplingShape.reg_scale _ (i.1.regular (CouplingShape.reg_scale (d.mark R c) hv)), sup_le (CouplingShape.sup_scale _ (Seat.sup i.1 (CouplingShape.reg_scale _ hv) hl)) ?_⟩
  unfold lowCost; have he (t:ℝ) : 0 ≤ |t| := abs_nonneg _; have ht := turnFee_pos p
  rw [mul_assoc |i.2.mark R c|]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (sq_nonneg p.threshold)) (abs_nonneg (i.2.mark R c))) ht.le) (abs_nonneg _)
  exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (pair_nonneg ..))
end YM.PhysicalNext.Repeat.Song
