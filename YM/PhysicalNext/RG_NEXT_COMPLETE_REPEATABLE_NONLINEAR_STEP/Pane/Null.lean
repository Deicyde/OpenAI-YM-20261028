import YM.AnalyticNext.QUARTIC_MATCH.Cells.Interval
import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-!
# Auxiliary income on Kin predecessors. VAC means all-good characteristic
on input VIRT step, not Wilson top. Keep F,W labels countable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes
open ConnectedActivityE6 Testing SectorMeasure
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge}
section Muse
variable (n : Side) (G : Gauge)
def keys : ℕ≃(Site n×ℕ):= numbering _
def abscissas (i : ℕ) := (keys n i).1
def pale : Activities G n where
  reg i:= ⟨abscissas n i,{abscissas n i},mem_singleton_self _⟩
  forced i:=⟨{abscissas n i},{abscissas n i},singleton_nonempty _, Subset.refl _, fun _=>True⟩
  E _:=0
  K _:=0
lemma whey (P : BudgetPoint) : (pale n G).Valid P 0 0 := by
  have hr i:P.Regular (((pale n G).reg i).support) (fun _ : Config G n=> (0:ℝ)):= CouplingShape.reg_const _
  refine ⟨⟨hr,fun _=>rfl,fun _ _ a b _ _=> by
    unfold logHessian; change iteratedFDeriv ℝ 2 (fun _ : Directions G n=> (0:ℝ)) 0 _ = _; simp⟩,?_,?_,?_,?_⟩
  · refine ⟨fun _ _ _=>rfl,fun _ _ _=>Iff.rfl,fun _=>measurable_const,fun _=>MeasurableSet.univ,fun _ _ _ _ _=> rfl, fun _ _ _ _ _=> rfl, fun i U hh=> False.elim (hh rfl)⟩
  · intro s b; let t := Equiv.prodCongr (StepData.sendSites s b) (Equiv.refl ℕ); let e:=keys n; let f:Equiv.Perm ℕ:= (e.trans t).trans e.symm
    have he i: e (f i)=t (e i) := e.apply_symm_apply _
    have hz i: abscissas n (f i)=affine s b (abscissas n i) := congr_arg Prod.fst (he i)
    have hv i : ({abscissas n (f i)}:Support n)= image (affine s b) {abscissas n i} := by simp [hz]
    exact ⟨⟨f,f,hz,hv,hv,hv,fun _ _=> Iff.rfl,fun _ _=> rfl, fun _ _=>rfl⟩⟩
  · refine ⟨fun _=>0,fun i=>?_,fun x=> by simp [SumBudget,BudgetPoint.mass]⟩
    simpa only [abs_zero] using! CouplingShape.sup_const (G:=G) (p:=P) (o:=((pale n G).reg i).site) (X:=((pale n G).reg i).support) 0
  exact ⟨0,fun i=>⟨le_rfl,fun U=> by change ‖(0:ℝ)‖ ≤ 0; rw [norm_zero]⟩,fun x=> by simp [SumBudget,BudgetPoint.mass]⟩
variable {n G}
lemma pale_value (P : BudgetPoint) (V : Config G n) : (pale n G).additive P V=0 ∧ (pale n G).gas P V=if flags P.threshold V=∅ then 1 else 0 := by
  constructor
  · change (∑' i,masked _ _ _ _) = (0:ℝ); simp [pale, masked, Set.indicator]; -- edit
  split
  next h=> exact Activities.gas_one _ _ h
  next h=>
    have he i: (pale n G).gasOccurrence P i V=0:= by
      unfold Activities.gasOccurrence; split
      next hk=>
        obtain ⟨k,hk⟩:= Finset.nonempty_iff_ne_empty.mpr (show i≠∅ from fun hi=> h ((by obtain ⟨_,hK⟩:=hk; rw [hi] at hK; simpa using hK.symm)))
        exact prod_eq_zero hk rfl
      rfl
    unfold Activities.gas; simp_rw [he,tsum_zero]
lemma tranquility {t : ℝ} (V : Config G n) (h : flags t V=∅) (s : Signed) (v : Site n) : flags t (pull s v V)=∅ := by
  have he:= Work.H03.flags_send s v t V; rw [h,Finset.image_eq_empty] at he; exact he -- orientations?
lemma lucid (P : BudgetPoint) (V : Config G n) (h : flags P.threshold V=∅) (p : Pressure.Cell n): G.chord (faceValue V p) ≤ P.threshold := by
  by_contra! he; have hz:p.1 ∈ flags P.threshold V:= (flags_spec ..).mpr ⟨p,YM.WilsonStartup.anchor_visit _,he⟩
  rw [h] at hz; simp at hz
lemma crystal (W : PathData G) (c : Clip) (P : BudgetPoint) (V : Config G n) (h : flags P.threshold V=∅) :
    ∑ i:Pressure.Cell n, W.baseTerm c P V i=quadratic c W V := by
  refine Finset.sum_congr rfl fun i _=> ?_
  unfold RG.PathData.baseTerm RG.PathData.clipped; rw [if_pos (lucid _ V h i), if_pos (show PathData.kept _ _ _ _ from fun j=> (lucid _ V h j).trans (le_mul_of_one_le_right P.threshold_pos.le (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) c.radius_pos.le))))]; rw [G.chord_price]; ring
lemma actly (k : ℕ) (W : ℕ→Atom G k) (P : BudgetPoint) (V : Config G n) (h : flags P.threshold V=∅) :
    ∑ i:Site n, PathData.atomSeries W P V i=uncut W V := Finset.sum_congr rfl (fun _ _=> tsum_congr fun _=> masked_eq _ _ _ _ (show Healthy P.threshold _ V from disjoint_left.mpr fun x _ hx=> notMem_empty x (h ▸ hx)))
lemma crystalline (W : PathData G) (c : Clip) (P : BudgetPoint) (β : ℝ) (V : Config G n) (h : flags P.threshold V=∅) :
    W.inChannels c P β V=β*mainTerm c W V + Precision.loop W V := by
  have hp s : W.principal c P β (pull s 0 V) = β*(quadratic c W (pull s 0 V) + uncut W.cubic (pull s 0 V)+ uncut W.quartic (pull s 0 V))+ uncut W.loop (pull s 0 V) := by
    have he:= tranquility V h s 0; unfold PathData.principal; rw [Finset.sum_add_distrib,crystal _ _ P _ he,actly _ _ _ _ he,actly _ _ _ _ he,actly _ _ _ _ he,add_assoc]
  unfold PathData.inChannels; simp_rw [hp]; rw [Finset.sum_add_distrib,← Finset.mul_sum]; unfold mainTerm Patch.average Precision.loop Patch.average; ring
end Muse
end YM.PhysicalNext.Repeat.Pane
