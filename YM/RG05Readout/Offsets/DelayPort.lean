import YM.RG05Readout.Offsets.Delay
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
/-! Angle adapter on bandage at registration -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice RG RG.Supply Wilson Pressure Precision Labels Tree Next Next.Foundations
open Input Org Extra.Histories JointLoad JointLoad.Heir JointLoad.Heir.Suite Bid
open AnalyticBridge VerifiedReset Time Push Push.Local Planned.PrimaryIntegral295 PPX Next.Free
open Planned.GuardedAtom Source
open PriceCompiler
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}
variable {M:Sheet G} {K:MapPrices}{V: Targets M K}{Y: Expenses V} {q:ℕ→ℝ} {r:ℕ→ℕ→ℕ}{w:Return.Wages}{D:Rolls M}{A:Register D Y w q} {P: Programs M}
variable (D P V Y r A) (C:ℕ→ℕ→ Record){Θ:Protection D}

abbrev OffTests (T:Delays Θ) := ∀ j x,T.betaEntry j ≤ x →∀ i d,M.first≤ i→ StepStages j i→ d+3≤ i→ Nonempty (Angle j i d (M.profile i).order (D.L j) (M.profile i) (M.profile j) (Pressure.Testing.query M K j i) M.kernel (P j i) (C j i) (V j i) (w j i) (A.o j i) (A.μ j i) x (r j i))
lemma reserveOff (he:∀ j i,StepStages j i→ M.first ≤ i→ (C j i).ε ≤ 1/4) (T : Delays Θ) : ∃ Z : Delays Θ, DelayLe T Z∧∀ U:Delays Θ,DelayLe Z U→OffTests V Y r D A P C U := by
  let U j i d (x:ℝ) := Nonempty (Angle j i d (M.profile i).order (D.L j) (M.profile i) (M.profile j) (Pressure.Testing.query M K j i) M.kernel (P j i) (C j i) (V j i) (w j i) (A.o j i) (A.μ j i) x (r j i))
  have hv (j i:ℕ)(hi:StepStages j i): ∀ᶠ x in atTop,∀ d:ℕ,M.first≤ i→d+3≤ i→U j i d x := by
    by_cases hf:M.first≤ i
    swap; exact Eventually.of_forall (fun _ _ h _=> False.elim (hf h))
    have H (d:ℕ)(h:d ≤ j) : ∀ᶠ x in atTop,U j i d x := aim_off (D.L j) (P j i) (C j i) M.kernel (V j i) _ _ d j i (r j i) (M.profile i) (M.profile j) (A.o j i) (he _ _ hi hf) (M.cut.trans hf) ((M.cut.trans hf).trans hi.1) ((by have h:=(M.profile i).order_ge;omega)) h (A.consumes _ _ hi|>.2.1)
    filter_upwards [(Finset.range (j+1)).eventually_all.mpr (fun i hx=> H i (Nat.le_of_lt_succ (Finset.mem_range.mp hx)))] with x hx d ha h
    exact hx _ (Finset.mem_range.mpr (by have h:=hi.1; omega))
  obtain ⟨x,-,hx,H⟩:= collect_upper T.betaEntry _ fun j=>eventually_transitions j _ _ (hv j)
  exact ⟨{T with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ hv j x hy i d hb ht hc=> H _ _ ((hv.beta j).trans hy) _ ht _ hb hc⟩

abbrev Moved {W: Metals G}{R:Rolls W.p}{A:Alloy W R}{X : Roost.Factor A} {C:ℕ→ℝ} {B:Bid.Worth} (p:Legato.Bandage X C B) :=
    OffTests X.target X.expense X.span R X.shape p.prices p.memberB A.delay
end YM.PhysicalNext.Repeat.Cub
