import YM.OPE.Log.VelourL
import YM.OPE.Log.Calendar
import YM.OPE.Rough.Supply

/-! Schedule with explicit post payments bounded by polynomials in log scale. A fixed
support exponent (choice allowed by pre-L tables) facilitates repricing at intermediate
grouping steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Filter Function Lattice RG Wilson Pressure RG.Supply Push.PriceCompiler Extra.Iteration.Scales
open MergeProof Next.UVStress PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge} {P:Sheet G} {D: Rolls P} {T: Protection D}
structure OnBudget (Q:Levels G) : Prop where
    mesh (m:ℕ) : ((Q.S.block m).val:ℝ) ≤ Q.clock.hatBeta m
    materials (m:ℕ) : (Q.params (m+1)).columns ≤ Q.clock.hatBeta m
    present (m:ℕ) : (Q.params m).columns ≤ Q.clock.hatBeta m
lemma aux_delay (V:Delays T): ∃ W, DelayLe V W∧ ∀ W', DelayLe W W' →
    ∀ {X : Bar W'} (P:Wait X) (Q:Levels G), Paid P Q→ OnBudget Q:=by
    obtain ⟨W,hW,h',hf⟩:= delay_extra V (fun j x=> ((D.L j).val:ℝ) ≤ x ∧ (P.profile j).columns ≤ x ∧ (P.profile (j-1)).columns ≤ x) (fun _ _ _=>True) (fun j=> (eventually_ge_atTop _).and ((eventually_ge_atTop _).and (eventually_ge_atTop _))) (fun _ _=>by simp)
    refine ⟨W,hW,fun W' hp _ Z Q hQ=>⟨fun m=>?_,fun m=>?_,fun m=>?_⟩⟩
    · rw [Extra.Iteration.block_eq hQ]; exact ((hf W' hp).1 _ _ (hQ.pays m)).1
    · rw [params_eq hQ]; exact ((hf W' hp).1 _ _ (hQ.pays m)).2.1
    rw [params_eq hQ]; rcases stepStages_target (step_paid Q m) with h|h <;> rw [h]; exact ((hf W' hp).1 _ _ (hQ.pays m)).2.1; exact ((hf W' hp).1 _ _ (hQ.pays m)).2.2
variable {C: Family G}
set_option quotPrecheck false
open scoped Classical
structure LogPackage (C:Family G)(W:Bid.Worth) (r:ℕ→ℕ)(D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) : Prop extends Package C W r D where
   lightCuts: LightArity C (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) r D
   money: OnBudget C.path.levels
   spare: Tendsto r atTop atTop
   support (m:ℕ): (C.path.levels.params m).supportExponent=100
end YM.OPE.Log
