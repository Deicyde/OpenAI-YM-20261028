import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Seaports
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.Bungalow
import YM.MergeProof.North.Focal
import YM.MergeProof.South.Window
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Corridor
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsColumnL
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Reroute
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.MultipleContact.Bunch.Focal

/- generalized from YM.MergeProof.North.Harvest to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories 
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}(H:History G) (N p:ℕ) {m : ℕ}
local notation "Ξ"=> Aged V slot
local notation "Γ"=> Bud V
set_option quotPrecheck false
local notation "L"=> H.S.side N p
local notation "R"=> H.rep N p
variable (F:Name V slot→ Config G (H.S.side N p)→ℂ)
local notation "G'"=> (fun i U=> ∏ b:slot,F (i,b) U)
local notation "x₀"=> birth Ξ (R N) F
local notation "xp"=> birth Γ (R N) G'
lemma glean (hp : Integrable (birth (Aged V slot) (H.rep N p N) F) (prior G _)) (hm:m≤N) : gust H N p N xp m hm=fun U=> reap (gust H N p N x₀ m hm U):=by
    induction hm using Nat.decreasingInduction with
    | self=> funext U; rw [gust_base,gust_base]; ext s; change ((birth _ _ _) U).part s=((birth _ _ _) U).part (plena s); unfold birth Mach; simp only [Poly.part_smul, pass_fire]; congr 1; unfold plena; rw [prod_product]
    | of_succ i hi IH=> rw [gust_step _ _ _ _ _ hi, IH]; funext U; rw [gust_step _ _ _ _ _ hi]; unfold StepData.push; let L':= (reap (V:=V) (slot:=slot)).restrictScalars ℝ; have he:= L'.integral_comp_comm (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i+1))) U _ (gust_live H N _ _ _ hp hi)); simp_rw [L'.map_smul] at he; exact he -- direction
lemma glean_in (hp : Integrable (birth (Aged V slot) (H.rep N p N) F) (prior G _)) : Integrable xp (prior G _):=by
    have hv := glean H N p F hp le_rfl; rw [gust_base] at hv; simp_rw [gust_base] at hv; rw [hv]; exact ((reap (V:=V)).restrictScalars ℝ).integrable_comp hp
end
end YM.MergeProof.BatchRibbons
