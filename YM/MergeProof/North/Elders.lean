import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Folio
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MergeProof.Domino
import YM.MergeProof.North.Focal
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.TwoMasks
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Corral
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Novas
import YM.Planned.PRIMARY_INTEGRAL_295.Thrift
import YM.UVNext.COUPLING_RESET.Prefix
import YM.UVNext.COUPLING_RESET.Tuning



set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Source Marker Accent Ribbon Local  Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories 
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:RG.History G) (d:ℕ) {N m p:ℕ}
set_option quotPrecheck false
local notation "F"=> (Labels.frames G).level d
local notation "B"=> Next.Foundations.localSection G d
local notation "A"=> Next.Foundations.hol G
local notation "f"=> H.S.side (m+1) p
local notation "c"=> H.S.side m p
local notation "X0"=> H.rep N p m
local notation "X1"=> H.rep N p (m+1)
local notation "Z"=> H.levels.clock.op m p
local notation "L"=> (H.S.block m)
local notation "χ"=> ((↑(H.S.block m).val:ℂ)^d)
local notation "P0"=> (H.levels.budget m)
local notation "P1"=> (H.levels.budget (m+1))
variable {x e t u w a y :ℝ} {I: V→ℝ} {J:V→ℝ}
    {θ:Config G (H.S.side (m+1) p)→Poly (Bud V)} {o:V→Site (H.S.side (m+1) p)}
    {G': V→ Config G (H.S.side (m+1) p)→ℂ} {K: V→ℕ→ Config G (H.S.side (m+1) p)→ℂ}
    {D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} (C:ℕ→ℕ)
    {P:V→Motion}{E:V→Site (H.S.side m p)}{v:V}
    {l:V→ℂ}
set_option quotPrecheck false
local notation "Ω"=> (Z).ratio.parent ∘ o
local notation "ρ"=> (Z).push (X1).beta θ
local notation "T"=> fun i=> (Z).ratio.embed (E i)
local notation "kp"=> fun i=> profile (X1).activities (K i)
-- No P v base assumption because symmetry from replicas explicitly ALL i says not trivial but drives proof at v too. uses actual budget.Y.S.
lemma crescent {Q:Coefficient ((Labels.frames G).level d) (H.S.side m p)} {F':Config G (H.S.side m p)→Poly (Bud V)} (hg: Q.Format 0 A (X0))(hh: Q.remBound 0 (X0) (kappa H m) a)(hx:(F).coeffSize Q.x ≤ y) (h:Served (X0) (fun i=> radiant (χ⁻¹) (P i) (E i) (Q.exponentialEntry 0 B (X0))) (fun i=> sunny X0 Q.forced (P i) (E i) (χ⁻¹)) F' E J ((P0).supportExponent) 1):
    ∃ Q':Coefficient F c,Q'.Format 0 A (X0) ∧ Q'.remBound 0 (X0) (kappa H m) ((H.S.a (m+1)^d)*a) ∧ (F).coeffSize Q'.x ≤ (H.S.a (m+1)^d)*y ∧
       Served (X0) (fun i=> radiant (alto H m d) (P i) (E i) (Q'.exponentialEntry 0 B (X0))) (fun i=> sunny X0 Q'.forced (P i) (E i) (alto H m d)) F' E J ((P0).supportExponent) 1:=by
    let z:=(alto H (m+1) d)⁻¹; let U:= Extra.Histories.stretch z Q; have hf:‖z‖= H.S.a (m+1)^d:=by unfold z; rw [norm_inv, alto_norm,inv_inv]
    rw [← hf]
    refine ⟨U,Extra.Histories.stretch_format _ hg,Extra.Histories.stretch_rem z hh,?_,?_⟩
    · exact le_trans (le_of_eq (Size.smul _ z Q.x)) (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have he(k:Motion): scalar k z=z:=by unfold z alto Motion.scalar; split <;>simp
    have hy:z*alto H m d=χ⁻¹:=by
       have ht:alto H m d≠0:= inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (H.S.a_pos _).ne')); unfold z; rw [alto_at, mul_inv_rev, mul_comm _ χ⁻¹, mul_assoc,inv_mul_cancel₀ ht,mul_one] -- check
    let a₁:=Q.exponentialEntry 0 B (X0)
    have hq: U.exponentialEntry 0 B (X0)= z • a₁:=by
       funext v; have hb(j): U.maskedTerm X0 j v=z* Q.maskedTerm X0 j v:= Extra.Histories.masked_scale .. -- mass
       change Extra.Histories.part B 0 (X0) v (z • Q.x) +∑' j,U.maskedTerm (X0) j v=z*(Extra.Histories.part B 0 (X0) v Q.x+ ∑' j,Q.maskedTerm (X0) j v); simp only [map_smul,hb, smul_eq_mul,tsum_mul_left,mul_add]
    convert! h using 1
    · funext i v; rw [hq]; unfold radiant; simp only [Pi.smul_apply,stepUp, Motion.scalar_mul,smul_eq_mul]; rw [he,← mul_assoc, mul_comm _ z,hy]
    funext i p v; unfold sunny; rw [show profile (X0).activities U.forced= _ from profile_scale _ Q.forced z]
    simp only [floatUp, Pi.smul_apply, stepUp, Motion.scalar_mul,smul_eq_mul];rw [he, ←mul_assoc, mul_comm _ z,hy]
end YM.MergeProof.Ribbons
