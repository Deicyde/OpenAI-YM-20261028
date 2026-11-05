import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.Coast
import YM.MergeProof.Paddle
import YM.Next.RANK.HomeSync
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
import YM.ProofPorts.GRID_REAL_MODELS_ESTIMATES_20261012.Author


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
open GridApprox
variable (J:ℕ) {hV:J≤k}{hN:k ≤ N}
def hands (v:ℕ) (i:Site (C.side v p)):= let t:= center C.S p (le_refl v) 0; dye (t.omega i) (t.hand i)
lemma handmove (he:J ≤ k) (q:Config G (C.side k p)→ℂ) (i:Site (C.side J p)) : stepUp (hands C p J i) (Mix.camp C p J k i) q=(center C.S p he 0).copy i q:=by
    let t:= center C.S p he 0; let v:=hands C p J i; have hg:v=dye (t.omega i) (t.hand i):=rfl
    have hx:Mix.camp C p J k i=(center C.S p he 0).translateBy i:=by
       rw [show (center C.S p he 0).translateBy i=anchor C.S p he i from tile_translate ..]; unfold Mix.camp; simp only [dif_pos he]
    funext U; change scalar v _=t.copy i q U; rw [hx,hg];rw [calling];rfl
lemma handneg (he:J ≤ k) (q:Config G (C.side k p)→ℂ) (i:Site (C.side J p)) : -(center C.S p he 0).copy i (-q)=(center C.S p he 0).copy i q:=by funext U; unfold Tiling.copy; split <;> simp
section
variable {I:Type}[Fintype I](X:I→ Config G (C.side k p)→ℂ) (s:I→ℂ)(e:J ≤ k)(u:k≤N)(Y:I→ C.label d) (b:C.label d)
    (t:ℕ)(hc:GridApprox.room C.path.levels J k t)(hX:∀ i, Interior (GridApprox.window (0:Site (C.side k p)) t) (X i))
include t X hX H
local notation "Z"=> ∑ i,(-s i) • X i
set_option maxHeartbeats 800000 in
lemma posing {A:ℝ}{c:ℝ}(he:0≤A)
   (hz : ∑ i, ‖s i‖ ≤ c)(hL:b=∑ i,s i • Y i)
   (hC:∀ b:C.label d,Interior ((center C.S p (e.trans u) 0).chamber 0) (C.O N p b 0))
   (hl:∀ i, (center C.S p (e.trans u) 0).rootTest (C.beta N p) (backTo T N p u (X i)- C.O N p (Y i) 0) ≤ A) (hR:GridApprox.room C.path.levels J k t): Interior (GridApprox.window (0:Site (C.side k p)) t) (Z) ∧ Interior ((center C.S p (e.trans u) 0).chamber 0) (backTo T N p u (Z)) ∧
       (center C.S p (e.trans u) 0).rootTest (C.beta N p) (-backTo T N p u (Z)-C.O N p b 0) ≤ c*A :=by
    have hα: Interior (GridApprox.window (0:Site (C.side k p)) t) (Z):= ProofPorts.GridRealModelsEstimates20261012.interior_sum _ _ (fun i _=> (hX i).scale (-s i))
    have hh{F':Config G (C.side k p)→ℂ}(hf:Interior (GridApprox.window 0 t) F'):Interior ((center C.S p (e.trans u) 0).chamber 0) (backTo T N p u F'):=by
       apply (backTo_local T N p e u 0 t _).enlarges (room_fits p C.path.levels t e u hR _); rw [show anchor C.path.S p e 0=0 from (C.S.toDepth _ _).root.map_zero]; exact hf
    refine ⟨hα,hh hα,?_⟩; let A':=(C.linearO N p d 0).mk' _; let t':= fun i=> backTo T N p u (X i); let y i:= C.O N p (Y i) 0
    rw [show backTo T N p u (Z)=_ from ProofPorts.GridRealModelsEstimates20261012.backTo_linSum (C:=C) N p u X (fun i=>-s i) (fun i=>cylinder_env (hX i)), hL,show C.O N p (∑ i,s i • Y i) 0=∑ i,s i • y i from by change A' _=∑ i,s i • A' (Y i); rw [map_sum]; simp_rw [map_smul], show -(∑ i,(-s i) • t' i) - ∑ i,s i • y i= ∑ i,s i • (t' i-y i) from by simp_rw [neg_smul, Finset.sum_neg_distrib, neg_neg,smul_sub,Finset.sum_sub_distrib]]
    apply (Next.UVStress.root_sum (center C.S p (e.trans u) 0) (C.beta N p) Finset.univ (fun i=>t' i-y i) s (fun i _=> Next.UVStress.minus (hh (hX i)) (hC (Y i))) (seamless H N p)|>.2).trans; refine le_trans (Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (hl i) (norm_nonneg (s i)))) ?_; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hz he
end
end YM.MergeProof
