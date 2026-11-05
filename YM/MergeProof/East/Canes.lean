import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Core
import YM.MergeProof.Marco
import YM.Next.RANK.Swath
import YM.Next.RANK.TrueWind


/-! Rotation at all the transported origin branches of this invoice -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Lattice Wilson Spindle  Price Source Source.Drops MeasureTheory Corona
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d k N p i:ℕ}
open Extra.Histories
-- General family‐not property; supplied through Freight
def ParadeX (C : Family G) : Prop := ∀ d k, C.ref d≤ k → ∀ N p,k ≤ N → ∀ s:Signed,∀ v:C.label d,
    awake C d k N p ((C.labels.level d).act s.ortho v)=(C.labels.level d).act s.ortho (awake C d k N p v) ∧
    ∀ U : Config G (C.side k p), flags (C.path.rep N p k).p.threshold U=∅ → awakeFull C k N p v (pull s 0 U) = awakeFull C k N p ((C.labels.level d).act s.ortho v) U
private lemma when_all {n:Side}(R : Rep G n) (U : Config G n) (hr : flags R.p.threshold U = ∅) (F : Labels.Frame G d) (S : SectionData F) (P : Coefficient F n) :
    0 < R.eval U ∧ P.density 0 S R U = (R.eval U:ℂ) * P.exponentialEntry 0 S R U := by
  refine ⟨?_,?_⟩
  · unfold Rep.eval; rw [Activities.gas_one _ _ hr, mul_one]; exact Real.exp_pos _
  have hg (p : Finset ℕ) : P.marked R p U=0 := by
    unfold Coefficient.marked; split; swap; · rfl
    rename_i h
    obtain hv|⟨i,hi⟩:=p.eq_empty_or_nonempty
    · subst p; exact Finset.sum_empty
    have hx : ((R.activities.forced i).inventory)⊆ Finset.biUnion p (fun i=> (R.activities.forced i).inventory) := Finset.subset_biUnion_of_mem (fun i => (R.activities.forced i).inventory) hi
    rw [h.2, hr] at hx; exact False.elim ((R.activities.forced i).inventory_ne.ne_empty (Finset.subset_empty.mp hx))
  unfold Coefficient.density; simp_rw [hg]; simp
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Graces Bandage
open Cub Circlet Graces Roost Planned.GuardedAtom
variable {M: Metals G}{P:Supply.Rolls M.p}{A:Alloy M P}{X:Factor A}{T:Bolt A}{t:ℕ→ℕ}{K:Bid.Worth}{h:Nest X T}
lemma enclosing (Y:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail T) N p) {D:∀ N p m,m<N→YM.MergeProof.GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m)}
   (hy:∀ d N p:ℕ,t d ≤ N→ Freight T h N p d (Y d N p) (t d) K (D N p)) :
    let C:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t Y
    C.Makes→ ParadeX C:=by
    intro C hC d k hd N p hN s v; obtain ⟨Z,hZ,he,hS,hQ⟩:=hy d N p (hd.trans hN)
    let W:= Y d N p; let F:= (Labels.frames G).level d; let R := C.path.rep N p k
    let Q:= F.act s.ortho; let V:= W.terminal.symm v; let K:= hC.calibrated d N p (hd.trans hN)
    have hV: W.terminal.symm (Q v)=Q V:=by
       apply W.terminal.injective; rw [LinearEquiv.apply_symm_apply,show W.terminal _=Q (W.terminal V) from K.orients s V]; rw [W.terminal.apply_symm_apply]
    let J:= Z.tone k; have hY:= hS.earned k hd hN
    have h1: Spindle.parcel C d k N p v=J.plays V:=by change (Y d N p).entries k V= _; rw [he];rfl
    have h2: Spindle.parcel C d k N p (Q v)=J.plays (Q V):=by
       change (Y d N p).entries k (W.terminal.symm _) = _; rw [hV,he];rfl
    constructor
    · unfold Price.awake; change _ • ((Spindle.parcel C d k N p _).x) = Q (_ • ((Spindle.parcel C d k N p v).x)); rw [map_smul,h2,h1,hY.currents,hY.currents]; exact congr_arg (_ • ·) (hY.moves V (s,false)).symm
    intro U hu; unfold awakeFull; rw [h1,h2]; apply congr_arg
    apply mul_left_cancel₀ (show (R.eval U:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (when_all R U hu _ (C.localSection d) (J.plays V) |>.1.ne') ) -- infer P
    obtain ⟨m⟩:= (hC.wilson.represents N p k hN).good.labels.moves s 0
    have hh : flags R.p.threshold (pull s 0 U)=∅:= by
       apply Finset.image_injective (f:=affine s 0) (Thirst.sends s (0:Site (C.side k p))).injective
       rw [Work.H03.flags_send ..]; rw [show flags R.p.threshold U = ∅ from hu]; simp
    have hs: (R.eval (pull s 0 U):ℂ)*(J.plays V |>.exponentialEntry 0 (C.localSection d) R (pull s 0 U))=(R.eval U:ℂ)*(J.plays (Q V)|>.exponentialEntry 0 (C.localSection d) R U):=by
       rw [← (when_all R _ hh _ _ _).2, ← (when_all R _ hu _ _ _).2]; exact congr_fun (hY.travels V (s,false)) U
    rwa [Push.Local.eval_pull m] at hs
end YM.Next.Rank.East
