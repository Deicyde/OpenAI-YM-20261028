import YM.SharpGram.Weak.Pairing
import YM.Extra.WEAK_SCALING_ACTLAW.Adjust
import YM.Push.FINITE_DETECTION.Test
/-!
# Correct to a single compatible weak measuring frame, through D

We switch on all pairs at once (mixed at the *same* D station, not plucked
from independently calibrated ones). Use a complex first-slot detector for
prices of the cross adjust; after that the real-part lower and norm upper
of Weak.Pairing transfer too. The final basis can be chosen as
Extra.WeakScaling.Graded (all incl and all H symmetries real, unit) and used
at `tiltLength` (doesn't require the tilted form itself to enjoy the mirror
symmetry).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak.Portfolio
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank PhysicalNext.RankCovariance
open Org Spec Next.Rank.Station Further.CorrectedLift Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Push.FiniteDetection.Free
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(U:Final C f S)
variable {D:ℕ}{u:Filter (ℕ×ℕ)}{H:C.Makes} (X : Portfolio C H D u)
local notation "F"=> standard C
local notation "σ"=> U.room.kernel.spin
local notation "θ"=> Maxwell.Free.spin_free C.labels

-- Work via Fin pair tag read for differently raised labels
def firstProbe {L : Register G} (T : Table L) {d : ℕ} (e : ℕ) (p : Points 2) (q : T.Field d) : T.Field e →ₗ[ℂ] ℂ :=
  Work.A15.front p (![⟨d,q⟩] : Fin 1 → T.Tag) _
lemma firstProbe_read {L:Register G} (T : Table L) {d e : ℕ} (p : Points 2) (x : T.Field d) (y : T.Field e) :
    firstProbe T d p y x = T.useAt T p ![⟨d,x⟩,⟨e,y⟩] := Work.A15.front_apply p ..
lemma firstProbe_eq {L:Register G} (T : Table L){q : Fin 2 → T.Tag} {x : Points 2} :
    firstProbe T (q 0).1 x (q 1).2 (q 0).2=T.useAt T x q := by
  rw [firstProbe_read,show (![⟨_,(q 0).2⟩,⟨_,(q 1).2⟩] : Fin 2 → T.Tag)=q from ?_]
  funext i; fin_cases i <;> rfl
lemma readSecond {L:Register G} (T : Table L) {d : ℕ} (p : Points 2)
    (x y : T.Field d) : firstProbe T d p y x = T.classMoment T (fun _=>d) p ![x,y] := by
  let q : Fin 2 → T.Tag := fun i=> ⟨d,(![x,y] : Fin 2→T.Field d) i⟩
  exact firstProbe_eq T (q:=q)
lemma ascend {L:Register G} (T : Table L) (P : DiffPlan T) (h : P.Inclusions T) {d e n : ℕ} (he : d ≤ e) (x : Points 2) (hx : x ∈ conf 2) (v : T.Field d) (z : T.Field n) : firstProbe T e x z (P.rise he v) = firstProbe T d x z v := by
  rw [firstProbe_read,firstProbe_read]
  exact h.kernels _ _ hx _

variable {W r T0} (T : OPE.TableTickets C W r T0) [u.NeBot] (hf : u ≤ f.fuse) (hG:G.Simple)
include U hf T hG
lemma twoBelow (d e : Fin (D+1)) (v : (F).Field d) (z : (F).Field e) :
    Tendsto (fun k => firstProbe S d (X.detector k) (X.draw S k e z) (X.draw S k d v)) atTop
      (𝓝 (firstProbe (F) d detectors z v)) := by
  let t := (![d,e] : Fin 2 → Fin (D+1))
  let a : (i : Fin 2) → C.label (t i) := Fin.cons (α := fun i=> C.label (t i)) (ladder C d v) (Fin.cons (ladder C e z) (fun i=> Fin.elim0 i))
  have he := X.twoC U hG T hf (t:=t) a
  let r : Fin 2 → (F).Tag := fun i=>⟨(t i).val, (F).project (t i) (a i)⟩
  let q k : Fin 2 → S.Tag := fun i=>⟨(t i).val,X.visible S k (t i) (a i)⟩
  change Tendsto (fun k=> S.useAt S _ (q k)) _ (𝓝 ((standard C).useAt (F) detectors r)) at he
  rw [← firstProbe_eq (F)] at he
  have hr : firstProbe (F) (r 0).1 detectors (r 1).2 (r 0).2=firstProbe (F) d detectors z v := by
    change firstProbe _ (d:ℕ) _ ((F).project _ (ladder C _ z)) ((F).project _ (ladder C _ v))=_
    rw [ladder_reads,ladder_reads]
  rw [hr] at he
  refine he.congr (fun k=>?_)
  exact (firstProbe_eq S (q:=q k)).symm

omit hG T hf
-- fallback only for small k or unwitnessed horizons
section
omit [u.NeBot]
include U
lemma someChart (d : ℕ) : Nonempty (YM.Spin.change S d) := by
  obtain ⟨H,h⟩:=U.phase.transport.comparator
  obtain ⟨e,h⟩:= h d
  exact ⟨e.symm⟩

def chart (k d : ℕ) : YM.Spin.change S d := if h:d ≤ D then
    let e := X.draw S k ⟨d,Nat.lt_succ_of_le h⟩
    if H : Bijective e then LinearEquiv.ofBijective e H else Classical.choice (someChart U d)
  else Classical.choice (someChart U d)
lemma chart_eq (k : ℕ) (d : Fin (D+1)) (h : Bijective (X.draw S k d)) (x : (F).Field d) :
    X.chart U k d x=X.draw S k d x := by unfold chart; rw [dif_pos (Nat.le_of_lt_succ d.isLt), dif_pos h]; rfl
end
include hG T hf
lemma chartDraw (d : Fin (D+1)) : ∀ᶠ k in atTop, Bijective (X.draw S k d) ∧ ∀ x : (F).Field d, X.chart U k d x=X.draw S k d x := by
  obtain ⟨δ,he,hc⟩:= freely (C:=C) d
  filter_upwards [X.certified U hG T hf d δ he hc] with k ⟨_,_,_,ha⟩
  exact ⟨ha,fun v => X.chart_eq U k d ha v⟩

lemma extraStep (d e : Fin (D+1)) (v : (F).Field d) (z : (F).Field e) :
    Tendsto (fun k => firstProbe S d (X.detector k) (X.chart U k e z) (X.chart U k d v)) atTop
      (𝓝 (firstProbe (F) d detectors z v)) := by
  apply (X.twoBelow U T hf hG d e v z).congr'
  filter_upwards [X.chartDraw U T hf hG d,X.chartDraw U T hf hG e] with k hk he
  rw [hk.2, he.2]

local notation "V"=> U.sector.derivatives
local notation "B"=> Maxwell.Free.scheme C.labels
set_option maxHeartbeats 800000 in
lemma stepFits : Extra.WeakScaling.Near V B (chart U X) D := by
  intro d hd v
  let e : Fin (D+1) := ⟨d+1, by omega⟩
  let r : Fin (D+1) := ⟨d, by omega⟩
  let β := Module.finBasis ℂ ((standard C).Field e)
  let b0 := Push.FiniteDetection.freeMatrix (C:=C) β detectors
  let b (k : ℕ):= LinearMap.pi (fun i: Fin (Module.finrank ℂ ((F).Field e)) =>
    (firstProbe S e (X.detector k) (X.chart U k e (β i))).comp (X.chart U k e).toLinearMap)
  have hv : ∀ x i, b0 x i = firstProbe (F) e detectors (β i) x :=
    fun x i => (readSecond (F) _ x (β i)).symm
  apply Work.A04.tendsto_of_fitted b b0.toLinearMap (Push.FiniteDetection.free_injective β) 
  · intro x
    refine tendsto_pi_nhds.mpr fun i => ?_
    change Tendsto _ atTop (𝓝 (b0 x i))
    rw [hv]
    exact X.extraStep U T hf hG e e x (β i)
  refine tendsto_pi_nhds.mpr fun i => ?_

  change Tendsto (fun k => firstProbe S e (X.detector k) (X.chart U k e (β i)) (X.chart U k e ((X.chart U k e).symm ((V).rise (show d≤e.val from d.le_succ) (X.chart U k d v))))) atTop (𝓝 (b0 ((B).rise (show d≤e.val from d.le_succ) v) i))
  rw [hv]
  rw [ascend (F) B (Maxwell.Free.scheme_filters _) _ detectors detectors_in]
  simp_rw [LinearEquiv.apply_symm_apply, ascend S V U.phase.transport.injection _ _ (X.detector_conf _)]
  exact X.extraStep U T hf hG r e v (β i)

-- an H-real filtration-compatible identification in every pose of a window.
lemma symmetrical (d:Fin (D+1)) : ∀ᶠ k : ℕ in atTop, YM.Spin.realH σ θ (X.chart U k d) := by
  filter_upwards [X.onLevel,X.chartDraw U T hf hG d] with k ⟨_,_,hp,hZ⟩ hE
  constructor
  · intro s x
    rw [hE.2,hE.2]
    change X.visible S k d (ladder C d _) = _
    rw [ladder_spin]
    exact commutesTurn hp U hf hZ s d _
  intro x
  rw [hE.2,hE.2]
  change X.visible S k d (ladder C d _) = _
  rw [ladder_conj]
  exact realStar hp U hf hZ d _

/-- Extra.WeakScaling's graded notion: full exact across the same Final d through D.
This uses a compatible basis, steering the noncoherent `Portfolio.draw`. -/
lemma tune_grades :
    ∃ p : ℕ → ∀ d : ℕ, YM.Spin.change S d,
      (∀ᶠ k : ℕ in atTop, Extra.WeakScaling.Graded V B σ θ (p k) D) ∧
      ∀ d : Fin (D+1), ∀ v : (F).Field d, Tendsto (fun k => (X.chart U k d).symm (p k d v)) atTop (𝓝 v) := by
  let X' := X.chart U
  choose P hP hx hy using (Extra.WeakScaling.retraction (Maxwell.Free.hierarchy C.labels) B (Maxwell.Free.scheme_filters _) (Maxwell.Free.phase_orientation _))
  let q := Extra.WeakScaling.rotateChart V B P X'
  have hr := X.stepFits U T hf hG
  refine ⟨q,?_,fun d x=> Extra.WeakScaling.relative hr (Nat.le_of_lt_succ d.isLt) x⟩
  have ht(d:Fin (D+1)):= (Extra.WeakScaling.eventually_unit (P:=P) hr (show d.val ≤ D from Nat.le_of_lt_succ d.isLt)).and ((X.symmetrical U T hf hG d).and ((X.chartDraw U T hf hG d).and (drawUnit (S:=S) X hf d)))
  filter_upwards [eventually_all.mpr ht] with k hk
  have hF d (hd:d ≤ D) (x : (F).Field d) : q k d x=Extra.WeakScaling.adjusted V B P (X' k) d x := Extra.WeakScaling.rotate_eq (hk (⟨d,Nat.lt_succ_of_le hd⟩:Fin (D+1))).1 x
  have hA d (hd:d ≤ D) : YM.Spin.realH σ θ (X' k d) ∧ X' k d ((standard C).unit d)= S.unit d := by
    let j : Fin (D+1) := ⟨d,Nat.lt_succ_of_le hd⟩
    obtain ⟨_,h,hv,ht⟩:= hk j
    exact ⟨h,(hv.2 ((standard C).unit d)).trans ht⟩
  obtain ⟨h1,h2⟩ := Extra.WeakScaling.adjusted_exact (h:=U.room.kernel) (H:=Maxwell.Free.hierarchy C.labels) U.phase.transport.injection (Maxwell.Free.scheme_filters _) U.phase.transport.rights (Maxwell.Free.phase_orientation _) (fun d => ⟨hP d,hx d,hy d⟩) hA
  constructor
  · intro d hd; simp_rw [LinearEquiv.coe_coe,hF d hd]; exact h1 d hd
  intro d e he hd; simp_rw [LinearEquiv.coe_coe,hF e hd,hF d (he.trans hd)]; exact h2 d e he hd

local instance {G: Gauge} {L:Register G} (S:Table L)(d:ℕ) : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _

-- transfer real-part actual estimate to the compatible measuring frames
-- private case change

def inBasis (k : ℕ)(d : ℕ) (Y : (F).Field d ≃ₗ[ℂ] S.Field d) := pullBoth (Y.toLinearMap.restrictScalars ℝ) (Y.toLinearMap.restrictScalars ℝ) (glass S σ d (X.detector k))

lemma aligned (d: Fin (D+1)){P : ℕ → (F).Field d ≃ₗ[ℂ] S.Field d}
    (he : ∀ x, Tendsto (fun k => (X.chart U k d).symm (P k x)) atTop (𝓝 x)) :
    Tendsto (fun k => inBasis U X k d (P k)) atTop (𝓝 (model C d)) := by
  refine formsLimits _ _ (fun i j => ?_)
  let Z k := (P k).trans (X.chart U k d).symm
  have ht := X.detectorActual U hG T hf d
  have h := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (ht.prodMk_nhds (he i))
  have h' := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds (he j))
  refine h'.congr' ?_
  filter_upwards [X.chartDraw U T hf hG d] with k hk
  change glass S σ d (X.detector k) (X.draw S k d (Z k i)) (X.draw S k d (Z k j))=glass S σ d (X.detector k) (P k i) (P k j)
  rw [← hk.2,← hk.2]; unfold Z; rw [LinearEquiv.trans_apply,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
end YM.SharpGram.Weak.Portfolio
