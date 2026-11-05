import Mathlib.Analysis.Fourier.Convolution
import YM.Next.BOUNDARY.Coordinates
import YM.Next.BOUNDARY.Core
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Dues
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical

/-! Expose drows separately (signs and supports needed independently
on this step). Uses SECTOR_MEASURE currency lemmas for paths and clip;
no differentiated hard mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior Bloch Laurent MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
  
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace

namespace Fabric
section measures
variable {G : Gauge} {c f n : Side} {S : StepData c f}
    {X : Type*} [MeasurableSpace X]

-- No global instance. CLM meas achieved by joint t into V etc.
private lemma packM {I J : Type*} [Fintype J] {g : Config G c → I → J → Pay G}
    (h : ∀ i j, Continuous (fun x => g x i j)) {a : X → (J→G.Color)} (ha : Measurable a)
    {V : X → Config G c} (hV : Measurable V) (i : I) : Measurable (fun x => zip (g (V x)) (a x) i) := by
  have hi : Continuous (fun y : Config G c × (J → G.Color) => zip (g y.1) y.2 i) :=
    cont_zip (fun i j => (h i j).comp continuous_fst) (fun j => (continuous_apply j).comp continuous_snd) i
  have hl : Measurable (fun y : Config G c × (J → G.Color) => zip (g y.1) y.2 i) := hi.measurable
  exact hl.comp (f:=fun x => (V x,a x)) (hV.prodMk ha)

private lemma openM {I J : Type*} [Fintype I] {g : Config G c → I → J → Pay G}
    (h : ∀ i j, Continuous (fun x => g x i j)) {a : X → (I→G.Color)} (ha : Measurable a)
    {V : X → Config G c} (hV : Measurable V) (j : J) : Measurable (fun x => unzip (g (V x)) (a x) j) := by
  have hi : Continuous (fun y : Config G c × (I → G.Color) => unzip (g y.1) y.2 j) :=
    cont_unzip (fun i j => (h i j).comp continuous_fst) (fun i => (continuous_apply i).comp continuous_snd) j
  have hl : Measurable (fun y : Config G c × (I → G.Color) => unzip (g y.1) y.2 j) := hi.measurable
  exact hl.comp (f:=fun x => (V x,a x)) (hV.prodMk ha)

private lemma pairM {v w : X → G.Color} (h : Measurable v) (he : Measurable w) : Measurable fun x => inner ℝ (v x) (w x) := by
  let M : X → G.Color × G.Color := fun x => (v x,w x)
  have hh : Measurable (fun y : G.Color × G.Color => inner ℝ y.1 y.2) := (continuous_fst.inner continuous_snd).measurable
  exact hh.comp (f:=M) (h.prodMk he)

lemma Zm {V Q : X → Config G c} (hV : Measurable V) (hQ : Measurable Q) (i : Bond c) :
    Measurable (fun x => Tube.Z (f:=f) S (Q x) (V x) i) := by
  have hi (p : X → Config G c) (h : Measurable p) : Measurable (fun x => p x i) := (measurable_pi_apply i).comp h
  exact (measurable_const (a:=Real.sqrt S.kernel.penalty)).smul (G.continuous_curvature.measurable.comp
    ((hi _ hV).mul (hi _ hQ).inv))

private lemma monetaryM {V Q : X → Config G c} (hV : Measurable V) (hQ : Measurable Q) (i : Bond c) :
    Measurable (fun x => monetary S (Q x) (V x) i) := by
  have h0 : Continuous (fun y : Config G c × Config G c => monetary S y.1 y.2 i) := by unfold monetary wire; fun_prop
  let M : X → Config G c × Config G c := fun x => (Q x,V x)
  have hf : Measurable M := hQ.prodMk hV
  have ha : Measurable (fun y : Config G c × Config G c => monetary S y.1 y.2 i) := h0.measurable
  exact ha.comp (f:=M) hf

variable {R : ℕ} {T : Tube G S} {P : Teller G} (hT : P.Funds S T)
include hT

lemma xFine {U : X→Config G f} (h : Measurable U) (i : Twin f) : Measurable (fun x => T.Xf R (U x) i) := by
  obtain ⟨a,b,h1,h2⟩ := hT.feeds
  rw [← hT.high] at h1
  exact (plotted_cont h1 R 1 i).measurable.comp h

lemma xCoarse {V : X→Config G c} (h : Measurable V) (i : Twin c) : Measurable (fun x => T.Xn R (V x) i) := by
  obtain ⟨a,b,h1,h2⟩ := hT.feeds; rw [← hT.low] at h2
  exact (plotted_cont h2 R S.patch.L.val i).measurable.comp h

private lemma thinnedM {s : ℝ} (hs : 0≤s) {V : X → Config G c} (hV : Measurable V) :
    Measurable (fun x => T.vision R s (V x)) := by
  obtain ⟨b,l,h1,h2⟩ := hT.feeds; rw [← hT.low] at h2
  exact (env_read h2 R S.patch.L.val s hs).meas.comp hV

-- projections independently (construct dummy positions cumbersome)
private lemma riseM (i : Twin f) (j : Twin c) : Continuous (fun V : Config G c => T.Φ R V i j) := by
  obtain ⟨h1,h2,h3,-⟩ := hT.crosses
  exact leap_cont (Row.rights _ _ h3 P.width.le) ..
private lemma hopM (i : Bond c) (j : Twin c) : Continuous (fun V : Config G c => T.Φ' R V i j) := by
  obtain ⟨h1,h2,h3,-⟩ := hT.crosses
  exact lane_cont (Row.rights _ _ h1 P.width.le) ..
private lemma coM (i : Co c Gain) (j : Twin c) : Continuous (fun V : Config G c => T.N R V i j) := by
  obtain ⟨h1,h2,h3,-⟩ := hT.crosses
  exact lane_cont (Row.rights _ _ h2 P.width.le) ..

lemma mvM {s : ℝ} (hs : 0≤s) {V : X→Config G c} (hV : Measurable V) (i : Twin f) :
    Measurable (fun x => T.Mv R s (V x) i) :=
  packM (riseM hT) (thinnedM hT hs hV) hV i
lemma mwM {s : ℝ} (hs : 0≤s) {V : X→Config G c} (hV : Measurable V) (i : Bond c) :
    Measurable (fun x => T.Mw R s (V x) i) := packM (hopM hT) (thinnedM hT hs hV) hV i

lemma fine {s : ℝ} (hs : 0≤s) (t : ℝ) {U : X→Config G f} (hU : Measurable U) {V : X→Config G c} (hV : Measurable V) (i : Cell f) :
    Measurable (fun x => T.workF R (U x) (V x) t s i) := by
  obtain ⟨a,b,h1,h2⟩ := hT.feeds; rw [← hT.high] at h1
  unfold workF; refine Measurable.add ((env_crown h1 ..).meas.comp hU) ?_
  refine Finset.measurable_fun_sum _ fun j _ => ?_
  have hf := xFine (R:=R) hT hU (i,j); have hl := mvM (R:=R) hT hs hV (i,j)
  exact ((hl.norm.pow_const 2).div_const 2).sub (pairM hl hf)

lemma bond {s : ℝ} (hs : 0≤s) {V Q : X→Config G c} (hV : Measurable V) (hQ : Measurable Q) (i : Bond c) :
    Measurable (fun x => T.workI R (Q x) (V x) s i) := by
  have hf := Zm (S:=S) hV hQ i; have hl := mwM (R:=R) hT hs hV i
  exact (monetaryM (S:=S) hV hQ i).add (((hl.norm.pow_const 2).div_const 2).sub (pairM hl hf))

set_option maxHeartbeats 800000 in
lemma levels {s : ℝ} (hs : 0≤s) {U : X→Config G f} (hU : Measurable U)
    {V Q : X→Config G c} (hV : Measurable V) (hQ : Measurable Q) (i : Cell c) :
    Measurable (fun x => T.workC R (V x) s i) ∧ Measurable (fun x => T.workL R (U x) (Q x) (V x) s i) ∧
      Measurable (fun x => T.workD R (V x) s i) := by
  have hv := thinnedM (R:=R) hT hs hV
  have ht j : Measurable (fun x => T.vision R s (V x) j) := (measurable_pi_apply j).comp hv
  let K x := Tube.Z S (Q x) (V x)
  have hk : Measurable K := measurable_pi_lambda _ fun _ => Zm (S:=S) hV hQ _
  have hh : Measurable (fun x => T.Xf R (U x)) := measurable_pi_lambda _ fun _ => xFine (R:=R) hT hU _
  let M x := zip (T.N R (V x)) (T.vision R s (V x))
  have hm : Measurable M := measurable_pi_lambda _ fun j=>packM (coM hT) hv hV j
  obtain ⟨a,b,h1,h2⟩ := hT.feeds; rw [← hT.low] at h2
  refine ⟨?_,?_,?_⟩
  · unfold workC
    refine (Finset.measurable_fun_sum _ (fun (j : Bool) _ => ?_)).sub ((env_crown h2 ..).meas.comp hV)
    exact (pairM (ht (i,j)) (xCoarse (R:=R) hT hV (i,j))).sub (((ht (i,j)).norm.pow_const 2).div_const _)
  · unfold workL; refine Finset.measurable_fun_sum _ (fun j hj => ?_)
    have hp := openM (riseM (R:=R) hT) hh hV (i,j)
    have he := openM (hopM (R:=R) hT) hk hV (i,j)
    exact pairM (ht (i,j)) ((hp.add he).sub (xCoarse (R:=R) hT hV (i,j)))
  unfold workD; refine Finset.measurable_fun_sum _ (fun j hj => ?_)
  have ha := openM (riseM (R:=R) hT) (measurable_pi_lambda _ (mvM (R:=R) hT hs hV)) hV (i,j)
  have he := openM (hopM (R:=R) hT) (measurable_pi_lambda _ (mwM (R:=R) hT hs hV)) hV (i,j)
  have hz := openM (coM (R:=R) hT) hm hV (i,j)
  have hl := ht (i,j)
  exact (pairM hl (hl.sub ((ha.add he).add hz))).div_const (2:ℝ)

lemma moment {s : ℝ} (hs : 0 ≤ s) {V : X→Config G c} (hV : Measurable V) (i : Co c Gain) :
    Measurable (fun x => T.workN R (V x) s i) :=
  (((packM (coM (R:=R) hT) (thinnedM hT hs hV) hV i).norm).pow_const 2).div_const _

lemma core (x : ℝ) (k : S.Choices) (i : Slots S) : Measurable (fun V : Config G c => base T x V k i) := by
  obtain ⟨s,j|j⟩ := i
  have hl : Continuous (fun V : Config G c => replica S.ratio V) := by
    refine continuous_pi fun i=>?_ ; unfold replica; split <;> fun_prop
  · have hf : Measurable (fun V : Config G c => facade S s V 0) := by
      simp_rw [fixed_facade]; exact (continuous_pull _ _).measurable.comp hl.measurable
    exact (xFine (T:=T) (R:=till x) hT hf j).sub (mvM (R:=till x) hT (temp_nonneg _) (continuous_pull s 0).measurable j)
  · have hf : Measurable (fun V : Config G c => facade S s V 0) := by
      simp_rw [fixed_facade]
      apply (continuous_pull _ _).measurable.comp
      apply Continuous.measurable
      refine continuous_pi fun i=>?_ ; unfold replica; split <;> fun_prop
    have hz := Zm (S:=S) (continuous_pull (G:=G) s (0:Site c)).measurable ((S.prediction_meas (funds_branch hT) (choice s k)).comp hf) j
    exact hz.sub (mwM (R:=till x) hT (temp_nonneg _) (continuous_pull s 0).measurable j)
end measures
end Fabric
end YM.PhysicalNext.Dictionary
