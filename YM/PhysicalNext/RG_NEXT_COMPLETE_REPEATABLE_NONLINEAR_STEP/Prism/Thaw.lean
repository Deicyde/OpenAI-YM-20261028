import YM.Next.MULTISOURCE.Tome
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Space
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Tails
import YM.Push.LOCAL_SPLITTING.Slices

/-!
# Tail split at a paid-I ledger. Close erf on normalized T laws.

All portals tied to true η `(Q β−β*)`; avoid faking station. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Prism
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E→ Config G c} {p : E} {n : ℕ} {v N Q K δ τ L : ℝ}
variable (X : Coat T F) {I : Type} {Y : Support c} (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (h : Intake P T X.x R) (hp : Scrim X a) {ζ d A t : ℝ} (ht : Canary G d A)
variable (A' : Anthem n) (hs : ∀ (u:Prices G I), ‖u‖≤ L→ Score X i R a q κ b D u K d ζ δ N Q A' Z p)
    (hτ : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) τ) (hk : τ≤ K)

section outage
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def outage (v : ℝ) : Set (ι→ℝ) := {z | ∃ i, v ≤ |z i|}
omit [DecidableEq ι] in
lemma outageSet (v : ℝ) : MeasurableSet (outage (ι:=ι) v) := by
  unfold outage; simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (f:=fun i=>{z:ι→ℝ| v ≤ |z i|}) (fun i=>
    measurableSet_le measurable_const ((measurable_pi_apply _).abs)) -- edit

def spentP (N M t:ℝ) := N*(2*Real.exp (-t+M/2))
lemma spent (v t:ℝ) {C : Matrix ι ι ℝ} (hp : C.PosSemidef) (hz:∀ a:ι→ℝ,dotProduct a (C*ᵥ a)≤v*dotProduct a a)
    (hN : (Fintype.card ι:ℝ) ≤ N) : (Gaussian.cloud C).real (outage t) ≤ spentP N v t := by
  let μ:= sweep C
  let L:= {z: Poll.Body ι | ∃ i, t ≤ |z i|}
  have hr:(Gaussian.cloud C).real (outage t)= μ.real L:= by
    have hf:=Gaussian.preserving_cloud C
    unfold Measure.real; rw [← hf.map_eq,Measure.map_apply hf.measurable (outageSet ..)]; rfl
  rw [hr]
  let S i:={z:Poll.Body ι| ∀ j∈({i}:Finset ι), t≤|z j|}
  refine (measureReal_mono (s₂:=⋃ i∈ (Finset.univ:Finset ι), S i) (fun z hz=>?_) (measure_ne_top μ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  · obtain ⟨i,hi⟩:=hz
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_univ _,fun j hj=>?_⟩⟩; rw [Finset.mem_singleton.mp hj]; exact hi
  have he (i:ι) : μ.real (S i)≤2*Real.exp (-t+v/2):= by simpa only [neg_one_mul,one_pow,mul_one,Finset.card_singleton,pow_one,Nat.cast_one] using rectangle hp hz {i} t 1 zero_le_one
  refine (Finset.sum_le_sum (fun i _=>he i)).trans ?_; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; exact mul_le_mul_of_nonneg_right hN (by positivity)
end outage

section paid
variable (hc : ∀ᶠ x in 𝓝 p, ∀ s, veil X a q κ b D R.p d R.beta s (Z x) ≠0 → coin X i R a d R.beta ζ (Z x) s =1)
  (hv : 0 ≤ v) (hD : gStep R.beta*(Fintype.card G.ColorIndex:ℝ)*(v+δ) < (D.ε*R.p.threshold)/8)

include hc hs h ht hv hD
lemma seaward (s : Prices G I) (hl : ‖s‖ ≤ L) (hy : s∉outage v) :
    ∀ᶠ x in 𝓝 p, coin X i R a d R.beta ζ (Z x) s=1 ∧ veil X a q κ b D R.p d R.beta s (Z x)=1 := by
  let g:= gStep R.beta; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr h.positive)
  let U y:= reading9 X (Z y) a s q b d R.beta
  let Y:= D.ε*R.p.threshold; have he:0<Y:= mul_pos D.guards R.p.threshold_pos; have hr:=hs s hl
  have ht i : g* ‖tape (U p) i‖ < Y/8 := by
    have he j : |(U p) (i,j)| ≤ v+δ := by
      have hd : reading6 X (Z p) a s d R.beta=s:= by unfold reading6; rw [hr.at_z]; exact fast_zero X a ht h.positive s
      have hh : |s (i,j)-U p (i,j)| ≤ δ := hd ▸ (hr.shift (i,j)).bound -- edit
      have hx : |s (i,j)| < v := lt_of_not_ge fun ht=> hy ⟨(i,j),ht⟩
      calc
        _ ≤ |U p (i,j) - s (i,j)| + |s (i,j)| := by simpa only [sub_zero,Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub (U p (i,j)) (s (i,j)) 0
        _ ≤ _ := by rw [abs_sub_comm]; linarith only [hh,hx]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (color_cover (add_nonneg hv hr.delta) (tape (U p) i) he) hg.le) ?_; rwa [← mul_assoc]
  have hx i : ∀ᶠ y in 𝓝 p, g*‖tape (U y) i‖ ≤ Y /8:= by
    have hy: ContDiffAt ℝ n U p:=contDiffAt_pi.mpr fun i=> (hr.cols i).smooth
    exact (ContinuousAt.const_mul ((continuousAt_pi.mp ((gaugeCount (G:=G)).continuousAt.comp hy.continuousAt) i).norm) g).eventually (ge_mem_nhds (ht i))
  filter_upwards [hc,eventually_all.mpr hx] with y hh hz
  have hg : veil X a q κ b D R.p d R.beta s (Z y)=1:= guard_open κ hg he hz
  exact ⟨hh _ (ne_of_eq_of_ne hg one_ne_zero),hg⟩
end paid
end YM.PhysicalNext.Repeat.Prism
