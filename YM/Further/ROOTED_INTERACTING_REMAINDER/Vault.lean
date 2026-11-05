import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Signal
import YM.Push.CORRECTED_COLUMNS.Tree
import YM.Push.STATIONARY_UNIFORM.FrameMin

/-!
# Flat-point floor and Gibbs costs without Counter

Even when scalar jump / Gaussian alignment and the post-hole integrand are
not reconstructed, pay the normalization against the actual intact law.
Crucial not to use the band comparison of Z(V) to partition for the
flat-point floor (16 β per site in that direction; too much!). Reuse
hold at `RG.calm` **on the arbitrary block tree**, true phases and tags,
quantitative prediction estimates even across any switches and any period,
and NtF (3*sites f + sites c), exact residual count.

In fact on every V we give a denominator paying sum of **squared** chords
on *any* chosen coarse gauge, so one can also use when β * mean(chord)²
is small at probes away from all-good holonomy; no claim this floor costs
little at locally flat V, though in some applications `passage` just to
a test region may be used together with it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Filter Function Lattice RG RG.Patch Wilson Finset Precision MeasureTheory Tree
open Pressure Pressure.Stores Pressure.Testing 
open    RG.Shoot
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "Δ" => Module.finrank ℝ G.Color

namespace Vault
open YM.Push.Uniform

def fare (P : Patch) := ((2*P.radius:ℕ):ℝ)
lemma fare_positive (P : Patch) : 0<fare P := by unfold fare radius; positivity
private lemma minutes (P : Patch) (i : Site f) (U : Config G f) (r : ℝ) (hr : 0≤r) (hc : U ∈ calm G f r) :
    ClosePaths P (expandAt i U) (fare P*r) := by
  intro x y l
  rw [travel_at]
  have ht := routeLe P x y l
  apply (pathBound hc ..).trans
  unfold fare; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (by linarith : (0:ℝ) ≤ r/4)).trans_eq (by push_cast; ring)

def frameFare (P : Patch) := (Push.Uniform.alignCost P+2)*fare P


lemma frame_good (i : Site f) (U : Config G f) (P : Patch) (k : KernelChoices) (z : P.FrameTag) (x : P.Points)
    (r : ℝ) (hr : 0≤r) (hc : U ∈ calm G f r) :
    G.chord (P.frame k (expandAt i U) z x) ≤ frameFare P*r := by
  have he := minutes P i U r hr hc
  have hf : 0 ≤ fare P * r := mul_nonneg (fare_positive _).le hr
  unfold Patch.frame; split
  · have h := cluster_root P (P.min_exists (expandAt i U)).choose_spec he x
    apply h.trans; unfold frameFare; linarith only [hf]
  apply (G.chord_triangle _ _).trans; rw [G.chord_inv]
  apply le_trans (add_le_add (he z.1 P.center z.2) (he z.1 x z.2))
  unfold frameFare; linarith only [mul_nonneg (align_pos P).le hf]

def farePrice (P : Patch) (K : KernelChoices) : ℝ :=
    2*max 1 K.predictor_cut⁻¹ * ((frameFare P+P.L.val)+frameFare P)


lemma prediction_good (S : StepData c f) (U : Config G f) (i : S.Choices) (r : ℝ) (hr : 0≤r) (hc : U ∈ calm G f r) (e : Bond c) :
    G.chord (S.prediction U i e) ≤ farePrice S.patch S.kernel * r := by
  let P := S.patch; let D := frameFare P; let L : ℝ := P.L.val; let K := S.kernel
  have he (x : P.Points) (j : Site c) : G.chord (S.frames U i.1 j x) ≤ D*r := frame_good _ _ P K _ _ _ hr hc
  let Y := S.connector U i.1 e
  let M := 2*max 1 K.predictor_cut⁻¹
  have h0 : G.chord (S.prediction U i e) ≤ M * (∑ x, P.weight x * G.chord (Y x)) := by
    change G.chord (P.predict K Y (i.2 e)) ≤ 2*max 1 K.predictor_cut⁻¹ * _
    simpa only [inv_one,one_mul,mul_one] using price_query P K Y (i.2 e) 1 1
  apply h0.trans
  have hx (x : P.Points) : G.chord (Y x) ≤ ((D*r + L*r)+D*r) := by
    unfold Y StepData.connector
    apply (G.chord_triangle _ _).trans; rw [G.chord_inv]
    apply add_le_add ((G.chord_triangle _ _).trans (add_le_add (he x _) ?_)) (he x _)
    rw [travel_at]; apply (pathBound hc ..).trans
    rw [List.length_replicate]; unfold L; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc
    _ ≤ M * (∑ x, P.weight x * ((D*r+L*r)+D*r)) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold M; positivity)
      apply sum_le_sum; exact fun x _=>mul_le_mul_of_nonneg_left (hx _) (weight_nonneg ..)
    _ = _ := by rw [←sum_mul,weight_sum,one_mul]; change _ = farePrice P K * r; unfold D farePrice L M; ring



 

 







-- forest tree floor reuse. Requires root-preserving, not full GI.
open YM.Tree ENNReal
open scoped ENNReal









end Vault
end YM.Further.RootedInteractingRemainder
