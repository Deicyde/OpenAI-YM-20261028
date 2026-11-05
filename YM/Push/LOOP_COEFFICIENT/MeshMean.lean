import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Laurent.Art
import YM.Pressure.Seeds
import YM.Push.LOOP_COEFFICIENT.Frequency
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.F07.Read


/-!
# All-period error for an internal analytic torus summand

Cube uses right-closed one-dimensional intervals and ordinary
Euclidean 4-volume divided by `(2π)^4`. This applies to arbitrary families
of analytic periodic summands satisfying `Vane` and a strip bound, uniformly
without varying-p convergence hypotheses or any removal of the harmonic mode.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent Finset MeasureTheory Complex UnitAddTorus
open scoped Topology BigOperators ENNReal ContDiff

def zone : Set E4 := {x | ∀ i, x i ∈ Ioc (-Real.pi) Real.pi}

def radians (x : E4) : Momentum := fun i => (x i : ℂ)

def normalize4 : ℝ := ((2*Real.pi)^4)⁻¹
lemma normalize_pos : 0 < normalize4 := by unfold normalize4; positivity

def boxMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Momentum → E) : E :=
  normalize4 • ∫ k in zone, u (radians k)

lemma zone_measurable : MeasurableSet zone := by
  rw [zone,setOf_forall]; exact MeasurableSet.iInter fun i => (PiLp.continuous_apply 2 _ i).measurable measurableSet_Ioc

lemma mean_market {u : Momentum → ℂ} {η : ℝ} (h : Vane u η) : market u 0 0 = boxMean u := by
  let f := veils u 0
  rw [market, mFourierCoeff]; simp only [neg_zero,mFourier_zero, ContinuousMap.one_apply, one_smul]
  rw [UnitAddTorus.integral_preimage _ (fun _ : Axis => (-1/2:ℝ))]
  let T := {x : Axis → ℝ | ∀ i, x i ∈ Ioc (-1/2:ℝ) (-1/2+1)}
  have hT : MeasurableSet T := MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  change (∫ x in T,f (dress Axis x)) = _
  simp only [f, h.steps (p:=0) (show (0:Momentum)∈strip η from fun i => by simpa using h.side), zero_add]
  let P := 2*Real.pi
  let g := zone.indicator (u ∘ radians)
  have hmem (x : Axis → ℝ) : x∈T ↔ P • WithLp.toLp 2 x ∈ zone := by
    have hp := Real.pi_pos
    unfold T zone P
    simp only [Set.mem_setOf_eq,Set.mem_Ioc,PiLp.smul_apply,smul_eq_mul]
    apply forall_congr'; intro i; constructor
    · rintro ⟨h,h'⟩; constructor <;> nlinarith
    rintro ⟨h,h'⟩; constructor <;> nlinarith
  rw [← integral_indicator hT]
  change (∫ x, T.indicator _ x) = _
  calc
    _ = ∫ x : Axis → ℝ,g (P • WithLp.toLp 2 x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ T
      · dsimp only [g]; rw [Set.indicator_of_mem hx,Set.indicator_of_mem ((hmem x).mp hx)]
        apply congr_arg u
        ext1 i; simp [Laurent.walk,radians,P]
      dsimp only [g]; rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (mt (hmem x).mpr hx)]
    _ = ∫ x : E4,g (P • x) := (PiLp.volume_preserving_toLp Axis).integral_comp (MeasurableEquiv.toLp 2 (Axis → ℝ)).measurableEmbedding (fun x : E4 => g (P • x))
    _ = _ := by rw [Measure.integral_comp_smul_of_nonneg (volume : Measure E4) g P (hR:=by unfold P; positivity)]; simp [boxMean,normalize4,g,E4,P,Axis, integral_indicator zone_measurable,Function.comp_def]

lemma sum_mode (n : Side) (z : Cover) : ∑ i : Site n, mode (mon i) z = if wrap n z = 0 then (n.val:ℂ)^4 else 0 := by
  split
  next he => simp only [(mon_matches _).read _,he,cell_origin,sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow,mul_one]
  next he =>
    rw [← sum_cell he]; exact sum_congr rfl fun i _ => ((mon_matches i).read z).trans (cell_duality ..)

lemma size_wrap {n : Side} {z : Cover} (he : wrap n z=0) (h : z≠0) : n.val ≤ size z := by
  obtain ⟨i,hi⟩ : ∃ i, z i≠0 := by contrapose! h; exact funext h
  have hv : n.val ∣ (z i).natAbs := Int.natCast_dvd_natCast.mp <| Int.dvd_natAbs.mpr <|
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (congr_fun he i)
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hi) hv).trans (Finset.single_le_sum (f:=fun i => (z i).natAbs) (fun i _ => Nat.zero_le _) (mem_univ i))

variable {σ K : ℝ}

def meshMean (n : Side) (u : Momentum → ℂ) := ((n.val:ℂ)^4)⁻¹ * ∑ i : Site n,u (mon i)

lemma read_error (n : Side) {c : Cover → ℂ} (hc : Width σ K c) (hs : 0 < σ) :
    ‖meshMean n (Laurent.read c) - c 0‖ ≤ K * Real.exp (-σ*n.val) := by
  let a (z : Cover) := if wrap n z=0 then c z else 0
  let b (z : Cover) := if z=0 then c z else 0
  let f (z : Cover) := Real.exp (σ*size z)*‖c z‖ * Real.exp (-σ*n.val)
  have hf (z) : ‖a z - b z‖ ≤ f z := by
    by_cases hz : z=0
    · simp [a,b,hz,f]; positivity
    simp only [a,b,if_neg hz, sub_zero]
    split
    · unfold f; rw [mul_right_comm, ← Real.exp_add]; exact le_mul_of_one_le_left (norm_nonneg _) <| Real.one_le_exp <| by
        have he : n.val ≤ size z := size_wrap ‹_› hz
        have hv : (n.val:ℝ) ≤ size z := by exact_mod_cast he
        nlinarith
    unfold f; rw [norm_zero]; positivity
  have hA : Summable a := ((hc.summable hs.le).indicator {z | wrap n z=0}).congr (fun i => by by_cases h : wrap n i=0 <;> simp [indicator, *, a])
  have hB : Summable b := summable_of_ne_finset_zero (s:={0}) (fun z h => if_neg (by simpa using h))
  have hF : Summable f := hc.2.1.mul_right _
  have hM : meshMean n (Laurent.read c) = ∑' z,a z := by
    have hv (i : Site n) (_ : i ∈ Finset.univ) : Summable fun z => mode (mon i) z • c z :=
      (hc.series (mon i) (fun j => (Work.F07.realStrip σ hs (real_frequency i) j).le)).2.1.of_norm
    unfold meshMean Laurent.read; rw [← Summable.tsum_finsetSum hv,← tsum_mul_left]
    refine tsum_congr (fun z => ?_)
    rw [show (∑ i : Site n,mode (mon i) z • c z) = _ from (Finset.sum_mul ..).symm, sum_mode]
    simp only [a]; split <;> simp [side_ne n]
  rw [hM, show c 0 = ∑' z,b z from Eq.symm ((tsum_eq_single 0 (fun z hz => if_neg hz)).trans (if_pos rfl)), ← hA.tsum_sub hB]
  exact (norm_tsum_le_tsum_norm (hF.of_nonneg_of_le (fun z => norm_nonneg _) hf)).trans <| (hF.of_nonneg_of_le (fun z => norm_nonneg _) hf |>.tsum_le_tsum hf hF).trans
    (show (∑' i, f i) ≤ _ by unfold f; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hc.2.2 (Real.exp_pos _).le)

lemma mesh_error (n : Side) {u : Momentum → ℂ} {η b : ℝ} (h : Vane u η) (hk : ∀ x∈strip η, ‖u x‖ ≤ K) (hσ : 0 < σ) (hb : 0 < b) (he : σ + b < η) :
    ‖meshMean n u - boxMean u‖ ≤ (K*(2*((1+b)/b))^4) * Real.exp (-σ*n.val) := by
  have hh : meshMean n u = meshMean n (Laurent.read (market u 0)) := by
    unfold meshMean; congr 1; exact sum_congr rfl fun i _ => (h.paints hk _ (Work.F07.realStrip η h.side (real_frequency _))).symm
  rw [hh, ← mean_market h]; simpa only [Axis,Fintype.card_fin] using read_error n (h.issues hk σ b hσ.le hb he) hσ
end YM.Push.Loops
