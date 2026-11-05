import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Slopes
import YM.Next.BOUNDARY.Coordinates
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# Actual unmasked path in log inputs

Frobenius norm, no circumference gain. Price also on finite-radius
real log vectors (later useful for exchanging derivative sums with
actual infinite rows); uniform costs independent of periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix  Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n l : Side} {ι : Type*} [DecidableEq ι]

namespace Logfee

lemma guaranties (G : Gauge) (m : ℕ) (R : ℝ) (hr : 0 ≤ R) : ∃ C : ℝ, 1≤C ∧
    ∀ (S : ℕ),S ≤ m → S ≠ 0 → ∀ y : G.Color, ‖y‖ ≤ R →
    let f := fun z => G.mat (G.lieExp z)
    ‖iteratedFDeriv ℝ S f y‖ ≤ C^S := by
  let f := fun z => G.mat (G.lieExp z)
  let B := Metric.closedBall (0:G.Color) R
  have hs : ContDiff ℝ ω f := G.exp_jet
  have hx : ∀ i : ℕ,∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ B, ‖iteratedFDeriv ℝ i f y‖ ≤ C := by
    intro i; have hh := (show Continuous fun y => ‖iteratedFDeriv ℝ i f y‖ from
      (hs.continuous_iteratedFDeriv le_top).norm)
    obtain ⟨a,_,he⟩ := (isCompact_closedBall (0:G.Color) R).exists_isMaxOn (Metric.nonempty_closedBall.mpr hr) hh.continuousOn
    refine ⟨max 1 ‖iteratedFDeriv ℝ i f a‖, le_max_left ..,fun v hv => ?_⟩; exact (he hv).trans (le_max_right ..)
  choose C hC H using hx
  let D := ∑ i∈Finset.range (m+1), C i
  have ht (s) (hs : s≤m) : C s ≤ D := Finset.single_le_sum (fun i _ => zero_le_one.trans (hC i)) (Finset.mem_range.mpr (by omega))
  have hp := (hC 0).trans (ht 0 (Nat.zero_le _))
  refine ⟨D,hp,fun i hi hk y hy => ?_⟩
  exact ((H i y (by simpa [B] using hy)).trans (ht i hi)).trans (by
    change D ≤ D^i; conv_lhs => rw [← pow_one D]
    exact pow_le_pow_right₀ hp (by omega))
structure UValue (G : Gauge) (m : ℕ) where
  C : ℝ
  used : 1≤C
  he : ∀ S ≤ m,S ≠ 0 → ∀ y : G.Color, ‖y‖ ≤ 1 →
    ‖iteratedFDeriv ℝ S (fun z => G.mat (G.lieExp z)) y‖ ≤ C^S

def unitPrice (G : Gauge) (m : ℕ) : UValue G m :=
    let C := guaranties G m 1 zero_le_one
    ⟨C.choose,C.choose_spec.1,C.choose_spec.2⟩

lemma confirms (y : G.Mat) (v : G.El) : ‖G.mat v * y‖=‖y‖ := Gauge.mul_frob_eq _ _ (G.mat_star_mul _)
lemma unit_pay (v : G.El) : ‖G.mat v‖=‖(1:G.Mat)‖ := by rw [← confirms (1:G.Mat) v,mul_one]

variable (v : ι→Dir G n) (z : Site n) (a : Dir G n) (m : ℕ)

def width (a : Dir G n) (e : Step) (z : Site n) := ‖a ((e.used z).1,coord (e.used z).2)‖

def piece (e : Step) (z : Site n) (a : Dir G n) := G.mat (e.read (represent a) z)
lemma piece_cont (e : Step) : ContDiff ℝ ω (piece (G:=G) e z) := by
  unfold piece Step.read; split
  · simp_rw [G.mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (represent_smooth ..)
  exact represent_smooth ..

omit [DecidableEq ι] in
lemma scale (S : Finset ι) (h : S.card ≤ m) (he : S.Nonempty) (ha : ‖a‖ ≤ 1) (e : Step) :
    ‖bill S v (piece e z) a‖ ≤ (unitPrice G m).C^S.card * ∏ i∈S,width (v i) e z := by
  let y := e.used z
  let p : Body 1 n := (y.1,coord y.2)
  let f (a : G.Color) := G.mat (G.lieExp a)
  let F (a : Dir G n) := G.mat (represent a y)
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body 1 n => G.Color) p
  have hf : F=f ∘ L := funext fun i => congr_arg G.mat (represent_link ..)
  have ht : ‖L a‖ ≤ 1 := (norm_le_pi_norm a p).trans ha
  have hh := bill_bound S (L ∘ v) f (L a);
  have hb := hh.trans (mul_le_mul_of_nonneg_right ((unitPrice G m).he S.card h (Finset.card_ne_zero.mpr he) (L a) ht)
    (Finset.prod_nonneg fun i _ => norm_nonneg _))
  have hp : ‖bill S v F a‖ ≤ (unitPrice G m).C^S.card * ∏ i∈S,width (v i) e z := by
    rw [hf,readdress S v L a G.exp_jet]; exact hb
  unfold piece Step.read; split
  · simp only [G.mat_inv]; let V : G.Mat ≃L[ℝ] G.Mat := starL ℝ
    change ‖bill S v (V.toContinuousLinearMap ∘ F) a‖ ≤ _
    have he := left_price S v V.toContinuousLinearMap (show ContDiffAt ℝ ω F a from (represent_smooth (G:=G) y).contDiffAt)
    refine (congr_arg (fun a : G.Mat => ‖a‖) he).trans_le ?_
    change ‖star (bill S v F a)‖ ≤ _; rw [norm_star]; exact hp
  exact hp

def weight (a : Dir G n) (w : Walk) (z : Site n) : ℝ :=
    match w with | [] => 0 | e::w => width a e z+weight a w (z+e.vec)

def transport (w : Walk) (z : Site n) (a : Dir G n) := G.mat (travel (represent a) z w)

lemma weight_nonneg (w : Walk) : 0 ≤ weight a w z := by
  induction w generalizing z with
  | nil => exact le_rfl
  | cons e l ih => exact add_nonneg (norm_nonneg _) (ih _)
lemma train_rate (w : Walk) : ContDiff ℝ ω (transport (G:=G) w z) := by
  induction w generalizing z with
  | nil => exact contDiff_const
  | cons e w ih => rw [show transport (G:=G) (e::w) z = fun a => piece e z a * transport w (z+e.vec) a from funext fun a => G.mat_mul ..]; exact (piece_cont (G:=G) z e).mul (ih _)

def ample (G : Gauge) := max 1 ‖(1:G.Mat)‖
lemma ample_back (G : Gauge) : 1 ≤ ample G := le_max_left ..
lemma ample_pos (G : Gauge) : 0 < ample G := lt_of_lt_of_le zero_lt_one (ample_back G)

theorem ticket (w : Walk) (S : Finset ι) (h : S.card ≤ m) (ha : ‖a‖ ≤ 1) :
    ‖bill S v (transport w z) a‖ ≤ ample G * ((unitPrice G m).C^S.card * ∏ i∈S, weight (v i) w z) := by
  let φ := ContinuousLinearMap.mul ℝ G.Mat
  have hu : 0 ≤ (unitPrice G m).C := zero_le_one.trans (unitPrice G m).used
  induction w generalizing z S with
  | nil =>
    rcases Finset.eq_empty_or_nonempty S with H|H
    · rw [H,blank,transport,unit_pay (G:=G) (travel ..)]
      simp [ample]
    rw [show bill S v (transport [] z) a=0 from mute H v a _,norm_zero]
    exact mul_nonneg (ample_pos ..).le (mul_nonneg (pow_nonneg hu _) (Finset.prod_nonneg fun i _ => weight_nonneg ..))
  | cons e w ih =>
    let P (i : Finset ι) := (unitPrice G m).C^i.card
    let r i := width (v i) e z
    let q i := weight (v i) w (z+e.vec)
    let F := piece (G:=G) e z
    let L := transport (G:=G) w (z+e.vec)
    rw [show transport (e::w) z = (fun u : Dir G n => φ (F u) (L u)) from funext fun i => G.mat_mul ..,
      account φ S v F L a (piece_cont z e).contDiffAt (train_rate _ w).contDiffAt]
    change _ ≤ ample G * (P S*∏ i∈S,(r i+q i))
    rw [Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
    apply (norm_sum_le ..).trans (Finset.sum_le_sum _)
    intro i hi
    have hi := Finset.mem_powerset.mp hi
    let x := bill i v F a
    let y := bill (S\i) v L a
    have hh := ih (z+e.vec) (S\i) ((Finset.card_le_card Finset.sdiff_subset).trans h)
    have hp : P S=P i*P (S\i) := by
      dsimp only [P]; rw [← pow_add,Nat.add_comm, Finset.card_sdiff_add_card_eq_card hi]
    rcases Finset.eq_empty_or_nonempty i with hx|hx
    · subst i; simp only [blank,Finset.sdiff_empty,Finset.prod_empty,one_mul] at *
      rw [show φ (F a) _=G.mat _ * _ from rfl, confirms]; exact hh
    change ‖x*y‖ ≤ _
    have hb : ‖x‖ ≤ P i * ∏ j∈i,r j := scale v z a m i ((Finset.card_le_card hi).trans h) hx ha e
    exact ((norm_mul_le ..).trans (mul_le_mul hb hh (norm_nonneg _) ((norm_nonneg _).trans hb))).trans_eq (by
      rw [hp]; unfold P r q; ring)
end Logfee
end YM.AnalyticNext.QuarticMatch.Estimate
