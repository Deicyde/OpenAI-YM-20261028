import Mathlib.Analysis.Complex.Schwarz
import YM.Push.LOOP_COEFFICIENT.Line
import YM.Push.LOOP_COEFFICIENT.Tubes
import YM.Work.B04
import YM.Work.F07.Read



/-! # Bounded periodic symbols on linear width budgets -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice Laurent Bloch Complex Metric RG Exterior
open scoped BigOperators Topology ContDiff Matrix.Norms.L2Operator
variable {f : Momentum → ℂ} {η C D : ℝ} {p : Momentum}

def Center (η : ℝ) : Set Momentum := {p | p∈Tube η ∧ ∀ i, |(p i).re| ≤ Real.pi}
lemma center_neg (hp : p ∈ Center η) : -p ∈ Center η := ⟨tube_neg hp.1,fun i => by simpa using hp.2 i⟩
lemma norm_in_center (hp : p ∈ Center η) : ‖p‖ ≤ Real.pi + η := by
  have hη := (abs_nonneg _).trans_lt (hp.1 0)
  exact (pi_norm_le_iff_of_nonneg (by positivity : 0≤Real.pi+η)).mpr fun i => (norm_le_abs_re_add_abs_im _).trans (add_le_add (hp.2 i) (hp.1 i).le)
lemma center_adjust (hp : p∈Tube η) : ∃ q ∈ Center η, ∃ z, p = q + Laurent.reciprocal z := by
  let z (i : Axis) := ⌊(p i).re / (2*Real.pi) + 1/2⌋
  let q := p+reciprocal (-z)
  refine ⟨q, ⟨tube_reciprocal hp _,fun i => ?_⟩, z,by simp only [q,reciprocal_neg]; abel⟩
  have he := Int.floor_le ((p i).re / (2*Real.pi) + 1/2)
  have ht := Int.lt_floor_add_one ((p i).re / (2*Real.pi) + 1/2)
  change (z i : ℝ) ≤ _ at he; change _ < (z i : ℝ)+1 at ht
  have h := Real.pi_pos
  simp only [q,reciprocal_neg, Pi.add_apply,Pi.neg_apply, Complex.add_re,Complex.neg_re,reciprocal, ← ofReal_intCast,← ofReal_ofNat,← ofReal_mul,ofReal_re,abs_le]
  constructor
  all_goals field_simp at ht he; linarith

lemma ball_tube : ball (0:Momentum) η ⊆ Tube η := fun p hp i => (abs_im_le_norm _).trans_lt ((norm_le_pi_norm p i).trans_lt (by simpa using hp))



lemma schwarz_two (hη : 0<η) (hf : ∀ p∈Tube η, ContDiffAt ℂ ω f p ∧ ‖f p‖ ≤ C) (hz : ∀ p, Below f p 2) (hp : p∈Tube η) : ‖f p‖ ≤ C*(‖p‖/η)^2 := by
  have h := (hf 0 (Work.F07.realStrip _ hη (star_zero ..))).1
  have h0 := (line_zero (p:=p) (f:=f)).symm.trans (hz p 0 (by decide))
  have hd := (h.differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℂ f 0 = 0 from ContinuousLinearMap.ext fun p => (line_one h p).symm.trans (hz p 1 (by decide))] at hd
  by_cases he : p∈ball 0 η
  · simpa [h0] using! dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n:=1)
      (fun _ hx => ((hf _ (ball_tube hx)).1.differentiableAt (by simp)).differentiableWithinAt)
      (fun x hx => show f x ∈ closedBall (f 0) C by simpa [h0] using! (hf _ (ball_tube hx)).2)
      (by simp only [pow_one,sub_zero]; apply Asymptotics.isLittleO_norm_right.mpr; simpa using hd.isLittleO) he
  exact (hf _ hp).2.trans (le_mul_of_one_le_right ((norm_nonneg _).trans (hf _ hp).2) (one_le_pow₀ (by rw [le_div_iff₀ hη,one_mul]; simpa using he)))

variable {a b d : Type}
structure Entries (X : Matrix a b ℂ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  entry i j : ‖X i j‖ ≤ C

namespace Entries
variable {X Y : Matrix a b ℂ} (hx : Entries X C) (hy : Entries Y D)
include hx
lemma mono {D : ℝ} (he : C≤D) : Entries X D := ⟨hx.nonneg.trans he,fun i j => (hx.entry i j).trans he⟩
include hy in lemma sub : Entries (X-Y) (C+D) := ⟨add_nonneg hx.nonneg hy.nonneg,fun i j => (norm_sub_le ..).trans (add_le_add (hx.entry i j) (hy.entry i j))⟩
include hy in lemma add : Entries (X+Y) (C+D) := ⟨add_nonneg hx.nonneg hy.nonneg,fun i j => (norm_add_le ..).trans (add_le_add (hx.entry i j) (hy.entry i j))⟩
lemma smul (c : ℂ) : Entries (c • X) (‖c‖*C) := ⟨mul_nonneg (norm_nonneg _) hx.nonneg,fun i j => by rw [Matrix.smul_apply,norm_smul]; gcongr; exact hx.entry i j⟩
lemma transpose : Entries X.transpose C := ⟨hx.nonneg, fun i j => hx.entry j i⟩
lemma mul [Fintype b] {Y : Matrix b d ℂ} (he : Entries Y D) : Entries (X*Y) (Fintype.card b * (C*D)) :=
  ⟨mul_nonneg (by positivity) (mul_nonneg hx.nonneg he.nonneg),fun i j => by rw [Matrix.mul_apply]; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => C*D) fun k _ => by rw [norm_mul]; exact mul_le_mul (hx.entry i k) (he.entry k j) (norm_nonneg _) hx.nonneg).trans_eq (by simp))⟩
omit hx in lemma sum {ι : Type*} (s : Finset ι) {X : ι → Matrix a b ℂ} {C : ι → ℝ} (h : ∀ i ∈ s, Entries (X i) (C i)) : Entries (∑ i∈s,X i) (∑ i∈s,C i) :=
  ⟨Finset.sum_nonneg (fun i hi => (h i hi).nonneg),fun i j => by rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun k hk => (h k hk).entry i j)⟩
end Entries

variable {G : Gauge} {σ Λ : ℝ}







end YM.Push.Loops
