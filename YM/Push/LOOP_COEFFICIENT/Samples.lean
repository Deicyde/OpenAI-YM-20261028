import YM.Push.LOOP_COEFFICIENT.Frequency
import YM.Push.LOOP_COEFFICIENT.JetMatrix
import YM.Push.LOOP_COEFFICIENT.Routed

/-!
# Two-wave comparison port for actual matrices (per-cell normalization)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators ContDiff
variable {n : Side} {E F a b : Type} [Fintype E] [Fintype F] [Fintype a] [Fintype b]
  [DecidableEq E] [DecidableEq F] [DecidableEq a] [DecidableEq b]
variable {M : Grid n E a} {N : Grid n F b} {X Y : Matrix E F ℂ} {U V : Momentum → Matrix a b ℂ}

def sample (M : Grid n E a) (N : Grid n F b) (X : Matrix E F ℂ) (k i : Site n) :=
    ((n.val:ℂ)^4)⁻¹ • ((plane M k).transpose * X * plane N i)
structure Compares (M : Grid n E a) (N : Grid n F b) (X : Matrix E F ℂ) (V : Momentum → Matrix a b ℂ) (tol : ℝ) : Prop where
  off (k i : Site n) : k+i ≠ 0 → sample M N X k i = 0
  price {p i} : Matches p i → ∀ j k, ‖sample M N X (-i) i j k - V p j k‖ ≤ tol

abbrev Coeff (f : (E → ℝ) → ℝ) := cmat (bilinearAt f 0)

lemma sample_actual (f : (E → ℝ) → ℝ) (k i : Site n) (x y : CSpace a) :
    x ⬝ᵥ (sample M M (Coeff f) k i *ᵥ y) =
    ((n.val:ℂ)^4)⁻¹ * (actualScalar f).quad (plane M k *ᵥ x) (plane M i *ᵥ y) := by
  rw [actualScalar_quad,sample,smul_mulVec,dotProduct_smul, ← mulVec_mulVec,← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]; rfl

omit [DecidableEq E] [DecidableEq F] [Fintype a] [Fintype b] in
lemma sample_add (k i : Site n) : sample M N (X+Y) k i = sample M N X k i + sample M N Y k i := by
  unfold sample; rw [Matrix.mul_add,Matrix.add_mul,smul_add]
omit [DecidableEq E] [DecidableEq F] [Fintype a] [Fintype b] in
lemma sample_smul (c : ℂ) (k i : Site n) : sample M N (c • X) k i = c • sample M N X k i := by
  unfold sample; rw [Matrix.mul_smul,Matrix.smul_mul,smul_comm]

namespace Compares
variable {tol tol' : ℝ}

omit [DecidableEq E] [DecidableEq F] [Fintype b] in
lemma of_routed (h : ∀ i p, Matches p i → Routed M N i i X (V p)) : Compares M N X V 0 := by
  constructor
  · intro k i hk
    rw [sample,(h i (mon i) (mon_matches i)).paired, if_neg (mt add_eq_zero_iff_neg_eq.mpr hk),smul_zero]
  · intro p i hp j k; rw [sample,(h i p hp).paired, if_pos (neg_neg i),smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (side_ne _)), one_smul,sub_self,norm_zero]

omit [DecidableEq E] [DecidableEq F] [Fintype a] [Fintype b] in
lemma mono (h : Compares M N X U tol) (ht : tol ≤ tol') : Compares M N X U tol' := ⟨h.off,fun hp j k => (h.price hp j k).trans ht⟩

omit [DecidableEq E] [DecidableEq F] [Fintype a] [Fintype b] in
lemma add (h : Compares M N X U tol) (h' : Compares M N Y V tol') : Compares M N (X+Y) (U+V) (tol+tol') := by
  constructor
  · intro k i he; rw [sample_add, h.off k i he,h'.off k i he,zero_add]
  · intro p i hp j k; rw [sample_add]; simp only [Matrix.add_apply, Pi.add_apply,add_sub_add_comm]; exact (norm_add_le ..).trans (add_le_add (h.price hp j k) (h'.price hp j k))

omit [DecidableEq E] [DecidableEq F] [Fintype a] [Fintype b] in
lemma smul (c : ℂ) (h : Compares M N X U tol) : Compares M N (c • X) (c • U) (‖c‖*tol) := by
  constructor
  · intro k i he; rw [sample_smul,h.off k i he,smul_zero]
  · intro p i hp j k; rw [sample_smul]; simp only [Matrix.smul_apply,Pi.smul_apply,← smul_sub,norm_smul]; exact mul_le_mul_of_nonneg_left (h.price hp j k) (norm_nonneg _)

omit [DecidableEq E] [DecidableEq F] [Fintype a] [Fintype b] in
lemma exact_sample (h : Compares M N X V 0) {p i} (hp : Matches p i) : sample M N X (-i) i = V p := by
  ext j k; exact sub_eq_zero.mp (norm_le_zero_iff.mp (h.price hp j k))
end Compares
end YM.Push.Loops
