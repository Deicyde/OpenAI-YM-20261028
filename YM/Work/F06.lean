import YM.Work.F06.Harmonic
import YM.Work.F06.Stencil




/-!
# F06 – repair of the all-phase positivity margin

The single (momentum-independent) price pays for adding the Gram
of the outgoing coboundary to the three-form row. Use counting energy,
allowing a nonorthogonal splitting in the region away from zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F06
open Lattice Laurent Bloch Exterior Craft Matrix
open scoped BigOperators Topology

lemma near_harmonic (Q : C3) {v η C δ : ℝ} (hr : Reaches Q v)
    (hs : Q.strip η C) (hη : 0 < η) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hcost : countCeil (TypeFace 3)^2 * (δ / η * C) ≤ v/2)
    (p : Momentum) (hp : star p = p) (he : ∀ i, ‖q p i‖ ≤ δ) (x : TypeFace 3 → ℂ) :
    v/2 * sqLength x ≤ pairingRe (Q.read p) x x := by
  have hb i j : ‖(Q.read p - Q.read 0) i j‖ ≤ δ / η * C :=
    row_entry_depart hs hη p hp δ hδ he i j
  have hl := (pairingRe_diag _ (by positivity) hb x).trans
    (mul_le_mul_of_nonneg_right hcost (sqLength_nonneg x))
  rw [pairingRe_sub] at hl
  linarith only [harmonic_lower Q hr hs hη x, (abs_le.mp hl).1]

def extraFee (v C δ : ℝ) : ℝ :=
  let N := countCeil (TypeFace 3)
  mixPrice v (N^2 * C) * (N * (δ⁻¹)^2)

lemma away_lower (Q : C3) {v η C δ : ℝ} (hr : Reaches Q v)
    (hs : Q.strip η C) (hv : 0 < v) (hη : 0 < η) (hC : 0 ≤ C) (hδ : 0 < δ)
    (p : Momentum) (hp : star p = p) (k : Axis) (hk : δ < ‖q p k‖) (x : TypeFace 3 → ℂ) :
    v/4 * sqLength x ≤ pairingRe (Q.read p) x x + extraFee v C δ * sqLength (symbol 3 p *ᵥ x) := by
  have hj : q p k ≠ 0 := norm_pos_iff.mp (hδ.trans hk)
  let b := (q p k)⁻¹ • ((left ℂ 2 k).transpose *ᵥ x)
  let y := symbol 2 p *ᵥ b
  let u := symbol 3 p *ᵥ x
  let z := (q p k)⁻¹ • ((left ℂ 3 k).transpose *ᵥ u)
  let N := countCeil (TypeFace 3)
  have hsplit : x = y + z := cartan_split x (q p) k hj
  have hy : v * sqLength y ≤ pairingRe (Q.read p) y y := (hr p hp).2 b
  have hN : 0 < N := countCeil_pos _
  have hz : sqLength z ≤ (N * (δ⁻¹)^2) * sqLength u := by
    have hi : ‖(q p k)⁻¹‖ ≤ δ⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ (hδ.trans hk) hδ).mpr hk.le
    calc
      sqLength z = ‖(q p k)⁻¹‖^2 * sqLength ((left ℂ 3 k).transpose *ᵥ u) :=
        sqLength_smul ..
      _ ≤ (δ⁻¹)^2 * (N * sqLength u) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hi _) (contraction_price u k)
          (sqLength_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hh := pairingRe_complete (Q.read p) hC hv (row_entry_le hs hη.le p hp) y z hy hz
  rw [← hsplit] at hh
  exact hh

theorem answer : YM.Bid.F06 := by
  intro A v η hv hη
  let C := |A|+1
  let N := countCeil (TypeFace 3)
  have hC : 0 < C := by unfold C; positivity
  have hN : 0 < N := countCeil_pos _
  let δ := η * v / (2 * N^2 * C)
  have hδ : 0 < δ := by unfold δ; positivity
  let r := extraFee v C δ
  have hc : N ^ 2 * (δ / η * C) ≤ v/2 := Eq.le (by unfold δ; field_simp)
  have hprice : 0 ≤ r := by
    change 0 ≤ (N^2*C + 2*(N^2*C)^2/v + v/2) * (N*(δ⁻¹)^2)
    positivity
  -- Finite correction independent of Q
  let R : C3 := gramRow r Exterior.support (cobound 3)
  obtain ⟨K,hK,hks⟩ := strip_of_fin (diffBox Exterior.support) R
    (gramRow_extinct r Exterior.support (cobound 3)) η
  let B := N ^ 2 * (C + K)
  have hb : C + K ≤ B := by
    have he : 1 ≤ N := by unfold N countCeil; simp
    calc
      C + K = 1 ^ 2 * (C + K) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) he _) (by positivity)
  refine ⟨v/4, B, η, by positivity, hη, ?_⟩
  intro Q hreach hq
  have hQc : Q.strip η C := fun i j => (hq i j).mono le_rfl
    (by unfold C; linarith [le_abs_self A])
  let P : C3 := Q + R
  have hPs : P.strip η (C+K) := row_strip_add hQc hks
  have hPr (p : Momentum) (hp : star p = p) : P.read p = Q.read p +
      (r:ℂ) • ((symbol 3 p).conjTranspose * symbol 3 p) := by
    rw [show P.read p = Q.read p + R.read p from
      row_read_add hQc hks p (within_real hη.le hp)]
    unfold R
    rw [gramRow_read r Exterior.support (cobound 3) (certified 3) p hp,
      Exterior.reading]
  refine ⟨P, ?_, fun i j => (hPs i j).mono le_rfl hb, ?_⟩
  · intro p hp
    constructor
    · rw [hPr p hp]
      refine (hreach p hp).1.add ?_
      exact (Matrix.isHermitian_conjTranspose_mul_self _).smul
        (show IsSelfAdjoint (r:ℂ) by simp [IsSelfAdjoint])
    intro x
    change v/4 * sqLength x ≤ pairingRe (P.read p) x x ∧ pairingRe (P.read p) x x ≤ B * sqLength x
    refine ⟨?_, (abs_le.mp (pairingRe_diag _ (by positivity) (row_entry_le hPs hη.le p hp) x)).2⟩
    rw [hPr p hp, pairingRe_add, pairingRe_scale, pairingRe_gram]
    by_cases he : ∀ i, ‖q p i‖ ≤ δ
    · have hl := near_harmonic Q hreach hQc hη hC.le hδ.le hc p hp he x
      have hz : 0 ≤ r * sqLength (symbol 3 p *ᵥ x) := mul_nonneg hprice (sqLength_nonneg _)
      have hy : 0 ≤ v * sqLength x := mul_nonneg hv.le (sqLength_nonneg _)
      linarith only [hl, hz, hy]
    push Not at he
    obtain ⟨k,hk⟩ := he
    exact away_lower Q hreach hQc hv hη hC.le hδ p hp k hk x
  have H (p : Momentum) (hp : star p = p) : P.read p * (cobound 2).read p =
      Q.read p * (cobound 2).read p := by
    rw [hPr _ hp, Matrix.add_mul, Exterior.reading, Matrix.smul_mul, Matrix.mul_assoc,
      show symbol 3 p * symbol 2 p = 0 from Exterior.d_d 2 _, Matrix.mul_zero, smul_zero,
      add_zero]
  intro n
  have hh := acts_coincide P Q (cobound 2) (Row.rights _ _ hPs hη.le) (Row.rights _ _ hQc hη.le)
    (cobound_safe 2) H n
  change P.acts n * d 2 n = Q.acts n * d 2 n at hh
  rw [Matrix.mul_assoc, hh, Matrix.mul_assoc]

end YM.Work.F06
