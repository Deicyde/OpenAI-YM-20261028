import YM.MergeProof.East.Suds
import YM.Push.FINITE_DETECTION.TwoPoint

/-! A generic pair (thus volume comparisons hold there) tending to
reflection, at each weak k. Tilt avoids point-limit questions along true
coordinate ties. Hence nonsymmetric detector; do NOT use reflection positivity
(not opposite time reflected partner) or units of an arbitrary ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak
open Function Set Filter MeasureTheory Lattice Wilson RG Extraction Next.Rank.Station
open Push.FiniteDetection Push.FiniteDetection.Free
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {b : ℝ}

-- if a coordinate ties, nudge. Works for any target pair.

def stripe (s : ℝ) (x : Points 2) : Fin 2 → Cover :=
  let f := Extraction.address s x
  ![f 0, fun j => if f 1 j = f 0 j then f 1 j + 1 else f 1 j]

lemma stripeGeneric {s : ℝ} (h : 0 < s) (x : Points 2) : tag s (stripe s x) ∈ generic 2 := by
  have he j : stripe s x 0 j ≠ stripe s x 1 j := by
    by_cases ht : address s x 1 j = address s x 0 j <;> simp [stripe,ht]; exact Ne.symm ht
  intro a i j hij
  change s * (stripe s x i a : ℝ) = s * (stripe s x j a : ℝ) at hij
  have ht := mul_left_cancel₀ h.ne' hij
  have hh : stripe s x i a = stripe s x j a := by exact_mod_cast ht
  fin_cases i <;> fin_cases j <;> first | rfl | exact ((he a) hh).elim | exact ((he a) hh.symm).elim

lemma stayNear {s : ℝ} (hs : 0 < s) (x : Points 2) :
    dist (tag s (stripe s x)) x ≤ 16*s := by
  let v := tag s (stripe s x) - x
  have h i j : |v i j| ≤ 2*s := by
    have hh := coord_grid_bound hs x i j
    change |s * (stripe s x i j:ℝ) - x i j| ≤ _
    change |s * (address s x i j:ℝ) - x i j| ≤ _ at hh
    rcases Fin.eq_zero_or_eq_succ i with h|⟨k,h⟩
    · subst i; rw [show stripe s x 0 j=address s x 0 j from by simp [stripe]]; linarith
    subst i; fin_cases k
    change |s * (stripe s x 1 j:ℝ) - x 1 j| ≤ _
    change |s * (address s x 1 j:ℝ) - x 1 j| ≤ _ at hh
    by_cases hx : address s x 1 j=address s x 0 j
    · rw [show stripe s x 1 j=address s x 1 j+1 from by simp [stripe,hx]]
      rw [abs_le] at *; push_cast
      constructor <;> linarith [hh.1,hh.2]
    · rw [show stripe s x 1 j=address s x 1 j from by simp [stripe,hx]]; linarith only [hh,hs]
  rw [dist_eq_norm,← sq_le_sq₀ (norm_nonneg _) (by positivity)]
  rw [← Points.flatten.norm_map v, EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 2 × Axis, (2*s)^2 := Finset.sum_le_sum (fun i _ => sq_le_sq.mpr
      (by rw [abs_of_pos (show 0 < 2*s by positivity)]; exact h i.1 i.2))
    _ ≤ _ := by simp; nlinarith only [hs]

def strip (A : Levels G) (b : ℝ) (j : ℕ) := stripe (mag A b j)⁻¹ detectors

def placement (A : Levels G) (b : ℝ) (j : ℕ) : Points 2 := tag ((mag A b j)⁻¹) (strip A b j)
def tiltLength (A : Levels G) (b : ℝ) (j : ℕ) : Points 2 := tag (A.S.a j) (strip A b j)
lemma placement_generic (A : Levels G) (b : ℝ) (j : ℕ) : placement A b j ∈ generic 2 :=
  stripeGeneric (inv_pos.mpr (mag_pos ..)) detectors
lemma tilt_rule (A : Levels G) (b : ℝ) (j : ℕ) : tiltLength A b j = gap A b j • placement A b j := by
  ext i k; change A.S.a j * _ = (A.S.a j * mag A b j) * ((mag A b j)⁻¹ * _); field_simp [(mag_pos ..).ne']
lemma tilt_generic (A : Levels G) (b : ℝ) (j : ℕ) : tiltLength A b j ∈ generic 2 :=
  tilt_rule A b j ▸ Next.UVStress.scales_wild (gap_pos ..) _ (placement_generic A b j)
lemma places_limit (A : Levels G) (h : G.Simple) (hb : 0 < b) : Tendsto (placement A b) atTop (𝓝 detectors) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _=>dist_nonneg) (fun i=> stayNear (inv_pos.mpr (mag_pos ..)) _) ?_
  have hf := (tendsto_inv_atTop_zero.comp (mag_rate A h hb)).const_mul 16
  simpa only [mul_zero,Function.comp_apply] using hf
end YM.SharpGram.Weak
