import YM.Bid.Craft
import YM.Work.F06.Energy
import YM.Work.F06.Phase



/-!
# Recovering positivity at zero

For every vector in the tested complex three-form space, find a real
line in momentum space on which the vector belongs to the range to first
order. This is where dimension four and the preceding, not succeeding,
coboundary in `Reaches` matter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F06
open Lattice Laurent Bloch Exterior Craft Finset Filter Matrix
open scoped BigOperators Topology

def lineMomentum (n : Axis → ℝ) (t : ℝ) : Momentum := fun i => (t:ℂ) * (n i:ℂ)

def slopeQ (n : Axis → ℝ) : Axis → ℂ := fun i => Complex.I * (n i:ℂ)

lemma real_lineMomentum (n : Axis → ℝ) (t : ℝ) : star (lineMomentum n t) = lineMomentum n t := by
  funext i; simp [lineMomentum]

/-- Top coordinate unique. -/
def fullBlade : TypeFace 4 := ⟨univ, by simp [Axis]⟩

lemma fullBlade_only (a : TypeFace 4) : a = fullBlade := by
  apply Subtype.ext
  apply Finset.eq_univ_of_card
  simp [Axis, a.property]

lemma wedge_action (r : ℕ) (z : Axis → ℂ) (v : TypeFace r → ℂ) (i : TypeFace (r+1)) :
    (wedge r z *ᵥ v) i = ∑ k, z k * (left ℂ r k *ᵥ v) i := by
  simp_rw [wedge, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Evaluation into the (single) complex top coordinate. As a real
linear map this has a nontrivial kernel. -/
def wedgeProbe (x : TypeFace 3 → ℂ) : (Axis → ℝ) →ₗ[ℝ] ℂ where
  toFun n := (wedge 3 (slopeQ n) *ᵥ x) fullBlade
  map_add' a b := by
    simp_rw [wedge_action, slopeQ, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' t a := by
    change (wedge _ _ *ᵥ _) _ = t • _
    simp_rw [wedge_action, slopeQ, Complex.real_smul, Pi.smul_apply,
      smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma exists_null_axis (x : TypeFace 3 → ℂ) :
    ∃ n : Axis → ℝ, n ≠ 0 ∧ wedge 3 (slopeQ n) *ᵥ x = 0 := by
  let W := wedgeProbe x
  have hi : ¬ Function.Injective W := by
    intro he
    have hb := (LinearMap.finrank_le_finrank_of_injective he).trans (RCLike.finrank_le_two ℂ)
    rw [Module.finrank_pi] at hb
    simp [Axis] at hb
  unfold Function.Injective at hi
  push Not at hi
  obtain ⟨n,m,hn,he⟩ := hi
  refine ⟨n-m, sub_ne_zero.mpr he, ?_⟩
  have h : W (n-m) = 0 := by rw [map_sub, hn, sub_self]
  funext i
  rw [fullBlade_only i]; exact h

lemma first_range (x : TypeFace 3 → ℂ) :
    ∃ (n : Axis → ℝ) (a : TypeFace 2 → ℂ), x = wedge 2 (slopeQ n) *ᵥ a := by
  obtain ⟨n, hn, he⟩ := exists_null_axis x
  have hk : ∃ k, slopeQ n k ≠ 0 := by
    by_contra! H
    apply hn; funext i
    have h := H i
    simpa [slopeQ] using h
  obtain ⟨k,hk⟩ := hk
  have h := cartan_split x (slopeQ n) k hk
  rw [he, Matrix.mulVec_zero, smul_zero, add_zero] at h
  exact ⟨n, _, h⟩

lemma deriv_step (n : Axis → ℝ) (i : Axis) :
    HasDerivAt (fun t => q (lineMomentum n t) i) (slopeQ n i) 0 := by
  simpa [slopeQ, q, lineMomentum] using!
    (((Complex.ofRealCLM.hasDerivAt (x:=0)).mul_const (n i:ℂ)).const_mul Complex.I).cexp.sub_const 1

lemma rescaled_step (n : Axis → ℝ) (i : Axis) :
    Tendsto (fun t : ℝ => (t:ℂ)⁻¹ * q (lineMomentum n t) i) (𝓝[≠] 0) (𝓝 (slopeQ n i)) := by
  simpa [Complex.real_smul, lineMomentum, q] using (deriv_step n i).tendsto_slope_zero

lemma rescaled_symbol (r : ℕ) (n : Axis → ℝ) (x : TypeFace r → ℂ) (i : TypeFace (r+1)) :
    Tendsto (fun t : ℝ => (symbol r (lineMomentum n t) *ᵥ ((t:ℂ)⁻¹ • x)) i)
      (𝓝[≠] 0) (𝓝 ((wedge r (slopeQ n) *ᵥ x) i)) := by
  simp_rw [Matrix.mulVec_smul, symbol, Pi.smul_apply, smul_eq_mul, wedge_action,
    Finset.mul_sum, ← mul_assoc]
  exact tendsto_finsetSum _ fun k _ => (rescaled_step n k).mul_const _

lemma harmonic_lower (Q : C3) {η A v : ℝ} (hr : Reaches Q v) (hs : Q.strip η A)
    (hη : 0 < η) (x : TypeFace 3 → ℂ) :
    v * sqLength x ≤ pairingRe (Q.read 0) x x := by
  obtain ⟨n,a,hx⟩ := first_range x
  let p := lineMomentum n
  let X := fun t : ℝ => symbol 2 (p t) *ᵥ ((t:ℂ)⁻¹ • a)
  let l := 𝓝[≠] (0:ℝ)
  have h0 (i : Axis) : Tendsto (fun t => q (p t) i) l (𝓝 0) := by
    have hh := (deriv_step n i).continuousAt.tendsto
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    simpa [p, q, lineMomentum] using hh
  have hp i j : Tendsto (fun t => Q.read (p t) i j) l (𝓝 (Q.read 0 i j)) :=
    row_entry_hlimit hs hη p (real_lineMomentum n) h0 i j
  have hh i : Tendsto (fun t => X t i) l (𝓝 (x i)) := by
    rw [hx]; exact rescaled_symbol 2 n a i
  have hu : Tendsto (fun t => sqLength (X t)) l (𝓝 (sqLength x)) := by
    simp_rw [sqLength_apply]
    exact tendsto_finsetSum _ fun i _ => (hh i).norm.pow _
  have hv : Tendsto (fun t => pairingRe (Q.read (p t)) (X t) (X t)) l
      (𝓝 (pairingRe (Q.read 0) x x)) := by
    have hg : Tendsto (fun t => dotProduct (star (X t)) (Q.read (p t) *ᵥ X t)) l
        (𝓝 (dotProduct (star x) (Q.read 0 *ᵥ x))) := by
      unfold dotProduct Matrix.mulVec dotProduct
      refine tendsto_finsetSum _ fun i _ => (hh i).star.mul ?_
      exact tendsto_finsetSum _ fun j _ => (hp i j).mul (hh j)
    exact Complex.continuous_re.continuousAt.tendsto.comp hg
  exact le_of_tendsto_of_tendsto' (hu.const_mul v) hv
    (fun t => (hr (p t) (real_lineMomentum n t)).2 ((t:ℂ)⁻¹ • a))

end YM.Work.F06
