import YM.Push.PRICE_COMPILER.Compiler
import YM.Push.PRICE_COMPILER.PathBudget


/-!
# Conditional numerical support transfer

E `ageom`  in our conventions. Not assuming a smaller width or
support test for the *next* step after one projection. Give a finite constant
(depending on the quoted pre-data; if polynomial power is provided only after
L it can of course also depend on that power). Uniform in both actual
period and history depth. **Must** be invoked with the true read support in
the halo, with *every* dependency; doesn't give layout or actual cap of
cluster sums. Every use must still afford this constant in its bill including
if used repeatedly. Not an all-gas estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Pressure Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Termwise version of the pre-contraction on projected covers.
No dependence on each support's cardinality or the period in this cost. -/
theorem cover_fee {m n : Side} (q : Ratio m n) (M B s : ℕ) (h : 0 < B) (hm : M ≤ 2*B)
    (X : Support n) (Y : Support m) (hf : Y ⊆ halo (s*B) (X.image q.parent)) {e E A : ℝ}
    (hp : 0 < A) (he : e ≤ E) (hz : 0 ≤ E) (hint : 10 * haloC s * E / q.count.val < A/2) (d : ℕ) :
    Real.exp (e * coverNumber B Y) * (1+(coverNumber M X:ℝ))^d ≤
      (Real.exp (E * haloC s) * momentFactor d (A/2)) * Real.exp (A * coverNumber M X) := by
  let C := haloC s
  let N := coverNumber B Y
  let D := coverNumber M X
  let L := q.count.val
  have hL : (0:ℝ) < L := Nat.cast_pos.mpr q.count.property
  have ha : L*N ≤ (L+10*D)*((s+6)+(s+6)+1)^4 :=
    (Nat.mul_le_mul_left _ (cover_mono hf _)).trans (collapse q X M B h hm s)
  have hN : (N:ℝ) ≤ C + (10*C/L)*D := by
    have hh : (L:ℝ) * N ≤ ((L:ℝ) + 10*D)*C := by
      unfold C haloC; exact_mod_cast ha
    apply le_of_mul_le_mul_left _ hL
    apply hh.trans_eq
    field_simp
  have hv : e*(N:ℝ) ≤ E*C+(A/2)*(D:ℝ) := calc
    e*(N:ℝ) ≤ E*(N:ℝ) := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)
    _ ≤ E*(C+(10*C/L)*D) := mul_le_mul_of_nonneg_left hN hz
    _ = E*C+(10*haloC s*E/q.count.val)*D := by unfold C L; ring
    _ ≤ E*C+(A/2)*D := by gcongr
  let u := momentFactor d (A/2)
  calc
    _ ≤ Real.exp (E*C+(A/2)*D)*(u*Real.exp (A/2*D)) := mul_le_mul
      (Real.exp_monotone hv) (pays_moment d D (half_pos hp)) (by positivity) (Real.exp_pos _).le
    _ = _ := by
      change Real.exp _ * (_*Real.exp _) = _ * Real.exp (A* (D:ℝ))
      unfold u
      rw [Real.exp_add, show A*(D:ℝ)=(A/2)*D+(A/2)*D by ring, Real.exp_add]; ring

namespace Permit
variable {G : Gauge} {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
    {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Permit M I a)
include h

lemma cover_band (m : ℕ) : (a.budget (m+1)).B ≤ 2*(a.budget m).B := by
  let j := a.clock.J (m+1)
  let N := (a.budget (m+1)).B; let n := (a.budget m).B
  have hp := h.post.priced.1 j (first_le h.paid (m+1)) _ (h.paid.pays m)
  have he : N^2 ≤ 2*n^2 := by
    change Stock.scaleB (a.clock.hatBeta (m+1))^2 ≤ 2*Stock.scaleB (a.clock.hatBeta m)^2
    rw [beta_eq h.paid]; exact hp
  change N ≤ 2*n; nlinarith

theorem support (m p d : ℕ) :
    let S := a.clock.op m p
    let j := a.clock.J (m+1); let i := a.clock.J m
    let s := P.reserve.rad j i; let v := a.budget (m+1); let u := a.budget m
    let E := u.supportExponent + P.reserve.allow j i
    ∀ (X : Support (a.S.side (m+1) p)) (Y : Support (a.S.side m p)),
      Y ⊆ halo (s*u.B) (X.image S.ratio.parent) → ∀ e : ℝ, e ≤ E →
        Real.exp (e * coverNumber u.B Y)*(1+(coverNumber v.B X:ℝ))^d ≤
          (Real.exp (E*haloC s)*momentFactor d (v.supportExponent/2))*Real.exp (v.supportExponent * coverNumber v.B X) := by
  intro S j i s v u E X Y hf e he
  apply cover_fee S.ratio v.B u.B s u.B_pos (h.cover_band m) X Y hf v.exponent_pos he (add_nonneg u.exponent_pos.le
    (P.reserve.extra ..)) ?_ d
  have hd := (h.pre.at_edge h.paid m).covers
  change 10 * haloC s * ((a.params m).supportExponent + _)/ (a.S.block m).val < (a.params (m+1)).supportExponent / 2
  rw [params_eq h.paid, params_eq h.paid]; exact hd
end Permit
end YM.Push.PriceCompiler
