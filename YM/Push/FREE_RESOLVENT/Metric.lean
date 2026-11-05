import YM.Push.FREE_RESOLVENT.Fold

/-!
# Same-level inverses in the exact kernel format of Rack

Construct the inverse rows *themselves*. From the two forward Rows of
Precision.Bed (original and modified -- don't assume any inverse data,
period bound, F06 repair assumption, etc.) & pre-L forward width and
coercivity, can thus obtain the inverse fields closed at pre-L cost. Includes
harmonic. Preserve cuts for metric roots etc separately.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice RG Matrix Laurent Bloch Exterior Precision Work.F08 Filter Topology
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

def margin (α : Type*) [Fintype α] (s M r : ℝ) := safeRate s ((Fintype.card α:ℝ)*M) r
lemma margin_pos {s M r : ℝ} (α : Type*) [Fintype α] (hs : 0 < s) (hm : 0 ≤ M) (hr : 0 < r) :
    0 < margin α s M r := rate_pos hs (by positivity) hr

def inversePrice (α : Type*) [Fintype α] (s M r u γ : ℝ) := sheetPay (margin α s M r-γ) * (r/2+u)⁻¹

omit [DecidableEq α] in
lemma inversePrice_pos {s M r u γ : ℝ} (hu : 0 ≤ u) (hr : 0 < r) (hg : γ < margin α s M r) :
    0 < inversePrice α s M r u γ := mul_pos (sheetPay_pos _ (sub_pos.mpr hg)) (by positivity)

theorem strip_resolvent (P : Row α α) {s M r u γ : ℝ} (hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < s) (hm : 0 ≤ M) (hP : P.strip s M)
    (hg : ∀ n, Gap (P.acts n) r) (hc : γ < margin α s M r) :
    ∃ Q : Row α α, Q.strip γ (inversePrice α s M r u γ) ∧ ∀ n : Side, Q.acts n = resolve (P.acts n) u := by
  let w := margin α s M r
  have he : 0 < w := margin_pos _ hs hm hr
  refine Universal.publish _ he (by positivity) hc
    (Universal.inverses (P.rights _ _ hP hs.le) u fun n => ((hg n).shift u).unit_det (by positivity)) fun n => ?_
  exact resolve_point (by positivity) hs (taxi_schur hP hs.le n) (hg n) hr hu he.le le_rfl

-- convolution export and uniqueness in row arithmetic
omit [DecidableEq α] in
theorem row_witness {β : Type*} {P P' : Row β α} {s M M' : ℝ} (hs : 0 < s) (hp : P.strip s M) (hp' : P'.strip s M')
    (h : ∀ n, P.acts n=P'.acts n) : P=P' := by
  funext i j z
  let b (R : ℕ) : Side := ⟨2*R+1,by omega⟩
  have he {P : Row β α} {M : ℝ} (h : P.strip s M) :
      Tendsto (fun R => P.acts (b R) (0,i) (wrap (b R) z,j)) atTop (𝓝 (P i j z)) := by
    have hx : Tendsto (fun R : ℕ => (Fintype.card α:ℝ)*(Real.exp (-s*R)*M)) atTop (𝓝 0) := by
      have hw : Tendsto (fun R : ℕ => Real.exp (-s*R)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (by
        exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hs))
      simpa using (hw.mul_const M).const_mul (Fintype.card α:ℝ)
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop (size z), hx.eventually (gt_mem_nhds hε)] with R hR hl
    have ht := lift_comparison h hs.le (0 : Site (b R)) z i j R hR (Nat.lt_succ_self _)
    rw [zero_add] at ht
    exact ht.trans_lt hl
  apply tendsto_nhds_unique (he hp)
  simpa only [← h] using he hp'



section Bed




end Bed
end YM.FreeResolvent
