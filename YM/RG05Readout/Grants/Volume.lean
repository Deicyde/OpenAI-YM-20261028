import YM.RG05Readout.Aligned.Geometry
import YM.RG05Readout.Address.Shape
/-!
# Uniform wrap costs in the canonical threshold history

Take the tail for each demanded horizon. The size of pencils can depend
on this horizon but NOT on N or p. This argument avoids presuming allocation
of e.g. P-dependent blocks; holds once u already fine at *any admitted period*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Copper
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native Address
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

-- all meshs, K_t volume at least integer. v^η factor double via λ
lemma on_mesh {G:Gauge}(C: Levels G) (m p:ℕ): Real.exp (C.S.scale m) ≤ (C.S.side m p).val:=by
   have he:= C.S.span_side m p
   have h:0<C.S.a m:= C.S.a_pos m
   rw [Schedule.scale, Real.exp_log (inv_pos.mpr h), ← one_div, div_le_iff₀ h, mul_comm, he]; exact_mod_cast (C.S.period p).property

-- logarithms; >=2ad. use height, allocate B denominator after χ; exponential stronger than any ratio.
lemma oversized {G:Gauge}(A:Levels G)(hG:G.Simple)(Z:ℝ):
   ∀ᶠ m in atTop,∀ p:ℕ, Trace.Physical.Germ.wraps (A.budget m) (A.S.side m p) ≤ Real.exp (-Z*A.S.scale m):=by
    let C:= A.clock; let L:=A.S; let t:=A.S.scale; let b (m):=(A.budget m).supportExponent; let q:=b 0
    have hb : Monotone b := A.fits.deepExp; have hq : 0 < q := (A.budget 0).exponent_pos
    let s (m:ℕ):=(↑(A.budget m).B:ℝ); let w (m:ℕ):=(10:ℝ)*(4*s m+2); let y (m:ℕ):=(2+max 0 Z*(t m)/q)
    have ht:= L.divergent
    have hs(m):0 ≤ s m:=Nat.cast_nonneg _
    have hm : Height A.S atTop t (fun m=>m) 1:= level_height tendsto_id
    obtain hM:= lambda_rate hG ht hm
    have hp : RateLE atTop t (fun i=>((Lambda A i)^2:ℝ)) 0:= by simpa using (hM.power 2).pays ht
    have hw: RateLE atTop t s 0:= hp.of_norm_le (Eventually.of_forall fun i=> by rw [Real.norm_of_nonneg (hs i)]; exact (budgetW A i).le)
    have ht0 : RateLE atTop t t 0:= RateIs.pays ⟨ht.eventually_gt_atTop 0,by simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp ht⟩ ht
    have hB : RateLE atTop t w 0:=by
       have hz:= (RateLE.const (10:ℝ) ht).mul ((((RateLE.const (4:ℝ) ht).mul hw)).addMax (RateLE.const (2:ℝ) ht) ht)
       simpa only [add_zero, max_self] using hz
    have hy : RateLE atTop t y 0:=by
       have ha := (RateLE.const (2:ℝ) ht).addMax (((RateLE.const (max 0 Z) ht).mul ht0).mul (RateLE.const q⁻¹ ht)) ht
       simpa only [y,add_zero,max_self, div_eq_mul_inv] using ha
    have hx:= hy.mul hB
    filter_upwards [hx (1:ℝ) (by norm_num), ht.eventually_ge_atTop 0] with i h hi p
    let z':= ((A.S.side i p).val:ℝ); have hv:= (le_abs_self (y i*w i)).trans h
    have hv' : y i * w i ≤ z':=le_trans hv (show Real.exp (1*t i) ≤ z' from one_mul (t i) |>.symm ▸ on_mesh A i p)
    have hh : 0 < w i:=by unfold w; positivity
    have hh' : 2 + (max 0 Z*(t i)/q) ≤ z' / (w i):= (le_div_iff₀ hh).mpr hv'
    unfold Trace.Physical.Germ.wraps; apply Real.exp_le_exp.mpr
    change 2*b i - b i*z'/w i ≤ -Z*t i
    rw [mul_div_assoc]; apply le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_left hh' (hq.trans_le (hb i.zero_le)|>.le)) _)
    have hY:= le_mul_of_one_le_left (show 0 ≤ max 0 Z * t i from mul_nonneg (le_max_left _ _) hi) (show (1:ℝ) ≤ b i/q from (one_le_div hq).mpr (hb i.zero_le)); have hz:= mul_le_mul_of_nonneg_right (le_max_right 0 Z) hi; simp only [div_eq_mul_inv] at hY hz ⊢; linarith only [hY,hz]
end YM.RG05Readout.Copper
