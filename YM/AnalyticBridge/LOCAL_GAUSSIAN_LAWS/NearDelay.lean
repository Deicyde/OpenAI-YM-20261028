import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ChipHeal
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.ITERATION_NO_LOSS.Scales



/-!
# Post-L cost of comparing a whole R-vicinity of V for $†d_1 Z$

Calibrate $\gamma$, costs before period, scale power in *these*
RG conventions.

Here B is literally `log² x` rounded up.

Not buying e^-x
or free-field polynomial price uniform before L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure  Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}

/-- patch cost with R=B. Coarse constant gauge. `Clears` prem
includes edge margin; flag test only on the same V. -/
def clearanceFare (x : ℝ) := 16*(2*((radiusB x+1:ℕ):ℝ)+1)^5 * Fintype.card PlaqAxes * temp x

lemma axial (S : StepData c f) (U : Stores S) (V : Config G c) (o : Site c)
    (he : Clears U x o (radiusB x)) (hm : 100*(1+radiusB x)≤c.val) (h : U.flags=RG.flags (temp x) V) :
    ∃ z : Site c→G.El, (∀ i : Bond c, separation o i.1≤radiusB x → G.chord (Lattice.gauge z V i)≤ clearanceFare x) ∧ paid S (replica S.ratio (Lattice.gauge z V)) o (radiusB x) (clearanceFare x) := by
  let R := radiusB x
  have hv (i : Site c) (hi : separation o i ≤ R+1) (p : PlaqAxes) : toll V (i,p) ≤ temp x := by
    by_contra! hx
    have hh : i∈ U.flags := h.symm ▸ (flags_spec ..).2 ⟨(i,p), by exact YM.Work.E01.base_touched (i,p), hx⟩
    apply he
    exact halo_spec.mpr ⟨i, Finset.mem_union_right _ hh,(separation_comm ..).trans_le (hi.trans (by unfold R; omega))⟩
  obtain ⟨w,H⟩ := Work.E08.axial_patch o V R (R+1) (by omega) (by unfold R; omega) (temp x) (temp_nonneg x) hv
  refine ⟨w,H,fun i hi => ?_⟩
  unfold replica; split
  · rw [G.chord_one]; unfold clearanceFare; have hh := temp_nonneg x; positivity
  exact H _ hi

section fare

def census (G : Gauge) (P : Patch) (x A η H : ℝ) :=
  let N := (Fintype.card (Site P.L):ℝ)*(LocalJet.grain (boxCharge x) * (Fintype.card Axis:ℝ))* (Fintype.card G.ColorIndex:ℝ)
  N^2 * η⁻¹ * matter G P x A (clearanceFare x)*H⁻¹
lemma census_clock (G : Gauge) (S : StepData c f) (x A η H : ℝ) : clockChip G S x (clearanceFare x) 0 η H A = census G S.patch x A η H := by simp [clockChip,census,slotCount,LocalJet.chips]

set_option maxHeartbeats 700000 in
/-- Representation of subpower costs (reuse verified ITERATION_NO_LOSS
Scales, not that trajectory's cross kernels). Direct $x^{-1/4}$
even without optimizing the exponent. -/
lemma fares (G : Gauge) (P : Patch) (A : ℝ) (hA : 0≤A) {η H δ : ℝ} (he : 0<η) (hH : 0<H) (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop, 0≤clearanceFare x ∧ clearanceFare x≤δ ∧ census G P x A η H≤x^(-(1/4):ℝ) := by
  open Extra.Iteration.Scales in
    let b (x : ℝ) := 1+(radiusB x:ℝ)
    have hb : Tiny id b := Tiny.cover_size
    let D0 := 16*(3:ℝ)^5*(Fintype.card PlaqAxes:ℝ)
    let T x := D0*b x^5
    have heq (x : ℝ) : b x=1+radiusB x := rfl
    have h1 (x : ℝ) : 1≤b x := by unfold b; simp
    have ht : Tiny id T := Tiny.mul (Tiny.const tendsto_id D0 (by unfold D0; positivity)) (hb.pow tendsto_id 5) tendsto_id
    have hD : Tendsto clearanceFare atTop (𝓝 0) := by
      let C := 16*(5:ℝ)^5*(Fintype.card PlaqAxes:ℝ)
      apply squeeze_zero' (by filter_upwards with x; unfold clearanceFare; have h := temp_nonneg x; positivity)
        (_ : ∀ᶠ x in atTop, clearanceFare x ≤ C*((radiusB x:ℝ)^5*temp x)) (by simpa only [mul_zero] using! (Work.E09.radiusB_temp 5).const_mul C)
      filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx
      unfold clearanceFare C; rw [mul_assoc (16*(5:ℝ)^5)] -- rather calc
      have he : 1≤(radiusB x:ℝ) := by exact_mod_cast hx
      push_cast
      calc
        _ ≤ 16*(5*(radiusB x:ℝ))^5*(Fintype.card PlaqAxes:ℝ)*temp x := by have hx := temp_nonneg x; gcongr; linarith
        _ = _ := by ring
    have hF (x : ℝ) : clearanceFare x ≤ T x*temp x := by
      unfold clearanceFare T D0
      calc
        _ ≤ 16*(3*b x)^5*(Fintype.card PlaqAxes:ℝ)*temp x := by have ht := temp_nonneg x; gcongr; rw [Nat.cast_add,← show 1+(radiusB x:ℝ)=b x from rfl]; push_cast; have h : 0≤(radiusB x : ℝ) := Nat.cast_nonneg _; nlinarith
        _ = _ := by ring
    let Vs x := A*b x*T x
    have hV : Tiny id Vs := (((Tiny.const tendsto_id A hA).mul hb tendsto_id).mul ht tendsto_id)
    let W : ℝ := predReach P + 8
    have hW : 0≤W := by unfold W; positivity
    let Q : ℝ → ℝ := fun x => (3*W*b x)^4
    have hG (x : ℝ) (u : ℕ) (h : (u:ℝ) ≤ W*b x) : LocalJet.grain u≤Q x := by
      unfold LocalJet.grain Q; push_cast; gcongr; have := h1 x; unfold W at *; have hn : 0 ≤ ((predReach P:ℕ):ℝ) := Nat.cast_nonneg _; nlinarith only [hn,this,h,mul_nonneg hn (show 0≤b x by linarith only [this])]
    have hg : Tiny id Q := (((Tiny.const tendsto_id (3*W) (by positivity)).mul hb tendsto_id).pow tendsto_id 4) -- association
    let K := pieces P G; have hK : 0≤K := pieces_nonneg ..
    let J := (Fintype.card (Site P.L):ℝ)*(Fintype.card Axis:ℝ)*(Fintype.card G.ColorIndex:ℝ)
    let M x := K*Q x*((A+Vs x)*Vs x+Vs x*A)
    let Z x := (J*Q x)^2*η⁻¹*M x*H⁻¹
    have hA' := Tiny.const tendsto_id A hA
    have hk : Tiny id Z := Tiny.mul (Tiny.mul (Tiny.mul (Tiny.pow (Tiny.mul (Tiny.const tendsto_id J (by unfold J; positivity)) hg tendsto_id) tendsto_id 2)
      (Tiny.const tendsto_id η⁻¹ (by positivity)) tendsto_id) (Tiny.mul (Tiny.mul (Tiny.const tendsto_id K hK) hg tendsto_id)
      (Tiny.add (Tiny.mul (Tiny.add hA' hV tendsto_id) hV tendsto_id) (Tiny.mul hV hA' tendsto_id) tendsto_id) tendsto_id) tendsto_id) (Tiny.const tendsto_id _ (by positivity)) tendsto_id
    filter_upwards [hD.eventually (ge_mem_nhds hδ), Work.E09.temp_cost (1/8) (by norm_num),hk (1/8) (by norm_num), eventually_gt_atTop (1:ℝ)] with x hδ ht hk ht1
    have hs : 0≤temp x := temp_nonneg x
    have hr (x : ℝ) : till x ≤ radiusB x := by unfold till; omega
    have hb : 0 ≤ b x := (by linarith [h1 x])
    have hT : 0≤T x := by unfold T D0; positivity
    have hJ : 0≤J := by unfold J; positivity
    have hVs : 0≤Vs x := by unfold Vs; positivity
    have hq : 0≤Q x := by unfold Q; positivity
    have hu : ((boxCharge x):ℝ)≤W*b x := by
      change ((( (radiusB x+80)/20:ℕ)):ℝ)≤_
      have he : (radiusB x+80)/20≤radiusB x+4 := by omega
      apply le_trans (show ((( (radiusB x+80)/20:ℕ)):ℝ) ≤ radiusB x + 4 by exact_mod_cast he); have := h1 x; rw [heq]; unfold W; have hC : 0≤((predReach P:ℕ):ℝ) := Nat.cast_nonneg _; have hX : 0≤((radiusB x:ℕ):ℝ) := Nat.cast_nonneg _; nlinarith only [hX,hC, mul_nonneg hX hC]
    have hp : ((span P x):ℝ)≤W*b x := by
      unfold span; push_cast; have hc : (till x:ℝ)≤radiusB x := by exact_mod_cast hr x
      rw [heq]; unfold W; have hC : 0≤((predReach P:ℕ):ℝ) := Nat.cast_nonneg _; have hX : 0≤((radiusB x:ℕ):ℝ) := Nat.cast_nonneg _; nlinarith only [hX,hC, mul_nonneg hX hC,hc]
    have hl : 0≤clearanceFare x := by unfold clearanceFare; positivity
    let z:=wiggle x A (clearanceFare x)
    have hz : z ≤ Vs x * temp x := by
      have h : 1+(till x:ℝ) ≤ b x := add_le_add_right (by exact_mod_cast hr x) _
      unfold z wiggle
      calc
        _ ≤ A*b x * (T x*temp x) := by gcongr; exact hF x
        _ = _ := by unfold Vs; ring
    have hz0 : 0 ≤ z := wiggle_nonneg x hA hl
    have hs1 : temp x ≤ 1 := by
      apply ht.trans
      exact Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by norm_num)
    have hM : 0≤M x := by unfold M; positivity
    have hf : census G P x A η H ≤ Z x * temp x := by
      have hN : (Fintype.card (Site P.L):ℝ)*(LocalJet.grain (boxCharge x)*(Fintype.card Axis:ℝ))*(Fintype.card G.ColorIndex:ℝ) ≤ J*Q x := by unfold J; grw [hG x _ hu]; ring_nf; rfl
      have hY : matter G P x A (clearanceFare x) ≤ M x*temp x := by
        change K*LocalJet.grain _*((A+z)*z+z*A) ≤ _
        calc
          _ ≤ K*Q x*((A+Vs x)*(Vs x*temp x)+(Vs x*temp x)*A) := by gcongr; exacts [hG x _ hp,hz.trans (mul_le_of_le_one_right hVs hs1)]
          _ = _ := by unfold M; ring
      unfold census; dsimp only
      calc
        _ ≤ (J * Q x) ^ 2 * η⁻¹ * (M x * temp x) * H⁻¹ := by
          have ha : 0 ≤ matter G P x A (clearanceFare x) := matter_nonneg G P x hA hl
          apply mul_le_mul_of_nonneg_right _ (inv_pos.mpr hH).le
          refine mul_le_mul ?_ hY ha (mul_nonneg (sq_nonneg _) (inv_pos.mpr he).le)
          apply mul_le_mul_of_nonneg_right _ (inv_pos.mpr he).le
          apply pow_le_pow_left₀ _ hN; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
        _ = _ := by change ((J*Q x)^2*η⁻¹) * (M x * temp x) * H⁻¹ = (((J*Q x)^2*η⁻¹)*M x*H⁻¹)*temp x; rw [← mul_assoc, mul_right_comm (_*M x)]
    have hk : Z x≤x^(1/8:ℝ) := hk.2
    refine ⟨hl,hδ,hf.trans ((mul_le_mul hk ht hs (Real.rpow_nonneg (zero_le_one.trans ht1.le) _)).trans_eq ?_)⟩
    rw [← Real.rpow_add (zero_lt_one.trans ht1)]; norm_num

end fare
end YM.AnalyticBridge.LocalGaussianLaws.Remote
