import YM.Pert.Fourier.Fee
/-! Power saving top-box self comparison along the orbital schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Cellular
open Topology Filter Set Function Lattice MeasureTheory
open Band (turn)
open scoped Classical BigOperators

def coverLine (a : Cover) := Full.volumeFactor * ∫ k in Full.cube,(Full.delta k)⁻¹ * Full.wave false a k
lemma cover_interp (a : Cover) : coverLine a = ∫ y, cells.indicator (trace a) y := by
  let g k := (Full.delta k)⁻¹ * Full.wave false a k
  have eq (y) : (Full.cube.indicator g) (Band.turn • y) = cells.indicator (trace a) y := by
    by_cases h:y∈cells
    · rw [indicator_of_mem h,indicator_of_mem ((cells_cube _).mp h)]; rfl
    rw [indicator_of_notMem h,indicator_of_notMem (mt ((cells_cube _).mpr) h)]
  have hp := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume (Full.cube.indicator g) Band.turn (hR:=by positivity)
  simp only [eq, YM.Next.Rank.Radian.spaceD,smul_eq_mul,integral_indicator Full.cube_compact.isClosed.measurableSet] at hp
  unfold coverLine; rw [hp];unfold Full.volumeFactor; rw [zpow_neg]; norm_cast
lemma weighted (a : Cover) (n : Side) (hn : Even n.val) : (Full.toroid (wrap n a)).re = ∫ k, cells.indicator (fun q=> trace a (visit n q)) k := by
  rw [integrate_visit n hn (trace a) |>.2,Full.toroid]
  have hh (q : Site n) : (Full.topWeight n q * Full.char q (wrap n a)).re = (n.val:ℝ)⁻¹^4 * trace a (YM.Next.Rank.Radian.addr n (Lattice.lift q)) := by
    simp only [Full.char_wrapped,Complex.exp_mul_I,trace,clock,dtype,visit_defensive]
    have he' : Full.topWeight n q = (((((n.val:ℝ)^4)⁻¹ * (Full.delta (Full.moment q))⁻¹:ℝ)):ℂ) := by simp only [Complex.ofReal_mul, Complex.ofReal_inv,Complex.ofReal_pow, Complex.ofReal_natCast,Full.topWeight,zpow_neg,zpow_natCast]; rfl
    rw [he']; simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.mul_im,Complex.add_im,Complex.ofReal_im,Complex.I_im,Complex.I_re];rw [inv_pow];ring
  change Complex.reCLM (∑ q : Site n,_) = _
  rw [map_sum]; simp only [Complex.reCLM_apply] -- maybe hh
  exact (by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> hh i))
lemma strike_two (n : ℕ→Side) (h : ℕ→ℝ) (hx : ∀ i, 0<h i) (he : ∀ i, Even (n i).val) (htop : ∀ (j:ℕ), Tendsto (fun (i:ℕ)=>((n i).val:ℝ)*(h i)^j) atTop atTop) (hc : Tendsto h atTop (𝓝 0)) (d : ℕ) (a : Cover) :
   Tendsto (fun i=> ((Full.toroid (wrap (n i) a)).re - coverLine a) * (h i)^(-(d:ℤ))) atTop (𝓝 0) := by
  have hv : ∀ᶠ i in atTop, h i ≤ 1 := hc.eventually (ge_mem_nhds zero_lt_one)
  let f i:= ((Full.toroid (wrap (n i) a)).re - coverLine a)
  obtain ⟨C,hCp,E,hE,H⟩ := toroid_cost a
  let r i := (h i)^(d+1)
  have hbb (i : ℕ) (hh : 8 ≤ ((n i).val:ℝ)*(h i)^(d+1)) : 8*((n i).val:ℝ)⁻¹ ≤ r i := (div_le_iff₀ (Full.val_pos _)).mpr (by simpa only [mul_comm (r i),r] using hh)
  have hev : ∀ᶠ i in atTop, ‖f i‖ ≤ C*(r i)^2+E*((n i).val:ℝ)⁻¹/(r i)^4 := by
    filter_upwards [hv,(htop (d+1)).eventually (eventually_ge_atTop 8)] with i hi hζ
    convert! H (he i) (pow_pos (hx i) (d+1)) (pow_le_one₀ (hx i).le hi) (hbb i hζ) using 0; congr 1
    simp_rw [f,cover_interp a,weighted a _ (he i)]; dsimp only [r]; rfl
  let B i := C*(h i)^(d+2) + E*(((n i).val:ℝ)*(h i)^(4*(d+1)+d))⁻¹
  have hb : Tendsto B atTop (𝓝 0) := by
    have he0 := ((hc.pow (d+2)).const_mul C).add ((tendsto_inv_atTop_zero.comp (htop (4*(d+1)+d))).const_mul E)
    simpa only [Function.comp_apply,zero_pow (show d+2≠0 by omega),zero_pow (n:=4),mul_zero,mul_zero,add_zero] using he0
  have hh i : (C*r i^2+E*((n i).val:ℝ)⁻¹/r i^4) * (h i)^(-(d:ℤ)) = B i := by
    dsimp [r,B]; rw [zpow_neg, zpow_natCast]; rw [pow_add _ (4*(d+1)), show 4*(d+1)=(d+1)*4 from by ring, pow_mul (h i) (d+1),pow_succ,pow_add _ d]; field_simp [(hx i).ne',(Full.val_pos (n i)).ne']; ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) (hev.mono (fun i hi=> by rw [norm_mul,Real.norm_of_nonneg (zpow_pos (hx i) _).le, ←hh i]; exact mul_le_mul_of_nonneg_right hi (zpow_pos (hx i) _).le)) hb)
end YM.Pert.Cellular
