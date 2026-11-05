import YM.Pert.Fourier.Lava
/-! Removing heat on the symbol (positive inverse length simultaneously in both expression and reference, only away from zero). -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Band
open YM.Next.Rank.Radian MeasureTheory Lattice Topology Filter Analysis Maxwell
open scoped ContDiff BigOperators RealInnerProductSpace FourierTransform Classical

lemma greenSpire : Spire Green := (Spire.rope normal).product Spire.hill
lemma blazing (b : ℝ) : ContDiff ℝ ∞ (blaze b) := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)) -- parameter name see
lemma hotter (b : ℝ) (x : E4) (hx : x≠0) : ContDiffAt ℝ ∞ (Green * blaze b) x := (Maxwell.freeSmooth hx).mul (blazing b).contDiffAt

def warm (b : ℝ) := Green * blaze (Real.pi^2/b)
def fixedMol := Green * blaze (Real.pi^2)
def UVHeat (j : ℕ) : ℝ := ((j+1:ℕ):ℝ)⁻¹^2
lemma UVHeat_pos (j : ℕ) : 0< UVHeat j := by unfold UVHeat; positivity
lemma UVHeat_zero : Tendsto UVHeat atTop (𝓝 0) := by
  have he : Tendsto (fun j=>((j+1:ℕ):ℝ)) atTop atTop := by push_cast; exact tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R:=ℝ))
  unfold UVHeat; simpa using (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp he |>.pow 2
lemma scale_price {v : ℝ} (hv : 0<v) (x : E4) : warm (v⁻¹^2) x = v^2 * fixedMol (v • x) := by
  simp only [Green,warm,fixedMol, Pi.mul_apply,blaze,norm_smul,Real.norm_of_nonneg hv.le]; field_simp
lemma scale_price_ten (D : List Axis) {v : ℝ} (hv : 0<v) {x : E4} (hx : x≠0) : dV D (warm (v⁻¹^2)) x = v^(D.length+2) * dV D fixedMol (v • x) := by
  have h0 {x : E4} (hx : x≠0) : v • x ≠ 0 := smul_ne_zero hv.ne' hx
  induction D generalizing x with
  | nil => exact scale_price hv x
  | cons i L ih =>
    have he := outside_eq _ _ (fun x hx=>ih (show x≠0 from hx)) (x:=x) hx
    change grad i (dV L (warm _)) _ = _ * grad i (dV L fixedMol) _
    unfold grad; rw [GermD (basis i) he]; unfold Analysis.D
    have hh := stroll L (hotter (Real.pi^2) (v • x) (h0 hx))
    have hab : DifferentiableAt ℝ (fun y=>dV L fixedMol (v • y)) x := (hh.differentiableAt (show (∞:ℕ∞ω)≠0 by simp) |>.comp (g:=dV L fixedMol) x (show DifferentiableAt ℝ (fun (y:E4)=> v • y) x by fun_prop))
    rw [fderiv_const_mul hab (v^(L.length+2)),fderiv_comp_smul]
    simp only [smul_apply, smul_eq_mul,List.length_cons]; rw [show L.length+1+2=L.length+2+1 by omega,pow_add]; ring

lemma compare_heat (D : List Axis) {z : E4} (hz : z≠0) {b : ℝ} (hb : b>0) : harmon (press D (liturgy b)) z = ((dV D Green z - dV D (warm b) z : ℝ):ℂ) := by
  rw [takes D (passion hb)]
  have e : (harmon (liturgy b)) =ᶠ[𝓝 z] fun u => ((Green - warm b) u:ℂ) := outside_eq _ _ (fun x hx=> by rw [chants_h hb x hx]; congr 1; unfold warm blaze; simp only [Pi.sub_apply,Pi.mul_apply]; have hb' := hb.ne'; rw [mul_sub,mul_one]; field_simp) hz
  rw [(crushed D e).eq_of_nhds, echoes (f:=Green - warm b) D (fun x hx=> (freeSmooth hx).sub (hotter _ _ hx)) hz]; exact congrArg Complex.ofReal (show dV D (Green - warm b) z = _ from strolling D (f:=Green) (g:=warm b) (fun x hx => freeSmooth hx) (fun x hx => hotter _ _ hx) hz)
lemma off_zero_moll (D : List Axis) (z : E4) (hz : z≠0) : Tendsto (fun j:ℕ=>harmon (press D (liturgy (UVHeat j))) z) atTop (𝓝 ((dV D Green z:ℝ):ℂ)) := by
  obtain ⟨C,hCp,H⟩ := faded greenSpire (t:=Real.pi^2) (by positivity) D (D.length+3)
  have hp : 0<‖z‖ := norm_pos_iff.mpr hz
  let v (i:ℕ):ℝ:=(i:ℝ)+1
  let p:=D.length+3
  have he : Tendsto v atTop atTop := tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hv (i) : 0<v i := by unfold v; positivity
  have h0 : Tendsto (fun i=>‖dV D (warm (UVHeat i)) z‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ (by simpa using (tendsto_inv_atTop_zero.comp he).const_mul (C/‖z‖^p))
    filter_upwards [he.eventually (eventually_ge_atTop (1/‖z‖))] with i hi
    unfold UVHeat; push_cast; change ‖dV D (warm ((v i)⁻¹ ^2)) z‖ ≤ _
    have ht0 : 1 ≤ ‖v i • z‖ := by rw [norm_smul,Real.norm_of_nonneg (hv i).le]; exact (div_le_iff₀ hp).mp hi
    change ‖dV D (warm _) z‖ ≤ (C/‖z‖^p)*(v i)⁻¹
    rw [scale_price_ten D (hv i) hz,norm_mul, Real.norm_of_nonneg (pow_nonneg (hv i).le _)]
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ (hv i)).mpr -- mul_inv
    have H := H (v i • z) ht0; rw [norm_smul,Real.norm_of_nonneg (hv i).le,mul_pow] at H
    rw [show ∀ a : ℝ,(v i)^(D.length+2)*a*v i=(v i)^p*a from fun a=> by rw [mul_right_comm]; rfl]
    exact (le_div_iff₀ (pow_pos hp p)).mpr (by rw [mul_right_comm]; exact H)
  have heq : ∀ i, harmon (press D (liturgy (UVHeat i))) z = ((↑(dV D Green z:ℝ)) - ↑(dV D (warm (UVHeat i)) z):ℂ) := fun i=> by rw [compare_heat D hz (UVHeat_pos _),Complex.ofReal_sub]
  simp_rw [heq]; simpa only [Complex.ofReal_zero,sub_zero,Function.comp_apply] using tendsto_const_nhds (x:=((dV D Green z:ℝ):ℂ)) |>.sub (Complex.continuous_ofReal.continuousAt (x:=0) |>.tendsto.comp (tendsto_zero_iff_norm_tendsto_zero.mpr h0))

def casual (D : List Axis) (z : E4) := ((dV D Green z:ℝ):ℂ)

end YM.Pert.Band
