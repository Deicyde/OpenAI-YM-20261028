import YM.Further.CURVED_GAUSSIAN_JETS.Windows
/-!
# Integral representation per Panel line in the real physical metric
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Line
open Function Filter MeasureTheory Set Matrix Unitary SectorNext.Vacuum Precision
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {I : Type*} [Fintype I] [DecidableEq I]

def clock (x u : ℝ) := (1+u)⁻¹ - (x+u)⁻¹
lemma cleared {x : ℝ} (h : 0<x) : IntegrableOn (clock x) (Ioi 0) ∧ ∫ u : ℝ in Ioi 0, clock x u = Real.log x := by
  let g (u : ℝ) := Real.log (1+u) - Real.log (x+u)
  have hg (u : ℝ) (hu : u∈Ici 0) : HasDerivAt g (clock x u) u := by
    have hv : 0 ≤ u := hu
    unfold clock g; simp_rw [inv_eq_one_div]
    exact (((hasDerivAt_id' u).const_add _).log (by dsimp; linarith only [hv])).sub
      (((hasDerivAt_id' u).const_add _).log (by dsimp; linarith only [h,hv]))
  have hh : Tendsto g atTop (𝓝 0) := by
    have he : Tendsto (fun u : ℝ => (1-x)/(x+u)) atTop (𝓝 0) :=
      Tendsto.div_atTop (a:=1-x) tendsto_const_nhds (tendsto_atTop_add_const_left _ x tendsto_id)
    have hm := (he.const_add (1:ℝ)).log (by norm_num)
    rw [add_zero, Real.log_one] at hm
    apply hm.congr' (eventually_atTop.mpr ⟨0,fun u (hu : 0≤u) => ?_⟩)
    unfold g
    rw [← Real.log_div (by linarith only [hu] : (1:ℝ)+u ≠ 0) (by linarith only [hu,h])]; congr 1
    field_simp; ring
  have hI : IntegrableOn (clock x) (Ioi 0) := by
    rcases le_total x 1 with h1|h1
    · exact integrableOn_Ioi_deriv_of_nonpos' hg (fun u hu=> sub_nonpos.mpr
        (inv_anti₀ (by linarith only [(show 0<u from hu),h] : 0<x+u) (by linarith only [h1]))) hh
    exact integrableOn_Ioi_deriv_of_nonneg' hg (fun u hu=> sub_nonneg.mpr (inv_anti₀
      (by linarith only [(show 0<u from hu)] : 0<1+u) (by linarith only [h1]))) hh
  exact ⟨hI, (integral_Ioi_of_hasDerivAt_of_tendsto' hg hI hh).trans (by simp [g])⟩

def bell (u : ℝ) := 1/(1+u)^2
lemma bell_nonneg (u : ℝ) : 0≤bell u := one_div_nonneg.mpr (sq_nonneg _)
lemma bell_int : IntegrableOn bell (Ioi 0) ∧ ∫ u : ℝ in Ioi 0, bell u = 1 := by
  let g (u : ℝ) := - (1+u)⁻¹
  have hh : Tendsto g atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (β:=ℝ) (tendsto_atTop_add_const_left _ (1:ℝ) tendsto_id)).neg
  have hg (u : ℝ) (hu : u∈Ici 0) : HasDerivAt g (bell u) u := by
    have hv : 0≤u := hu
    convert! (((hasDerivAt_id' u).const_add (1:ℝ)).inv (by dsimp; linarith)).neg using 1
    unfold bell; ring
  have hr := integrableOn_Ioi_deriv_of_nonneg' hg (fun u _=>bell_nonneg u) hh
  exact ⟨hr,(integral_Ioi_of_hasDerivAt_of_tendsto' hg hr hh).trans (by simp [g])⟩

def dose (A : Table I) (i : I) (u : ℝ) := (1+u)⁻¹ - (shifted A u)⁻¹ i i

variable {A : Table I} (h : A.PosDef)
include h
lemma inv_entry (i l : I) (u : ℝ) (hu : 0≤u) :
    let V := h.1.eigenvectorUnitary.val
    (shifted A u)⁻¹ i l = ∑ j, V i j * V l j * (h.1.eigenvalues j + u)⁻¹ := by
  intro V
  let T := conjStarAlgAut ℝ _ h.1.eigenvectorUnitary
  let f (j : I) := h.1.eigenvalues j + u
  have hf (j : I) : 0<f j := by linarith [h.eigenvalues_pos j]
  have hs : shifted A u = T (Matrix.diagonal f) := by
    rw [shifted]; nth_rw 1 [h.1.spectral_theorem]
    rw [show Matrix.diagonal f=Matrix.diagonal h.1.eigenvalues + u • (1: Table I) by
        ext i j; by_cases H : i=j <;> simp [H,f,Matrix.diagonal], map_add, map_smul,map_one]; rfl
  have ht : (shifted A u)⁻¹ = T (Matrix.diagonal fun j=> (f j)⁻¹) := Matrix.inv_eq_right_inv (by
    rw [hs,← map_mul,Matrix.diagonal_mul_diagonal]; simp [(hf _).ne'])
  rw [ht]
  change (V * Matrix.diagonal (fun j => (f j)⁻¹) * Vᴴ) i l = _
  rw [Matrix.mul_apply]; simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply, star_trivial, f,mul_right_comm]
lemma inv_cont (i j : I) : ContinuousOn (fun u : ℝ => (shifted A u)⁻¹ i j) (Ioi 0) := by
  let V := h.1.eigenvectorUnitary.val
  apply (ContinuousOn.congr (f:=fun u => ∑ l, V i l * V j l * (h.1.eigenvalues l+u)⁻¹) _
    (fun u hu => inv_entry h i j u (le_of_lt hu)))
  apply continuousOn_finsetSum; intro l _
  exact continuousOn_const.mul ((continuousOn_const.add continuousOn_id).inv₀
    (fun u hu=> by dsimp; linarith only [(show 0<u from hu),h.eigenvalues_pos l]))
lemma dose_entry (i : I) (u : ℝ) (hu : 0≤u) : dose A i u = ∑ j,(h.1.eigenvectorUnitary.val i j)^2 * clock (h.1.eigenvalues j) u := by
  let V := h.1.eigenvectorUnitary.val
  have hh : V*Vᴴ=1 := h.1.eigenvectorUnitary.prop.2
  have he := congr_arg (fun Q : Table I=> Q i i) hh
  change _ = ∑ j, V i j^2 * _
  simp_rw [clock,mul_sub,Finset.sum_sub_distrib, ← Finset.sum_mul, dose, inv_entry h i i u hu]
  have hf : ∑ j,V i j^2=1 := by simpa [Matrix.mul_apply,pow_two] using he
  rw [hf]; simp only [V,one_mul,pow_two]
lemma dose_int_aux (i : I) : IntegrableOn (dose A i) (Ioi 0) ∧
    ∫ u : ℝ in Ioi 0, dose A i u = ∑ j, h.1.eigenvectorUnitary.val i j ^2 * Real.log (h.1.eigenvalues j) := by
  let V := h.1.eigenvectorUnitary.val
  let d (j : I) := fun u => V i j ^2 * clock (h.1.eigenvalues j) u
  have he : (fun u => ∑ j,d j u) =ᵐ[volume.restrict (Ioi 0)] dose A i := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using (dose_entry h i u (le_of_lt hu)).symm
  have hi j : IntegrableOn (d j) (Ioi 0) := (cleared (h.eigenvalues_pos j)).1.const_mul _
  refine ⟨(integrable_finsetSum _ fun j _ => hi j).congr he,?_⟩
  rw [integral_congr_ae he.symm, integral_finsetSum _ (fun j _=>hi j)]
  simp_rw [d, integral_const_mul, (cleared (h.eigenvalues_pos _)).2]; rfl
lemma dose_price {η L : ℝ} (hη : 0<η) (he : η≤L) (hp : Numeric A η L) (i : I) :
    ∫ u : ℝ in Ioi 0, dose A i u = Panel.priceLine A L i := by
  rw [Panel.priceLine, (Panel.balance A h.1 hp hη he i).tsum_eq, add_sub_cancel, (dose_int_aux h i).2]
end YM.Further.CurvedGaussianJets.Line
