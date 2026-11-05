import YM.Further.GAUSSIAN_SCALAR_LEDGER.Rates
import YM.SectorNext.VACUUM_NORMALIZATION.Etch

set_option warningAsError false

/-!
# Reconcile the two local scalar prices

Use u∈Ioi 0 (real Lebesgue). Show `Panel.priceLine` (incl its
summability qualification) equals the diagonal resolvent integral,
not merely that the traces agree. No Bochner logs on an implicit
boundary or term-by-term subtraction of separately divergent integrals.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice Unitary
open Lens (plus full)
open Round (rowRate)
open MeasureTheory Set
open YM.Progress.StationaryScenes.Green
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma lineCost {l : ℝ} (h : 0 < l) :
    let f := fun u : ℝ => (1+u)⁻¹-(l+u)⁻¹
    IntegrableOn f (Ioi 0) ∧ (∫ u in Ioi (0:ℝ), f u) = Real.log l := by
  intro f
  let g (u : ℝ) := Real.log (1+u) - Real.log (l+u)
  have hd : ∀ x ∈ Ici (0:ℝ), HasDerivAt g (f x) x := by
    intro x hx
    have hu : 0≤x := hx
    simpa [one_div,f] using! ((((hasDerivAt_id' x).const_add 1).log (show 1+x≠0 by positivity)).sub
      (((hasDerivAt_id' x).const_add l).log (show l+x≠0 by positivity)))
  have he : Tendsto g atTop (𝓝 0) := by
    have hm : Tendsto (fun u : ℝ => l+u) atTop atTop := by
      simpa [add_comm] using (tendsto_id (x:= (atTop:Filter ℝ))).atTop_add (g:=fun _ : ℝ => l) tendsto_const_nhds
    have hw := hm.inv_tendsto_atTop
    have ht : Tendsto (fun u : ℝ => (1-l)*(l+u)⁻¹+1) atTop (𝓝 1) := by
      simpa using (hw.const_mul (1-l)).add_const 1
    have hx : Tendsto (fun u : ℝ => (1+u)/(l+u)) atTop (𝓝 1) := by
      refine ht.congr' ?_; filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; field_simp; ring
    apply (show Tendsto (fun u : ℝ => Real.log ((1+u)/(l+u))) atTop (𝓝 0) by
      simpa using hx.log (by norm_num)).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact Real.log_div (by positivity) (by positivity)
  have hi : IntegrableOn f (Ioi (0:ℝ)) := by
    by_cases hp : 1 ≤ l
    · refine integrableOn_Ioi_deriv_of_nonneg' hd (fun x hx => ?_) he
      have hb : 0 < x := hx
      exact sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith : 1+x≤l+x))
    refine integrableOn_Ioi_deriv_of_nonpos' hd (fun x hx => ?_) he
    have hb : 0 < x := hx
    exact sub_nonpos.mpr (inv_anti₀ (by positivity) (by linarith : l+x≤1+x))
  exact ⟨hi,(integral_Ioi_of_hasDerivAt_of_tendsto' hd hi he).trans (by simp [g])⟩

def pulse (A : Wall ι) (i : ι) (u : ℝ) :=
    (1+u)⁻¹-full A u i i

variable {A : Wall ι} (h : A.PosDef)

lemma tilted_entry (i j : ι) {u : ℝ} (hu : 0≤u) :
    let V := h.1.eigenvectorUnitary.val
    full A u i j = ∑ k,(V i k * (h.1.eigenvalues k+u)⁻¹)*V j k := by
  intro V
  let T := conjStarAlgAut ℝ _ h.1.eigenvectorUnitary
  let g (k : ι) := h.1.eigenvalues k+u
  have hG k : 0 < g k := add_pos_of_pos_of_nonneg (h.eigenvalues_pos _) hu
  have hv : A=T (diagonal fun i => h.1.eigenvalues i) := h.1.spectral_theorem
  have hb : plus A u=T (diagonal g) := by
    unfold plus; rw [show diagonal g=diagonal (fun i => h.1.eigenvalues i)+u • 1 from ?_,map_add, map_smul,map_one,← hv]
    ext i j; by_cases hx : i=j <;> simp [g,hx,Matrix.diagonal]
  let d := diagonal (fun i => (g i)⁻¹)
  have hx : plus A u*T d=1 := by
    rw [hb, ←map_mul]
    rw [show diagonal g*d=1 from ?_,map_one]
    unfold d; rw [diagonal_mul_diagonal]; simp [((hG _).ne')]
  have hl : full A u=T d := by
    have hm := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Lens.plus_pos h hu).det_pos.ne')
    unfold full; rw [←mul_one (plus A u)⁻¹,← hx,←mul_assoc,hm,one_mul]
  rw [hl, show T d=V*d*Vᴴ from rfl, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro k _
  unfold d; rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply,star_trivial]

include h
lemma full_stable (i j : ι) : ContinuousOn (fun u => full A u i j) (Ioi (0:ℝ)) := by
  have he k : ContinuousOn (fun u : ℝ => (h.1.eigenvalues k+u)⁻¹) (Ioi 0) :=
    (continuousOn_const.add continuousOn_id).inv₀ fun u hu => (show 0 < h.1.eigenvalues k+u from
      add_pos (h.eigenvalues_pos _) hu).ne'
  have ht : EqOn (fun u => full A u i j) _ (Ioi (0:ℝ)) := fun u hu => tilted_entry h i j (mem_Ioi.mp hu).le
  exact (continuousOn_finsetSum _ fun k _ => (continuousOn_const.mul (he k)).mul continuousOn_const).congr ht

private lemma row_sq (i : ι) : ∑ j, (h.1.eigenvectorUnitary.val i j)^2=1 := by
  let V := h.1.eigenvectorUnitary
  have hl : V.val * V.valᴴ=1 := V.prop.2
  simpa [Matrix.mul_apply,pow_two,V] using congr_arg (fun Q : Wall ι => Q i i) hl

lemma settled {η L : ℝ} (f : Numeric A η L) (hp : 0 < η) (hb : η≤L) (i : ι) :
    IntegrableOn (pulse A i) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), pulse A i u) = Panel.priceLine A L i := by
  let a := h.1.eigenvectorUnitary.val
  let w k := a i k ^ 2
  let v k := h.1.eigenvalues k
  let F k (u : ℝ) := w k * ((1+u)⁻¹-(v k+u)⁻¹)
  have he : EqOn (fun u => pulse A i u) (fun u => ∑ k, F k u) (Ioi 0) := by
    intro u hu
    dsimp only [pulse]
    rw [tilted_entry h i i hu.out.le]
    change (1+u)⁻¹-∑ k,a i k*(v k+u)⁻¹*a i k = _
    calc
      _ = (∑ k, w k * (1+u)⁻¹) - (∑ k,w k*(v k+u)⁻¹) := by
        rw [← Finset.sum_mul,show ∑ k,w k=1 from row_sq h i,one_mul]
        congr 1; apply Finset.sum_congr rfl; intro k _; unfold w; ring
      _ = _ := by unfold F; simp only [mul_sub,Finset.sum_sub_distrib]
  have hf (k : ι) := lineCost (show 0<v k from h.eigenvalues_pos _)
  have hl k : IntegrableOn (F k) (Ioi (0:ℝ)) := (hf k).1.const_mul _
  refine ⟨(integrableOn_congr_fun he measurableSet_Ioi).mpr (integrable_finsetSum _ (fun k _ => hl k)),?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_finsetSum _ fun k _ => hl k]
  have hx (k : ι) : (∫ u in Ioi (0:ℝ), F k u) = w k * Real.log (v k) := by
    unfold F; rw [integral_const_mul,(hf k).2]
  simp_rw [hx]
  unfold Panel.priceLine
  rw [(Panel.balance A h.1 f hp hb i).tsum_eq]; unfold w v a; abel

omit h in
lemma kernel_budget :
    IntegrableOn (fun x : ℝ => (1+x)⁻¹^2) (Ioi 0) ∧ (∫ x in Ioi (0:ℝ), (1+x)⁻¹^2)=1 := by
  let g (u : ℝ) := -((1+u)⁻¹)
  have he : ∀ x ∈ Ici (0:ℝ), HasDerivAt g ((1+x)⁻¹^2) x := by
    intro x hx
    have hm : 0≤x := hx
    simpa only [neg_div,neg_neg,one_div, inv_pow] using! (((hasDerivAt_id' x).const_add 1).inv (show 1+x≠0 by positivity)).neg
  have hp : Tendsto g atTop (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => 1+u) atTop atTop := by
      simpa [add_comm] using (tendsto_id (x:= (atTop:Filter ℝ))).atTop_add (g:=fun _ : ℝ => 1) tendsto_const_nhds
    simpa only [g,neg_zero] using! h.inv_tendsto_atTop.neg
  have hu := integrableOn_Ioi_deriv_of_nonneg' he (fun i _ => sq_nonneg _) hp
  exact ⟨hu,(integral_Ioi_of_hasDerivAt_of_tendsto' he hu hp).trans (by simp [g])⟩

end YM.Further.GaussianScalar
