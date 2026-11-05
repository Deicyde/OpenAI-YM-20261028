import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Quadratic
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Mineral
import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization

/-!
# Tangentials for those two forecasts on dry probes

Initial aperture error compares the two FIRST-ORDER jets, bounded on real
δ schedules later. Both use true Hessian only at a flat reference. Carry θ,
Sources. Gram agreement does NOT imply mean agreement. Also still must price
perturbed cov-density score when used with field integrals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision
open Push.SectorMeasure.Oriented Scroll Vine Census
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

section Smooth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] {W : E→Matrix ι κ ℝ} {u : E → (ι → ℝ)}

abbrev meter (e : E→ κ → ℝ) (v:E) := fderiv ℝ e 0 v
abbrev Click (p : E→ Matrix ι κ ℝ) := ∀ i j, DifferentiableAt ℝ (fun e => p e i j) 0
omit [Fintype κ] in
lemma planes (h : Click W) (hu : DifferentiableAt ℝ u 0) :
    DifferentiableAt ℝ (fun x=> (W x)ᵀ*ᵥ u x) 0 := by
  refine differentiableAt_pi.mpr fun i=>?_
  unfold mulVec dotProduct
  exact DifferentiableAt.fun_sum (fun j _=> (h j i).mul (differentiableAt_pi.mp hu j))

lemma originD (h : Click W) (hu : DifferentiableAt ℝ u 0) (he : u 0=0) (v:E) :
    meter (fun x=> (W x)ᵀ*ᵥ u x) v = (W 0)ᵀ *ᵥ meter u v := by
  apply (Push.side _ (planes h hu) v).unique
  apply hasDerivAt_pi.mpr; intro i; unfold mulVec dotProduct
  refine HasDerivAt.fun_sum (fun j _=>?_)
  have hk := h j i
  have hd:= (Push.side _ (h j i) v).mul (hasDerivAt_pi.mp (Push.side u hu v) j)
  simp only [zero_smul,he,Pi.zero_apply,mul_zero,zero_add] at hd
  exact hd

lemma sideways (u : E→ι→ℝ) (hu : DifferentiableAt ℝ u 0) (q : ι) (v:E) :
    fderiv ℝ (fun x=> u x q) 0 v=meter u v q := (Push.side _ (differentiableAt_pi.mp hu q) v).unique (hasDerivAt_pi.mp (Push.side _ hu v) q)
end Smooth

section probe
variable (X : Coat T F) (h : P.Funds S T) {η r Q : ℝ} {m : ℕ}
variable (hW : Click (drills X))
  (hD : Click (mine X)) (hZ : DifferentiableAt ℝ (receipt X) 0)
  (hP : Click (looks X)) (hR : Click (rake X)) (hp : DifferentiableAt ℝ (paint X) 0)

include h
lemma ore_price (v : Directions G c) (hD : Click (mine X)) (hZ : DifferentiableAt ℝ (receipt X) 0) :
    meter (ore X) v = X.blank.form.transpose *ᵥ meter (receipt X) v := by
  have he : mine X 0=X.blank.form := by unfold mine gem dry; rw [Work.G07.at_zero_increment]; rfl
  rw [← he]; exact originD hD hZ (mute X h) v

include hD hZ
lemma matchesP (v : Directions G c) (hR : Click (rake X)) (hp : DifferentiableAt ℝ (paint X) 0) :
    (meter (ore X) v) ∘ tube X=meter (page X) v := by
  rw [show meter (ore X) v=_ from originD hD hZ (mute X h) v,show meter (page X) v=_ from originD hR hp (unpainted X h) v]
  funext i; let U (_ : Directions G c) := mine X 0; let V (_ : Directions G c):= rake X 0
  have hu : Click U:= fun _ _=>differentiableAt_const _; have hv : Click V := fun _ _=> differentiableAt_const _
  change ((U 0)ᵀ*ᵥ _) (tube X i)=((V 0)ᵀ*ᵥ _) i
  rw [← originD hu hZ (mute X h), ← originD hv hp (unpainted X h),← sideways _ (planes hu hZ),← sideways _ (planes hv hp)]
  simp_rw [U,V,scores X h]

lemma extractD (v : Directions G c) (e : Tubular f G) (hh : ¬X.blank.Hot e.1) : meter (ore X) v e=0 := by
  rw [ore_price X h v hD hZ]; simp only [Matrix.mulVec, Matrix.transpose_apply,dotProduct,X.blank.stays _ _ hh h,zero_mul,Finset.sum_const_zero]

include hW hP hR hp
lemma angle (v : Directions G c) :
    let A := forecast T X.x F X.k; let U := (drills X 0).submatrix (tube X) (tube X)
    meter (A-study X) v=(U-looks X 0)ᵀ *ᵥ meter (page X) v := by
  intro A U; let y:= meter (ore X) v
  have hv := planes hW (show DifferentiableAt ℝ (ore X) 0 from planes hD hZ); have hz : DifferentiableAt ℝ (source X) 0 := hv.neg
  have hu := planes hP (show DifferentiableAt ℝ (page X) 0 from planes hR hp)
  have hk : A=-(fun u => (looks X u)ᵀ *ᵥ page X u) := by funext u; exact neg_mulVec ..
  have hf : DifferentiableAt ℝ A 0 := hk.symm ▸ hu.neg
  have hb : DifferentiableAt ℝ (study X) 0 := differentiableAt_pi.mpr fun i=> differentiableAt_pi.mp hz (tube X i)
  have hA : meter A v = -((looks X 0)ᵀ *ᵥ meter (page X) v) := by
    unfold meter; rw [hk,fderiv_neg,_root_.neg_apply]; congr 1
    exact originD hP (planes hR hp) (bare_page X h) v
  have h₀ : meter (study X) v= -((drills X 0)ᵀ *ᵥ y) ∘ tube X := by
    funext i; rw [← sideways _ hb]; change fderiv ℝ (fun u=> source X u (tube X i)) 0 v= _
    rw [sideways _ hz]
    unfold meter; rw [show source X=-(fun u=>(drills X u)ᵀ *ᵥ ore X u) from rfl,fderiv_neg,
      _root_.neg_apply]; rw [show (fderiv ℝ _ 0 v)=_ from originD (u:=ore X) hW (planes hD hZ) (vacant X h) v]
    rfl
  have hh : ((drills X 0)ᵀ *ᵥ y) ∘ tube X=Uᵀ *ᵥ meter (page X) v := by
    rw [← matchesP X h hD hZ v hR hp]; funext i
    unfold Function.comp mulVec dotProduct; dsimp only; change ∑ j,(drills X 0) j _ * y j= ∑ j:Eye X,(drills X 0) (tube X j) _ * y _
    rw [← Finset.sum_map (f:=fun j=> (drills X 0) j (tube X i)*y j)]; symm; refine Finset.sum_subset (Finset.subset_univ _) ?_; intro j _ hj
    have he : ¬ X.blank.Hot j.1 := fun hh => hj (Finset.mem_map.mpr (by obtain ⟨u,h⟩ := spotlight X j hh; exact ⟨u,Finset.mem_univ _,h⟩))
    rw [show y j=0 from extractD X h hD hZ v j he,mul_zero]
  unfold meter; rw [fderiv_sub hf hb,_root_.sub_apply]; change meter A v-meter (study X) v=_; rw [hA,h₀]
  have heq : -((drills X 0)ᵀ *ᵥ y) ∘ tube X=-(((drills X 0)ᵀ *ᵥ y) ∘ tube X) := rfl
  rw [heq,hh,transpose_sub,sub_mulVec]; unfold meter; abel
end probe
end YM.PhysicalNext.Repeat.Malachite
