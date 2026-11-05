import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Ideal

/-!
# Zeroth-order Gaussian exchange with the ideal horizon-linked covariance

Only in Clear no-hole flat V geometry. Here even path uncutting part
pays (E radius/100000), include chart density switch receipts.
A_free is treeMatrix(S,H.metric), not H.inverse (two-forms). Do not
compute its inverse by separately arranging a gauge. Keep color det and
precision powers and all zero-mode components. center 0 of actual
sector too in these tests (even when some frozen coordinates? Clear
means none; enforce). Allow either Windows geometry. Uniform period at
fixed L. Report even *tag* uses by adjacent module, no transporting a
center paid on independent tags.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented Presented
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent Mark TestD Affine Window
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}
namespace Assembly

def idealFee (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (s C : ℝ) :=
  max 1 (stageCost G P K p 0 C s)

lemma priceQ (S : StepData c f) (p : Clip) (k : S.Choices) (F : Forest S.ratio) (W : PathData G) {s C Λ}
    (hS : Larger (G:=G) S) (h : W.Bounds p s C Λ) (hC : 0 ≤ C) (B : Bed) (he : Attached B W)
    (hh : (B.full p f).transpose * B.full p f=B.metric.acts f) (hb : Sworn B f G) :
    let a := footprint G S.patch S.kernel p 0 C s
    FreeResolvent.Gap (treeMatrix G S F B.metric) (headGap G S.patch S.kernel p) ∧
      (native c).Schur (theta S.ratio F) (theta S.ratio F) a (idealFee G S.patch S.kernel p s C)
        (treeMatrix G S F B.metric) ∧ (treeMatrix G S F B.metric).PosDef := by
  have hI : primary S F k p W Affine.all 0=treeMatrix G S F B.metric := Affine.identifies S F k hS.1 h he hh hb
  have hp := Affine.knows F k h.width hC (show Sheet W s C from h.rows) hS p 0 Affine.all
  intro a
  rw [← hI]
  refine ⟨hp.gap,hp.schur.mono (paid_size G S.patch S.kernel p (k:=0) h.width hC).2.2 (le_max_right ..),gap_positive ?_ hp.gap (headGap_pos ..)⟩
  unfold Affine.primary Affine.block; apply Matrix.IsSymm.submatrix; apply Matrix.IsSymm.smul
  unfold Matrix.IsSymm channel squareQ; simp [Matrix.transpose_sum]

structure FreePrice {Q C : Type} [Fintype Q] [DecidableEq Q] (D : Cost C) (p : Q→C)
    (M Y : Gaussian.Table Q) (s K e γ : ℝ) : Prop where
  prior : M.PosDef
  old : (mirror Y).PosDef
  pays : D.Schur p p s K M
  order : D.Schur p p s e (Y-M⁻¹)
  cov : D.Schur p p s e (mirror Y-M⁻¹)
  precision : D.Schur p p s (2*K^2*e) ((mirror Y)⁻¹-M)
  scalar : |Real.log ((mirror Y).det/(M⁻¹).det)| ≤ Fintype.card Q*(2*K*e)
  cluster : FreeResolvent.Gap (mirror Y) γ
  factor (z : Q → ℝ) :
    |Real.log (Density.replace (M⁻¹) (mirror Y) 0 z)| ≤ e*((Fintype.card Q:ℝ)*K + K^2*(z ⬝ᵥ z))

/-- Applies also when comparing any positive analytic ideal and supplied
small perturbation. For consumer on all fields NOT at flat, would need
pay the closeness to SAME uncut data, not *some* gauge patch's estimate!
Small ε sufficient; generic. -/
lemma fromCloseness {Q X : Type} [Fintype Q] [DecidableEq Q] {D : Cost X} {p : Q→X}
    {M Y : Gaussian.Table Q} {s K e η : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hm : M.PosDef) (hM : FreeResolvent.Gap M η) (hη : 0 < η) (hp : D.Schur p p s K M)
    (h : e ≤ η/(K+1)^2/2) (hd : K*e ≤ 1/2) (hQ : D.Schur p p s e (Y-M⁻¹)) :
    FreePrice D p M Y s K e (η/(K+1)^2/2) := by
  let C := mirror Y
  have hV : M⁻¹ |>.IsSymm := by
    unfold Matrix.IsSymm; rw [Matrix.transpose_nonsing_inv,(Matrix.isHermitian_iff_isSymm.mp hm.isHermitian).eq]
  have hx : D.Schur p p s e (C-M⁻¹) := by
    unfold C; rw [← mirror_symm_eq hV, ← mirror_sub]; exact mirrored hQ
  have H := flipped_gap hη hM hK (hp.mono hs le_rfl)
  have hc : FreeResolvent.Gap C (η/(K+1)^2/2) := (H.perturb (hx.mono hs le_rfl)).mono (by linarith)
  have ht : C.PosDef := gap_positive (mirror_symm _) hc (by positivity)
  have hr := reversePrice hs hK he hp hm ht hx hd
  have hh : 0 ≤ K*e := mul_nonneg hK he
  have hk : D.Schur p p s (K*e) (M*C-1) := by
    rw [show M*C-1=M*(C-M⁻¹) from (by rw [Matrix.mul_sub,M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp hm.isUnit)])]; exact hp.mul hx hs hK he
  have hL := log_payment hm ht hs hh hd hk
  have hl : |Real.log (C.det/(M⁻¹).det)| ≤ Fintype.card Q*(2*K*e) := by
    rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,div_inv_eq_mul, Real.log_mul ht.det_pos.ne' hm.det_pos.ne',mul_assoc 2]
    exact hL
  have hi : D.Schur p p s (2*K^2*e) (C⁻¹-M) := hr.mono le_rfl (by
    have hi : 0 ≤ K*e*K := by positivity
    calc
      _ = (1+2*(K*e))*(K*e*K) := by ring
      _ ≤ 2*(K*e*K) := by gcongr; linarith
      _ = _ := by ring)
  refine ⟨hm,ht,hp,hQ,hx,hi,hl,hc,?_⟩
  change ∀ z, |Real.log (Density.replace M⁻¹ C 0 z)| ≤ _
  intro z
  rw [Density.replace_income _ _ hm.inv ht,Density.spice,add_zero,force,force,Matrix.nonsing_inv_nonsing_inv _ (M.isUnit_iff_isUnit_det.mp hm.isUnit)]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2),← sub_div,← dotProduct_sub, ← Matrix.sub_mulVec, abs_div]
  refine (add_le_add (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤1/2)) (div_le_div_of_nonneg_right (schur_qf D p (hi.mono hs le_rfl) z) (abs_nonneg (2:ℝ)))).trans_eq ?_
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]; ring


/-- Purchase FreePrice on *retained* data. Receipt applies to either
actual window, after *same trees* and in-origin no-hole reindex. Ideal
kernel only at V=1, full. Does not implicitly include an `A_flat` claim
on determinant of a different user's Tube. -/
theorem freeHead (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) {s C : ℝ} (hs : 0<s) (hC : 0≤C) :
    ∃ α η E γ t : ℝ, 0<α ∧ 1≤E ∧ 0<γ ∧ 0<t ∧ 0<η ∧ ∀ᶠ x : ℝ in atTop,
      let e := E * Real.exp (-t * radiusB x)
      E*e ≤ 1/2 ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
        S.patch=P → S.kernel=K → Larger (G:=G) S → T.high=p → ∀ Λ, T.up.Bounds p s C Λ →
        ∀ (F : Forest S.ratio) (k : S.Choices) (U : Stores S) (g : Geometry) (h : Clear S x U F) (H : Bed),
        Attached H T.up → (H.full p f).transpose * H.full p f=H.metric.acts f → Sworn H f G →
          let r := opened G S x U F h
          let Q := treeMatrix G S F H.metric
          let Z := Rows.gram T x 1 k (shots S x) U F
          let W := pane (sectorW G S x U F g) Z 0
          FreeResolvent.Gap Q η ∧ FreePrice (native c) (theta _ F) Q (W.submatrix r r) α E e γ := by
  obtain ⟨t,Y,ht,hY,-,he⟩ := headComparison G P K p s C hs hC
  let a := footprint G P K p 0 C s
  let L := idealFee G P K p s C
  let E := max L Y
  have hL : 1 ≤ E := (le_max_left ..).trans (show L ≤ E from le_max_left ..)
  let m := headGap G P K p; let γ := m/(E+1)^2/2
  have hx : 0<a := (paid_size G P K p (k:=0) hs hC).1
  have hm : 0 < m := headGap_pos ..
  have hγ : 0 < γ := by unfold γ; positivity
  refine ⟨a,m,E,γ,t,hx,hL,hγ,ht,hm,?_⟩
  let e (x : ℝ) := E*Real.exp (-t*(radiusB x:ℕ))
  have hf : Tendsto e atTop (𝓝 0) := by
    have hr : Tendsto (fun x : ℝ => Real.exp (-t*(radiusB x))) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
      ((tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp Work.E01.radiusB_tendsto) |>.const_mul_atTop_of_neg (neg_lt_zero.mpr ht))
    simpa only [mul_zero,e] using! hr.const_mul E
  have hh : Tendsto (fun x : ℝ => E*e x) atTop (𝓝 0) := by simpa only [mul_zero] using! hf.const_mul E
  filter_upwards [he,hf.eventually (ge_mem_nhds hγ),hh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2))] with x hi h0 h1
  dsimp only
  refine ⟨h1,?_⟩; intro c f S T hP hK hS hp Λ hT F k U g h H hH hroot hsw
  obtain ⟨hr,-⟩ := hi 0 le_rfl S T hP hK hS hp Λ hT F k U g h H hH hroot hsw
  obtain ⟨hv,hE,hw⟩ := priceQ S p k F T.up hS hT hC H hH hroot hsw
  let Q:=treeMatrix G S F H.metric
  have hh : headGap G S.patch S.kernel p=m := by rw [hP,hK]
  rw [hh] at hv; rw [show footprint G S.patch S.kernel p 0 C s=a from (by rw [hP,hK]),show idealFee G S.patch S.kernel p s C=L from (by rw [hP,hK])] at hE
  refine ⟨hv,fromCloseness hx.le (zero_le_one.trans hL) (by have h : 0 < E := zero_lt_one.trans_le hL; positivity) hw hv hm (hE.mono le_rfl (le_max_left L Y)) h0 h1 ?_⟩
  have hf : treeInverse G S F H.metric 0=Q⁻¹ := by unfold treeInverse resolve; rw [zero_smul,add_zero]
  rw [hf] at hr; simp only [add_zero,inv_one,one_pow,mul_one] at hr
  exact hr.mono le_rfl (mul_le_mul_of_nonneg_right (le_max_right L Y) (Real.exp_pos _).le)
end Assembly
end YM.AnalyticBridge.LocalGaussianLaws
