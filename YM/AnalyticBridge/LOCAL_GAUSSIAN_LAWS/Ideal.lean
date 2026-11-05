import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Taylor

/-!
# Same retained free kernel: exponential error (fixed L)

Link `total` and `.Closes`-like receipts on chosen horizon H proper
through `Attached`. No error from losing harmonic/zero modes. Note the
difference prices at order zero here DON'T assume ε-affordability of
the ideal precision $H$ across V fields. They are from exact matching
at B=0 and the same Path.Bounds. Even ideal A_I has fixed-L gap simply
from the path data and Branches + geometry (FR directGap, there is no
pole at periodic zero here), and price; inverse alignment at this head.
No promise from the type of any retained horizon on its own: choose and
use it with the *same* T to read remaining data. Buying back smaller
powers after cuts does not buy free estimates across entering stages.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented Presented
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent Mark TestD Affine Window
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side}
namespace Assembly

/-- Absorb fixed integer radii, don't pretend continuous radius
conversions without an eventual clause. Include `(1+u)^{-2}`. -/
def expenses (k b r : ℕ) (s γ V M H T u : ℝ) :=
    let C0 := T * drain u
    let N := Real.exp (-(s/4)*(r:ℕ))*(2*tagPrice 1 k H H)
    TestD.patchFee γ ((b/60:ℕ):ℝ) M 1 V C0 k + tagPrice 1 k (tagPrice 1 k C0 N) C0

lemma diminishing (k : ℕ) (s γ V M H T : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hv : 0 ≤ V)
    (hm : 0 ≤ M) (_hH : 0≤H) (_ht : 0 ≤ T) :
    ∃ t C : ℝ, 0<t ∧ 0<C ∧ t≤γ ∧ ∀ b : ℕ, 200000 ≤ b → ∀ u : ℝ, 0 ≤ u →
      expenses k b (b/100000) s γ V M H T u ≤ C*Real.exp (-t*b)*((1+u)⁻¹)^2 := by
  let t := min (γ/120) (s/800000)
  have hx : 0 < t := lt_min (by positivity) (by positivity)
  let B₁ := (2:ℝ)^(2*k)*T^2*(V*M)
  let B₂ := (2:ℝ)^(3*k)*T^2*(2*H^2)
  refine ⟨t,B₁+B₂+1,hx,by unfold B₁ B₂; positivity,(min_le_left ..).trans (by linarith),?_⟩
  intro b hb u hu
  have hh : b ≤ 120*(b/60) := by omega
  have h : b ≤ 200000*(b/100000) := by omega
  let A := Real.exp (-((k+1:ℕ):ℝ)*γ*(b/60:ℕ))
  let B := Real.exp (-(s/4)*(b/100000:ℕ))
  let Q := Real.exp (-t*b)
  have hA : A ≤ Q := by
    apply Real.exp_monotone
    have hk : t ≤ γ/120 := min_le_left ..
    have hh : (b:ℝ) ≤ 120*(b/60:ℕ) := by exact_mod_cast hh
    push_cast
    have hi : 0 ≤ (k:ℝ)*γ*(b/60:ℕ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hh hx.le]
  have hB : B ≤ Q := by
    apply Real.exp_monotone
    have hk : t ≤ s/800000 := min_le_right ..
    have hh : (b:ℝ) ≤ 200000*(b/100000:ℕ) := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left hh hx.le]
  have hQ := (Real.exp_pos (-t*b)).le
  unfold expenses TestD.patchFee tagPrice; simp only [one_pow,one_mul]
  calc
    _ = (A * B₁ + B * B₂)*((1+u)⁻¹)^2 := by unfold A B₁ B B₂ drain; ring
    _ ≤ (Q*B₁+Q*B₂)*_ := by gcongr
    _ ≤ _ := by apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); unfold Q; nlinarith only [hQ]

/-- `total` in simple analytical currency. Includes all repeated
spatial marks (not the *sum-over*-marks stronger convention; use Stars
version for that at another rate). Retain the original larger mark γ;
comparison on fixed test lists in that ker may subsequently shrink it.
Derivative order and path charge & stage width are fixed data. -/
theorem fieldComparison (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (s J : ℝ) (n : ℕ) (hs : 0 < s) (hJ : 0 ≤ J) :
    let γ := footprint G P K p n J s
    ∃ t C : ℝ, 0<t ∧ 0<C ∧ t≤γ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ u : ℝ, 0 ≤ u → ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
        S.patch=P → S.kernel=K → Larger (G:=G) S → T.high=p → ∀ Λ, T.up.Bounds p s J Λ →
        ∀ (F : Forest S.ratio) (k : S.Choices) (U : Stores S) (g : Geometry) (h : Clear S x U F),
          let e := opened G S x U F h
          let Q (B : Coarse G c) := Rows.gram T x (enroll B) k (shots S x) U F
          let Ordered B := (pane (sectorW G S x U F g) (Q B) u).submatrix e e
          let I B := resolve (Affine.primary S F k T.high T.up Affine.all B) u
          let tC := C*Real.exp (-t*radiusB x)*((1+u)⁻¹)^2
          Bundle (ray G c) (marks G c γ) (native c) (theta _ F) (theta _ F) (fun B => Ordered B-I B) 0 n γ tC ∧
            Bundle (ray G c) (marks G c γ) (native c) (theta _ F) (theta _ F) (fun B => mirror (Ordered B)-I B) 0 n γ tC := by
  intro γ
  let V := load G P K p n J s
  let M := stageCost G P K p n J s
  let H := phasePrice G P K n J s
  let T := meter n n M 1 (rise V (headGap G P K p))
  have h := situate G P K p (k:=n) hs hJ
  obtain ⟨t,C,ht,hC,hγ,hF⟩ := diminishing n s γ V M H T hs h.pos h.vol (stage_nn G P K p hs hJ) (phase_nn G P K hs hJ) h.meter_abs
  refine ⟨t,2*C,ht,by positivity,hγ,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 200000] with x hx
  intro u hu c f S T' he hh hp hL Λ hH F k U g hS E Q O I tC
  rw [← hL] at hH
  obtain ⟨h₁,h₂⟩ := total S T' x k U F g hp hH hJ n u hu hS (by omega)
  -- in cost only, cannot rewrite the actual fields
  let b := radiusB x
  have hw : footprint G S.patch S.kernel T'.high n J s=γ := by rw [he,hh,hL]
  let V' := load G S.patch S.kernel T'.high n J s; let M' := stageCost G S.patch S.kernel T'.high n J s
  let H' := phasePrice G S.patch S.kernel n J s; let T₀ := meter n n M' 1 (rise V' (headGap G S.patch S.kernel T'.high))
  have hv : (expenses n b (till x) s (footprint G S.patch S.kernel T'.high n J s) V' M' H' T₀ u) ≤ C*Real.exp (-t*b)*((1+u)⁻¹)^2 := by
    unfold H' T₀ V' M'
    rw [he,hh,hL]; exact hF b hx u hu
  rw [← hw]
  let a := ((1+u)⁻¹)^2
  let e := Real.exp (-t*b)
  have he : 0 ≤ C*e*a := by unfold e a; positivity
  have h' : tC = 2*(C*e*a) := by unfold tC e a b; ring
  rw [h']
  refine ⟨h₁.mono le_rfl (hv.trans (by linarith)),h₂.mono le_rfl (mul_le_mul_of_nonneg_left hv (by norm_num))⟩

/-- Immediate physical-client correspondence to the actual free
Horizon-linked inverse. No requirement on same-gauge Tours geometry of
other periods. A positive exponent s' for measurement with Cost.Schur
(even full inverse at u=0), chosen before period/beta, post-L. -/
theorem headComparison (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (s J : ℝ) (hs : 0<s) (hJ : 0≤J) :
    let s' := footprint G P K p 0 J s
    ∃ t C : ℝ, 0<t ∧ 0<C ∧ t≤s' ∧ ∀ᶠ x : ℝ in atTop,
      ∀ u : ℝ, 0≤u → ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
        S.patch=P → S.kernel=K → Larger (G:=G) S → T.high=p → ∀ Λ, T.up.Bounds p s J Λ →
        ∀ (F : Forest S.ratio) (k : S.Choices) (U : Stores S) (g : Geometry) (h : Clear S x U F) (H : Bed),
        Attached H T.up → (H.full p f).transpose * H.full p f=H.metric.acts f → Sworn H f G →
          let e := opened G S x U F h
          let Q := Rows.gram T x 1 k (shots S x) U F
          let O := (pane (sectorW G S x U F g) Q u).submatrix e e
          (native c).Schur (theta _ F) (theta _ F) s' (C*Real.exp (-t*radiusB x)*((1+u)⁻¹)^2) (O-treeInverse G S F H.metric u) ∧
            (native c).Schur (theta _ F) (theta _ F) s' (C*Real.exp (-t*radiusB x)*((1+u)⁻¹)^2) (mirror O-treeInverse G S F H.metric u) := by
  intro s'
  obtain ⟨t,C,ht,hC,h,e⟩ := fieldComparison G P K p s J 0 hs hJ
  refine ⟨t,C,ht,hC,h,?_⟩
  filter_upwards [e] with x he
  intro u hu c f S T h1 h2 hh hp Λ hv F k U g hx H ha hq hS E Q O
  obtain ⟨h',h''⟩ := he u hu S T h1 h2 hh hp Λ hv F k U g hx
  have ht := (h'.bound [] (by simp)).reclaim
  have hD := (h''.bound [] (by simp)).reclaim
  simp only [TestD.zeroth] at ht hD
  have hg : enroll (0:Coarse G c) = 1 := Precision.link_one
  have H' : resolve (Affine.primary S F k T.high T.up Affine.all 0) u=treeInverse G S F H.metric u := by
    unfold Affine.all; rw [hp, Affine.identifies S F k hh.1 hv ha hq hS]; rfl
  rw [H',hg] at ht hD; exact ⟨ht,hD⟩
end Assembly
end YM.AnalyticBridge.LocalGaussianLaws
