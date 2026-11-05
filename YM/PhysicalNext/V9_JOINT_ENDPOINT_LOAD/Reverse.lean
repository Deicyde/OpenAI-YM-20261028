import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Supply
import YM.Progress.DIRECTED_RECIPE.Rollout
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Mosaic


/-!
# Arranging a comparison INTO the paid endpoint law

Need the OTHER direction to combine column-switch with the purchase of
loads on the ENDPOINT prescription. Mean likewise always from the selected
ordered columns, applied to the same blame. No moment of a whole physical
multiplier wrt an altered Gaussian for free; here compensate explicitly and
return the cost per changed column, via PHYSICAL_GAUSSIAN_SWITCH. Doesn't
redefine any of the likelihood factors or aperture licenses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Switch
open Function Filter Metric Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Push.SectorMeasure Wisps Schur Bid Matrix MeasureTheory
open SectorTools.PhysicalGaussianSwitch ColumnCosts Mosaic LocalLpWindows
open AnalyticBridge.GaussianFieldAlignment Relative
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius ENNReal

variable {I : Type} [Fintype I] [DecidableEq I] {c : Side} {p : I → Site c} {U V : Gaussian.Table I}
    {s K δ : ℝ}

private lemma turnabout (h : License U V p s K δ) (X : Finset I) (hδ : 2*K*δ ≤ 1/2) : License (hybrid U V X) U p s (2*K) δ := by
  have hc := h.change_cost X
  have hk := h.large
  have hQ := (h.positive X).posDef
  have hμ : 0 ≤ δ := hc.1.pos
  have ht : K + δ ≤ 2*K := by nlinarith
  refine ⟨?_,hQ,?_,TableCosts.inverse_perturb hQ h.pos h.lo hc.1 h.rate_pos h.afford,by linarith,h.rate_pos,hδ⟩
  · convert! TableCosts.pour_neg (TableCosts.columns_pour X h.coef) using 1; unfold hybrid; abel
  convert! (h.hi.bind hc.1).weaker le_rfl ht using 1; abel

omit [Fintype I] in
private lemma restored (U V : Gaussian.Table I) (X : Finset I) : hybrid (hybrid U V X) U X = U := by
  ext i j
  by_cases h : j∈X <;> simp [hybrid,TableCosts.columns,h]

structure Fare where
  M : ℝ
  s : ℝ
  C : ℝ
  paid : 0<M
  speed : 0<s
  bend : 0≤C


variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {d : Desk G S} {w : Fare}
    {A : Stores S} {F : Forest S.ratio} {Y : Config G c} {k : S.Choices} {x m : ℝ}

def Fare.value (w : Fare) (d : Desk G S) (p : ℝ) (n : ℕ) := sumPrice p (2*max 1 w.M) (decrease w.M w.s d.betaHat) d.g
  (w.C*(temp d.betaHat + d.radius)) n

structure Return (w : Fare) (p x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (Y : Config G c) (k : S.Choices) : Prop where
  reverse X : License (nextWin T A F x Y k X) (startWin T A F x Y k) (front A F) w.s (2*max 1 w.M) (decrease w.M w.s x)
  small : let K:=2*max 1 w.M; (2*K)*(2*p*(2*K^2*decrease w.M w.s x)) ≤ 1/4
  linear (q : Chi) (m : ℝ) (y : LinkArray G (Frozen A x F)) : 0 < m →
    ‖blame T x Y k (shots S x) A F q m y‖ ≤ w.C*(temp x + m)

theorem post (p : ℝ) (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G) :
    ∃ w : Fare, ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
      Larger (G:=G) S → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ A F Y k, A.flags=RG.flags (temp x) Y →
        Return w p x T A F Y k := by
  obtain ⟨s,η,M,D,hs,-,hM,-,hA⟩ := AnalyticBridge.GaussianFieldAlignment.purchase Pt P h
  obtain ⟨C,hC,hB⟩ := Bias.sources_read P Pt h
  refine ⟨⟨M,s,C,hM,hs,hC⟩,?_⟩
  let K := max 1 M
  have hk : 1 ≤ K := le_max_left ..
  have he : M ≤ 2*K := by have hh : M≤K := le_max_right ..; linarith
  have hl : max 1 (2*K)=2*K := max_eq_right (by linarith)
  filter_upwards [hA,hB,aft p s M hs, aft (max p 1) s (2*K) hs] with x hA hB hδ h'
  have hu : decrease M s x ≤ decrease (2*K) s x := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le) zero_le_two
  obtain ⟨hh,h'⟩ := h'
  rw [hl] at hh h'
  intro c f S T hP hL hS hT A F Y k hY
  refine ⟨fun X => ?_,?_ ,hB S T hP hS hT A F k Y hY⟩
  · rw [nextWin,mosaic]
    exact turnabout (cash T A F x Y k (hA _ _ S T hP hL hS hT A F k Y (Or.inl hY)) hs hδ.1) X
      ((mul_le_mul_of_nonneg_left hu (by linarith)).trans hh)
  apply le_trans ?_ h'
  change (2*(2*K))*(2*p*(2*(2*K)^2*decrease M s x)) ≤ _
  have h2 : 0 ≤ decrease M s x := by unfold decrease; positivity
  gcongr
  exact le_max_left ..

namespace Return
variable (h : Return w m d.betaHat d.tube A F Y k) (hm : 1 < m) (hβ : 0<d.input.beta) (hr : 0<d.radius)
include h hm hβ hr
/-- Holder from the altered columns, RHS on precisely the paid law for hK. -/
theorem reads (X : Finset (In (G:=G) d.betaHat A F)) (y : LinkArray G (Frozen A d.betaHat F)) (f : Prices G (Active A d.betaHat F) → ℝ) :
    let x := d.betaHat; let g := d.g; let orig := fog A F d.tube x Y k; let fresh := covNew d.tube A F x Y k X
    let μ := meanLog A F d.tube x Y k d.broadCut d.radius y; let ν := centerNew d.tube A F x Y k d.broadCut d.radius X y
    let q := Real.conjExponent m; let Fz z := f (μ+g • z); let Fy z := f (ν+g • z)
    (mixed fresh orig m).PosDef ∧ price fresh orig m (g⁻¹ • (μ-ν)) ≤ w.value d m X.card ∧
      (MemLp Fz (ENNReal.ofReal q) (Gaussian.cloud orig) →
      Integrable Fy (Gaussian.cloud fresh) ∧ ‖∫ z,Fy z∂Gaussian.cloud fresh‖ ≤
        w.value d m X.card ^ (1/m) * (∫ z, ‖Fz z‖ ^ q ∂Gaussian.cloud orig) ^ (1/q)) := by
  intro x g orig fresh μ ν q Fz Fy
  let T := d.tube; let b := blame T x Y k (shots S x) A F d.broadCut d.radius y
  let U := startWin T A F x Y k; let W := nextWin T A F x Y k X
  have he : hybrid W U X=U := by unfold W nextWin U; rw [mosaic]; exact restored ..
  have hg : 0<g := coupling_pos hβ
  have hb := h.linear d.broadCut d.radius y hr
  have hc := ColumnCosts.paid (h.reverse X) hm.le h.small X hg b hb
  have hC := normalized (h.reverse X) hm h.small X hg b hb f
  dsimp only at hC hc; unfold ColumnCosts.delta at hc
  change (mixed (symPart W) (symPart (hybrid W U X)) m).PosDef ∧ price _ _ m (g⁻¹ • (mean (hybrid W U X) b-mean W b)) ≤ _ at hc
  rw [he] at hc
  simp_rw [show hybrid (nextWin d.tube A F d.betaHat Y k X) (startWin d.tube A F d.betaHat Y k) X=_ from he] at hC
  exact ⟨hc.1,hc.2,hC⟩
end Return
end YM.PhysicalNext.JointLoad.Switch
