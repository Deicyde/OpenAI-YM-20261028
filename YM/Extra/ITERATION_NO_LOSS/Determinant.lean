import YM.Extra.ITERATION_NO_LOSS.Calibration
import YM.Extra.ITERATION_NO_LOSS.Roots
import YM.Work.F04.Choices
import YM.Work.F05

/-! Germ splitting for the fresh (pure determinant/Haar) calculation in RLoops. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Calibration
open Filter Function Lattice Wilson RG Exterior Precision Tree Bloch Bid Matrix Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {n c f : Side} {S : StepData c f}

def determinant (H : Forest S.ratio) (a : S.Choices) (R : PathData G) (p : Clip)
    (ρ : Dir G c → AxisChart G H) (O : ChartRatio G) (x : Dir G c) := (1/2:ℝ)*Real.log (hessian H a p R x (ρ x)).det -
        Real.log (∏ i : H.Free, O.J (ρ x i))

def errorBound (ρ σ : Dir G c → ℝ) (Θ γ Λ : ℝ) := ∀ (i j : Site c) (e f : TypeFace 1 → G.ColorIndex → ℂ),
      (∀ x y, ‖e x y‖ ≤ 1) → (∀ x y, ‖f x y‖ ≤ 1) →
      |jet 2 ρ ![wave i e,wave j f] - jet 2 σ ![wave i e,wave j f]| ≤
        (Fintype.card (Site c):ℝ)*Θ*Λ*Real.exp (-γ*c.val)

def FreshDet (H : Forest S.ratio) (a : S.Choices) (R T : PathData G) (p q : Clip) (ρ : Dir G c → AxisChart G H)
    (O : ChartRatio G) (α Θ γ : ℝ) := errorBound (determinant H a R p ρ O) (draft α T q) Θ γ 1

lemma determinant_jet {H : Forest S.ratio} {p R ρ η} (he : 0 < η) (h : PriceGap H p R η) (hr : Critical H p R ρ)
    (a : S.Choices) {O : ChartRatio G} (hO : LocalRatio O) : ContDiffAt ℝ ω (determinant H a R p ρ O) 0 := by
  unfold determinant
  have hd := Work.F05.curve_partial (F:= fun x => fderiv ℝ (tested H a p R x)) (Work.F05.curve_partial (hr.2.2 a).1)
  have hj : ContDiffAt ℝ ω (fun x => (hessian H a p R x (ρ x)).det) 0 := by
    simp_rw [det_apply]
    apply ContDiffAt.sum; intro i _
    simp_rw [Units.smul_def, zsmul_eq_mul]
    refine ContDiffAt.mul contDiffAt_const (contDiffAt_prod fun j _ => ?_)
    have ht : ContDiffAt ℝ ω (fun x => fderiv ℝ (fderiv ℝ (tested H a p R x)) (ρ x)) 0 :=
      (show ContDiffAt ℝ ω (uncurry fun x => fderiv ℝ (fderiv ℝ (tested H a p R x))) ((0:Dir G c), ρ 0) from (by rw [hr.1]; exact hd)).comp
        (f:=fun x : Dir G c => (x,ρ x)) 0 (graph_jet _ hr.2.1)
    simp only [hessian, of_apply,iteratedFDeriv_two_apply, Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    exact (ht.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  refine (contDiffAt_const.mul (Real.contDiffAt_log.mpr (mem_of_mem_nhds (Work.F05.hessian_pos he h hr a)).ne' |>.comp _ hj)).sub ?_
  have ht : ContDiffAt ℝ ω (fun x => ∏ i : H.Free,O.J (ρ x i)) 0 := contDiffAt_prod fun i _ => by
    refine ContDiffAt.comp (f:=fun x => ρ x i) 0 ?_ ((contDiffAt_pi.mp hr.2.1) i)
    rw [hr.1,Pi.zero_apply]; exact hO.germ _ (Metric.mem_ball_self hO.patch)
  exact (Real.contDiffAt_log.mpr (by simp [hr.1,hO.anchored])).comp 0 ht

lemma thermal_jet {H : Forest S.ratio} {p R ρ η σ C Λ} (he : 0 < η) (h : PriceGap H p R η) (hr : Critical H p R ρ)
    (a : S.Choices) {O : ChartRatio G} (hO : LocalRatio O) (hp : R.Bounds p σ C Λ) : ContDiffAt ℝ ω (thermal H a p R ρ O) 0 := by
  rw [show thermal H a p R ρ O = aged R.loop H ρ + determinant H a R p ρ O by ext1; simp only [thermal,determinant,aged,liftedTo,Pi.add_apply]; unfold action Precision.loop; abel]
  exact (action_smooth hp.width hp.two (liftedTo_smooth _ hr.2.1 hr.1)).add (determinant_jet he h hr a hO)

lemma determinant_price {H : Forest S.ratio} {p ρ η Λ} (R : PathData G) (he : 0 < η) (h : PriceGap H p R η)
    (hr : Critical H p R ρ) (a : S.Choices) {O : ChartRatio G} (hO : LocalRatio O)
    (Q : Bed) (three four old fresh) {q σ' C' Λ'} (hq : (bundle Q three four (join fresh old)).Bounds q σ' C' Λ')
    {B D} (hF : Charged fresh σ' B) (hD : Charged old σ' D) {α γ Θ : ℝ} (hΘ : 0 ≤ Θ) (hΛ : 1 ≤ Λ)
    (hh : FreshDet H a R (bundle Q three four fresh) p q ρ O α Θ γ)
    (hT : SameJet 2 (aged R.loop H ρ) (acted old)) :
    errorBound (thermal H a p R ρ O) (draft α (bundle Q three four (join fresh old)) q) Θ γ Λ := by
  have ht : thermal H a p R ρ O = determinant H a R p ρ O + aged R.loop H ρ := by
    funext x; unfold thermal determinant; simp only [Pi.add_apply]; unfold aged action liftedTo Precision.loop; abel
  let Z := bundle Q three four (join fresh old)
  let y := bundle Q three four fresh
  have hu : draft (c:=c) α Z q = draft α y q + acted old := by
    ext x; change α*secondTerm q Z (represent x) + action (join fresh old) (represent x) = _
    rw [action_join hq.width hF hD _, ← add_assoc]; rfl
  have hdraft : ContDiffAt ℝ ω (fun x : Dir G c => α * core Z q x + acted fresh x) 0 := ((contDiffAt_const (c:=α)).mul (core_jet hq)).add
    (acted_jet _ hq.width hF)
  change ContDiffAt ℝ ω (draft (c:=c) α y q) 0 at hdraft
  intro i j e f he hf
  rw [ht, jet_add _ (determinant_jet ‹0 < η› h hr a hO) hT.1, hu, jet_add _ hdraft (acted_jet _ hq.width hD),
    show jet 2 (aged R.loop H ρ)=_ from hT.2.2,_root_.add_apply,_root_.add_apply,add_sub_add_right_eq_sub]
  exact (hh i j e f he hf).trans (by gcongr)

lemma tag_thermal {H : Forest S.ratio} {p R ρ} (h : S.patch.Branches S.kernel G) (hr : Critical H p R ρ)
    (O : ChartRatio G) (a b : S.Choices) : thermal H a p R ρ O =ᶠ[𝓝 0] thermal H b p R ρ O := by
  filter_upwards [(Work.F05.crit_home hr).eventually (eventually_eventually_nhds.mpr (Work.F04.tested_germ h H p R a b))] with x hx
  have hz : tested H a p R x =ᶠ[𝓝 (ρ x)] tested H b p R x := Work.F05.hold_near (V:=fun z => uncurry (tested H a p R) z=uncurry (tested H b p R) z) hx
  simp only [thermal,hessian,(hz.iteratedFDeriv ℝ 2).self_of_nhds]

lemma all_forests {H F : Forest S.ratio} {R T : PathData G} {p q ρ u σ C Λ σ' C' Λ' η} (hL : Larger (G:=G) S) {O : ChartRatio G}
    (hO : LocalRatio O) (hr : Critical H p R ρ) (hu : Critical F p R u) (hp : R.Bounds p σ C Λ) (hq : T.Bounds q σ' C' Λ')
    (he : 0 < η) (hH : PriceGap H p R η) (hF : PriceGap F p R η) (t : S.Choices)
    (ht : ∀ j, j≤4 → SameJet j (actual H t p R ρ) (main T q)) : ClassicalMatch F p q R T u := by
  intro j hj a
  have heq := (YM.Work.F05.answer G c f S ?_ F H p R σ C Λ η η u ρ hp hu hr he he hF hH O hO a).1
  · have ht' : actual H a p R ρ =ᶠ[𝓝 0] actual H t p R ρ := (Work.F05.crit_home hr).eventually (Work.F04.tested_germ hL.1 H p R a t)
    have hd := heq.trans ht'
    exact ⟨actual_jet hu _,main_jet hq,(hd.iteratedFDeriv ℝ _ |>.self_of_nhds).trans ((ht _ hj).2.2)⟩
  exact hL

lemma transplant {H F : Forest S.ratio} {p q R T ρ u σ C Λ σ' C' Λ' α Θ γ η} (h : S.patch.Branches S.kernel G) {O : ChartRatio G}
    (hL : Larger (G:=G) S) (hO : LocalRatio O) (hr : Critical H p R ρ) (hu : Critical F p R u) (hp : R.Bounds p σ C Λ) (hq : T.Bounds q σ' C' Λ')
    (he : 0 < η) (hH : PriceGap H p R η) (hF : PriceGap F p R η) (t : S.Choices)
    (hw : errorBound (thermal H t p R ρ O) (draft α T q) Θ γ Λ) (ht : ∀ j, j≤4 → SameJet j (actual H t p R ρ) (main T q)) :
    FiniteBound F R T p q α O u Θ γ Λ ∧ ClassicalMatch F p q R T u := by
  constructor
  · refine ⟨Work.F05.hessian_pos he hF hu, fun a => thermal_jet he hF hu a hO hp,
      ((contDiffAt_const (c:=α)).mul (core_jet hq)).add (acted_jet _ hq.width hq.two),?_⟩
    intro a i j s v hs hv W
    have heq := (tag_thermal h hu O a t).trans (Work.F05.same_thermal h hp hu hr he hH hO t)
    rw [(heq.iteratedFDeriv ℝ _).self_of_nhds]
    exact hw i j s v hs hv
  exact all_forests hL hO hr hu hp hq he hH hF t ht
end YM.Extra.Iteration.Calibration
