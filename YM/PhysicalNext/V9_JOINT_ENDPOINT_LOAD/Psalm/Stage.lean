import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Refit

/-! # One schedule investing in Sounded/Gliss together with Sweep etc
No rechoose of incompatible collars, widths or threshold at a test. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Stage
open Function Filter Set Lattice RG Wilson Pressure Tree Precision Bid Exterior Bloch
    Next Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.SectorMeasure.Presented SectorNext.Remainder SectorNext.Remainder.Affine
    AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
    Heir Clockwork Testing RG.Supply Push.PriceCompiler Shoot Heir.Suite UVNext.PricedKernels Folio Input
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {Z : ChartRatio G} {s : Sheet G} {K : MapPrices} {D : Rolls s} {Θ : Protection D}
    {C : Programs s} {d : ℕ → ℕ → Record} {P Q : ℕ→ℕ→ℝ} {w : ℕ→ℕ→ℝ} {r : ℕ→ℕ→ℕ} {F : ℕ→ℕ→Cafe}
    {Bt : Baton G} {m : ℕ→ℕ→Menu} {b : ℕ→ℕ→ Booth} {J : ℕ→ℕ→Aux}

def condition (D : Rolls s) (C : Programs s) (d : ℕ→ℕ→Record) (w : ℕ→ℕ→ℝ) (Bt : Baton G) (F : ℕ→ℕ→Cafe) (m : ℕ→ℕ→Menu) (j i : ℕ) (x : ℝ) :=
  ∀ H : Patch, H.J=j → H.L=D.L j → Peace (C j i) Bt H s.kernel (w j i) (F j i).r x ∧ ∀ {c f : Side} {S : StepData c f} (desk : Desk G S),
    S.patch=H → x=desk.betaHat → betaF G x H.L/2 ≤ desk.input.beta → (m j i).q=desk.profile → desk.input.p.threshold= fiery G x H.L → Gliss (d j i) desk (s.profile i).order

def Listens (W : Delays Θ) (C : Programs s) (d : ℕ→ℕ→Record) (w : ℕ→ℕ→ℝ) (Bt : Baton G) (F : ℕ→ℕ→Cafe) (m : ℕ→ℕ→Menu) :=
  ∀ j x,W.betaEntry j ≤ x → ∀ i, StepStages j i → s.first ≤ i → condition D C d w Bt F m j i x

theorem prelude (U : Delays Θ) (h : Refit.requestW D C Bt ≤ w) (he : ∀ j i, StepStages j i → s.first ≤ i → 2*storeCost (C j i) ≤ (F j i).r) :
    ∃ W : Delays Θ, DelayLe U W ∧ OrderedDelays W ∧ ∀ V : Delays Θ, DelayLe W V → Listens V C d w Bt F m := by
  have hx (j i) (hi : StepStages j i) : ∀ᶠ x in atTop,s.first ≤ i → condition D C d w Bt F m j i x := by
    by_cases h₁ : s.first ≤ i
    swap; exact Eventually.of_forall fun _ h => False.elim (h₁ h)
    let A:=Clockwork.patch D hi h₁
    have hl := h j i; rw [Refit.requestW,dif_pos (And.intro hi h₁)] at hl
    filter_upwards [peaceful (C j i) Bt A s.kernel (s.has A) hl (he j i hi h₁),gliss G A (d j i) (s.profile i).order (m j i).q] with x hx hg _ H hj hL
    have hr : H=A := by cases H; unfold A Clockwork.patch; congr
    rw [hr]; exact ⟨hx, hg⟩
  obtain ⟨W,hW,hw,H⟩ := delay_extra U _ (fun _ _ _=>True) (fun j => eventually_transitions j _ _ (hx j)) (by simp)
  exact ⟨W,hW,hw,fun V hV=> (H V hV).1⟩

def adapt (m : Menu) (D : Record) := {m with θ:=min m.θ (D.ε/32), positive := lt_min m.positive (by have := D.guards; positivity)}


end YM.PhysicalNext.JointLoad.Psalm.Stage
