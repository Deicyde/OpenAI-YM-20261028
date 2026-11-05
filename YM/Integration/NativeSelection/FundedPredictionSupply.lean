import YM.Integration.NativeSelection.FundedCompanySelection

/-! Combine additional purchases before one native company is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeSelection.FundedPredictionSupply

open RG RG.Supply Precision PhysicalNext PhysicalNext.Repeat
open FundedCompanySelection
variable {G : Gauge}

/-- Purchase the prediction at every incoming native sheet and quote. -/
def AllPrices (prediction : Prediction G) : Prop :=
  ∀ (s : Sheet G) (T : MapPrices), Prepaid (@prediction) s (ThroughLaunch.raging s T)

def Always (G : Gauge) : Prediction G := fun {_} {_} {_} _ => True

/-- A vacuous additional prediction can retain all original floors and delays. -/
theorem always (s : Sheet G) (price : MapPrices) : Prepaid (@Always G) s price := by
  intro _ _ _ _ _ _ _
  refine ⟨fun _ => 0, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ V _
  refine ⟨V, Push.PriceCompiler.DelayLe.refl _, ?_⟩
  intros
  trivial

def Both (p q : Prediction G) : Prediction G := fun {_} {_} {_} R => p R ∧ q R

/-- Two predictors share a floor, and both receipts apply on the later delay. -/
theorem both {p q : Prediction G} {s : Sheet G} {price : MapPrices}
    (hp : Prepaid (@p) s price) (hq : Prepaid (@q) s price) :
    Prepaid (@Both G (@p) (@q)) s price := by
  intro targets expenses chart programs wages baton hw
  obtain ⟨floorP, first⟩ := hp targets expenses chart programs wages baton hw
  obtain ⟨floorQ, second⟩ := hq targets expenses chart programs wages baton hw
  refine ⟨floorP ⊔ floorQ, ?_⟩
  intro l hl D w u reg post scouts θ stages cost V quarter
  obtain ⟨W, hVW, hP⟩ :=
    first l (le_sup_left.trans hl) D w u reg post scouts θ stages cost V quarter
  obtain ⟨K, hWK, hQ⟩ :=
    second l (le_sup_right.trans hl) D w u reg post scouts θ stages cost W quarter
  refine ⟨K, hVW.trans hWK, ?_⟩
  intro W' hv bar wait priced carrier alloy η reset exchange menu aux rider booth hp' hy hm
  exact ⟨hP W' (hWK.trans hv) bar wait priced carrier η reset exchange menu aux rider booth hp' hy hm,
    hQ W' hv bar wait priced carrier η reset exchange menu aux rider booth hp' hy hm⟩

end YM.Integration.NativeSelection.FundedPredictionSupply
end
