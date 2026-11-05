import YM.Next.FREE_KERNELS.Calendar
import YM.Next.STATIONARY.FullPlanned


/-!
Compose the accepted free-kernel issuer with the stationary-path producer.
The free prices are chosen first; the path prices then precede the Sheet and
Rolls. Actual Rack data are constructed on the very Paid Levels consumed by
geared. This does not construct a nonlinear density, Move or Directed recipe.
-/
set_option autoImplicit false
noncomputable section
namespace YM.B70FreeStationaryConnection
open Lattice RG Precision Supply

/-- A shared pre-L purchase order, with no external Rack premise. -/
theorem paths (G : Gauge) (hG : G.Simple) (K : KernelChoices) :
    ∃ (B : MapPrices) (l γ : ℕ → ℝ) (b : ℕ → ℕ),
      Next.Free.Catalog K B l γ b ∧
      ∃ σ A : ℕ → ℝ, (∀ i, 0 < σ i) ∧ (∀ i, 0 ≤ A i) ∧
      ∀ (τ A' : ℕ → ℝ), τ ≤ σ → (∀ i, 0 < τ i) → A ≤ A' →
      ∃ (d c : ℕ → ℝ) (u : ℕ → ℕ), (∀ i, 0 ≤ d i) ∧ (∀ i, 0 < c i) ∧
      ∀ s : Sheet G, s.kernel = K → Stationary.Buys s τ A' d u γ →
        (∀ i, b i ≤ s.floorL i) →
      ∃ B' : MapPrices,
      ∀ L : Rolls s, ∃ (v : ℕ → ℕ) (η : ℕ → ℝ), Stationary.BudgetGap s L B η ∧
      ∀ Θ : Protection L, ∃ Δ : ℕ → ℝ,
      ∀ (D : Delays Θ) (T : Bar D) (M : Wait T),
        Δ ≤ D.betaEntry → v ≤ D.shells →
      ∀ Q : PostCost L, Q.η = η → 1 ≤ Q.Γ → Q.c ≤ c →
      ∀ a : Levels G, Paid M a → ∀ Y : ChartRatio G, LocalRatio Y →
      ∃ X W : Horizon a, Craft.Rack a B X ∧ Next.Free.Present a X l ∧
        Bid.Retained W X ∧ W.Suffices B' ∧
        ∃ U : Kin W Y, Stationary.FullPaths U Q := by
  obtain ⟨B,l,γ,b,hCatalog,hFree⟩ := Next.Free.before_paid (G := G) K
  obtain ⟨σ,A,hσ,hA,hPaths⟩ :=
    Stationary.geared G hG B K γ (fun i => (hCatalog.fit i).le)
  refine ⟨B,l,γ,b,hCatalog,σ,A,hσ,hA,?_⟩
  intro τ A' hτ hτpos hA'
  obtain ⟨d,c,u,hd,hc,hStep⟩ := hPaths τ A' hτ hτpos hA'
  refine ⟨d,c,u,hd,hc,?_⟩
  intro s hs hBuy hb
  obtain ⟨B',hNative⟩ := hFree s hs
  refine ⟨B',?_⟩
  intro L
  obtain ⟨v,η,hGap,hPost⟩ := hStep s hs hBuy L
  refine ⟨v,η,hGap,?_⟩
  intro Θ
  obtain ⟨Δ,hAfter⟩ := hPost Θ
  refine ⟨Δ,?_⟩
  intro D T M hΔ hv Q hη hΓ hc' a ha Y hY
  obtain ⟨X,W,hRack,hPresent,hRetained,hSuffices,-⟩ :=
    hNative s rfl (fun _ => ⟨rfl,le_rfl,le_rfl⟩)
      (fun i _ => hBuy.axis i) (fun i _ => hb i) L Θ D T M a ha
  obtain ⟨U,hU⟩ := hAfter D T M hΔ hv Q hη hΓ hc' a ha X W hRack hRetained Y hY
  exact ⟨X,W,hRack,hPresent,hRetained,hSuffices,U,hU⟩
end YM.B70FreeStationaryConnection
