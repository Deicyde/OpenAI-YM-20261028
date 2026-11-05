import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Income
/-! # Base Maj at any fixed lattice. candidate Even for recollection price
    nonsmall here. Gives branch Leg and summability for Compared so Compact.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet March Hues
open Gas Ursell Trees Multiple Alabaster Match Greenbelt Letter
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Geo Ovens RG.Shoot Next.Scheduling
open Push.BetaTransport
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I U : RG.Rep G f}
    {x μ C v e d D s : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}

lemma concerns {E:Type} (A:E→ Support c) (B: ℕ) (f:E→ ℝ) (he : Ac.Hit A B f d e) (hd:0 ≤ d) (hf:∀ i,0 ≤ f i) (hk : ∀ i,f i ≠ 0 → (A i).Nonempty) : Summable f := by
  have hp:= AbsoluteSums.Product.everyone_ne A B hf hk he
  exact hp.2.1.of_nonneg_of_le hf fun i=> le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg hd (Nat.cast_nonneg _)))

variable (Θ : Year H j v χ) (p : BudgetPoint) (hp : p.threshold=Pressure.temp x) (hf : p.order ≤ j)
   {σ C' Λ : ℝ} (h : T.down.Bounds T.low σ C' Λ) (hd : WilsonStartup.Decent T.low p) (hv : preExponent p/p.B≤ σ/2) (hΨ : Cash.Renewed n e d D H)
variable {H₀:Cash W x μ L Q o C T U} (X: Match.Alliance H₀ H 1 0) (γ:ℝ) (A:H₀.fragrances→RegularAddress c) (hA:∀ z,(A z).support=Song.perf H₀ z)

def booth (H₀:Cash W x μ L Q o C T U) (p:BudgetPoint) (A:H₀.fragrances→RegularAddress c) := {posting p H₀ with reg:=revolve (Sum.elim A (strings T.down p)) ∘ Song.pennant H₀}

include Θ hp hf h hd hv hA
theorem espy : let P:=Sum.elim A (strings T.down p); let R:=opus H₀ X χ γ
    ∃ f:Magazine H₀ → ℝ, Summable f ∧∀ i,p.Regular (P i).support (R i) ∧ p.supBounds (P i).site (P i).support (R i) (f i):= by
  intro Z V
  obtain ⟨f,hF,hx⟩:= Song.stanzaReady (n:=c) T.down T.low p R.beta γ h hd hv
  have hU:= chargedAt p f _ (fun i=> (hx i).2.1) hF
  let v i:= Θ.net.markΦ i p.power; let g:= v ∘ X.furrow
  have hk:=Θ.pay.applies Θ.net p.power 0; simp only [Nat.zero_le,↓reduceIte] at hk
  have hg: Summable v:= concerns _ _ _ hk le_rfl (fun i=> by obtain ⟨a,b⟩:= Song.crest H i; exact (Θ.net.gloryBudget i p hp hf).2.2 p.power le_rfl a b |>.1) (fun i _=> Song.crest H i)
  have hn : Summable g:= hg.comp_injective X.furrow.injective
  let u : Magazine H₀→ℝ:= Sum.elim g f; refine ⟨u,Summable.sum u hn hU,?_⟩; rintro (z|z)
  · change p.Regular (A z).support _ ∧ p.supBounds _ (A z).support _ _; rw [hA,Song.reconnects H₀ X z]
    have ht:= (Θ.net.gloryBudget (X.furrow z) p hp hf).2; refine ⟨CouplingShape.reg_scale _ ht.1,?_⟩
    obtain hb:= CouplingShape.sup_scale (-1) (ht.2 p.power le_rfl (A z).site (show _ ∈ Song.perf H (X.furrow z) from (hA z).trans (Song.reconnects H₀ X z) ▸ (A z).anchor)); rw [abs_neg,abs_one,one_mul] at hb; exact hb
  exact hx z
omit hp hf h hd hv hA Θ
include hΨ
lemma fitted : ∃ k:ℕ→ℝ, Summable k ∧∀ i,0 ≤ k i ∧ ∀ U:Config G c, ‖Refrain.fuse H₀ X χ (Refrain.badge H₀ i) U‖ ≤ k i := by
  let g := H.excels n; have ht i (hi : g i≠0): (H.library i).Nonempty := by
    unfold g Cash.excels at hi; split at hi
    next hx =>
      obtain ⟨x,hv⟩:= hx.2.1; exact Finset.Nonempty.mono (subset_biUnion_of_mem _ hv) (Refrain.chapter_ne H x)
    exact False.elim (hi rfl)
  have hk:= H.bulkhead hΨ 0; simp only [Nat.zero_le,↓reduceIte] at hk
  have h := concerns H.library _ g hk hΨ.full (H.excels_nn n) ht
  let y: Refrain.Annual H₀→ℝ:= Sum.elim (fun i=> g (X.tongs i.val)) (fun _=>0)
  have hf: Summable y:= Summable.sum y (h.comp_injective (X.tongs.injective.comp Subtype.val_injective)) summable_zero
  have hy i: 0 ≤ y i ∧ ∀ U, ‖Refrain.fuse H₀ X χ i U‖ ≤ y i := by
    rcases i with i|i; · exact ⟨H.excels_nn _ _,fun U=> H.excel_boundsPool ..⟩
    simp [y, Refrain.fuse]
  exact ⟨y ∘ Refrain.badge H₀,hf.comp_injective (Refrain.badge H₀).injective,fun i=>hy _⟩
include Θ hp hf h hd hv hA
lemma life : let S:= (Yearling.booth H₀ p A).read (plusone H₀ X χ γ)
    ∃ f g:ℕ→ℝ, Summable f ∧ Summable g ∧ Majorizes p f g S:= by
  intro S'; obtain ⟨f,hF,hU⟩:= espy Θ p hp hf h hd hv X γ A hA; obtain ⟨g,hg,hk⟩:= fitted hΨ X (χ:=χ) -- args?
  let P:= Sum.elim A (strings T.down p); let q i:= Rim c*(turnFee p*f i)
  let Y (i:Seat c × Magazine H₀):=q i.2
  have hp i:0 ≤ q i:= mul_nonneg (rim_nn _) (mul_nonneg (turnFee_pos _).le (hU i|>.2.1))
  have hy: Summable Y:= (summable_prod_of_nonneg (f:=Y) fun i=> hp _).2 ⟨fun i=> (hF.mul_left _).mul_left _,Summable.of_finite⟩
  refine ⟨Y ∘ Song.pennant H₀, g,hy.comp_injective (Song.pennant H₀).injective,hg,⟨?_,hk⟩⟩; intro j
  let u:= pennant H₀ j; obtain ⟨hk,hv⟩:= hU u.2
  have he:= CouplingShape.sup_scale (Song.Rim c) (Song.transSup u.1 hk hv); rw [abs_of_nonneg (rim_nn _)] at he; exact he
end YM.PhysicalNext.Repeat.Yearling
