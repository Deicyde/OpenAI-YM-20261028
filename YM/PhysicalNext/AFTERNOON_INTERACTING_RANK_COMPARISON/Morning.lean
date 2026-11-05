import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Focusing
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Illumined

/-! # Post requests for the Ignition

ALL purchasable after L (Sizing purchased), independent of
period. Per plateau stretch, apply across x,β bands with drift.
Doesn't imply arbitrary Rank Purse and trajectory already provide these
or determine which k buys subsequent estimate budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station WeightedGaussianMarginal45C.Issue.Cut
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

structure Dawn (P : Patch) (T : Teller G) (s n z : ℝ) (w : ℕ) (U t ε : ℝ) (x β β' : ℝ) : Prop where
  steady : Steady G P.L z x s β β'
  heart : Enlightened P T w x β
  strong : StrongScope P T U x
  cool : 0≤t
  heat : ShadePay w U G P.L 1 x β
  curves : InteractingRank.Paying P T s n z t x
  roam : Enclosed w G x
  swim : x^(-(1/8):ℝ)+t ≤ ε
  scope : x^(-(1/32):ℝ) ≤ ε
  azure : x^(-(1:ℝ)) ≤ ε^2

lemma herald (P : Patch) (T : Teller G) (h : P.Branches T.bind G) (s n z : ℝ) (hv : Sizing G P.L z)
    (hs : 0<s) (hn : 0<n) (hz : 0≤z) (w : ℕ) (fo γ : ℝ) : ∃ U : ℝ, 1≤U ∧ ∀ᶠ t : ℝ in atTop,
    ∀ x∈ Set.Icc (t/2) t, ∃ p : ℝ,∀ β β', x/2≤β → β ≤3*x→ x/2≤β'→ |β'-β| ≤ γ → Dawn P T s n z w U p (bill (-fo) t) x β β' := by
  obtain ⟨u,A,hu,hA,H⟩:=summon G P T h s z n hn hs hz
  obtain ⟨E,hE,hQ⟩:=scopes P T h
  obtain ⟨B,hB⟩:=eventually_atTop.mp (show ∀ᶠ x in atTop, StrongScope P T E x ∧ InteractingRank.Paying P T s n z (x^(-(1/8):ℝ)) x ∧ Enclosed w G x ∧ 0<x ∧ ∀ β : ℝ,x/2 ≤ β→β ≤ 3*x → Enlightened P T w x β ∧ ShadePay w E G P.L 1 x β ∧ ∀ β',x/2≤β' →|β'-β|≤γ → Steady G P.L z x s β β' from by
    filter_upwards [hQ,currency (TypeFace 2) s _ (1/8) hs (div_nonneg (psiBudget_nn z hz) (show 0≤(P.L.val:ℝ)^2 from sq_nonneg _)),
      currency (Current.dial P G) u A (1/8) hu hA.le,encloses w G,eventually_gt_atTop 0,illuminates P T w,buys_shade w G P.L E (zero_le_one.trans hE) 1 zero_le_one,
      steady_pass G P.L z s γ hv hz hs] with x h1 h2 h3 h4 h5 h6 h7 h8
    refine ⟨h1,⟨h2,fun Q hp hv=>?_⟩,h4,h5,fun i hi H=> ⟨h6 _ hi H,h7 _ hi H,fun j hk H' => h8 _ _ hi H hk H'⟩⟩
    obtain ⟨Z,hZ⟩:=H Q hp hv; exact ⟨Z,u,A,hZ,hu,hA,h3⟩)
  refine ⟨E,hE,?_⟩
  filter_upwards [long_pay fo (1/32) (by norm_num),long_pay (fo+1) (1/8) (by norm_num),long_pay (fo+fo) 1 zero_lt_one,absorb (-(fo+1)) (-fo) (by linarith) 2,Perch.half.eventually_ge_atTop B] with t ht he hp H ht'
  intro x hx
  obtain ⟨h1,h2,h3,h4,h5⟩:= hB x (ht'.trans hx.1)
  refine ⟨x^(-(1/8):ℝ),fun p q hp' hv ha he'=>?_⟩
  refine ⟨(h5 p hp' hv).2.2 q ha he', (h5 p hp' hv).1,h1,Real.rpow_nonneg h4.le _,(h5 p hp' hv).2.1,h2,h3,?_,ht _ hx,?_⟩
  · linarith only [he x hx,H]
  rw [sq,overlap,← neg_add]; exact hp x hx

variable {C : Family G} {N i p j : ℕ}
-- plateau can pay actual adjacencies when using `keeping`
lemma calendar_warm (m : ℕ) (C : Family G) : Atlas.clim C.path.levels (m+1)=betaF G (Atlas.clim C.path.levels m) (C.S.block m):= by
  unfold Atlas.clim Calendar.hatBeta betaF; rw [Schedule.scale_succ]; ring

end YM.PhysicalNext.InteractingRank
