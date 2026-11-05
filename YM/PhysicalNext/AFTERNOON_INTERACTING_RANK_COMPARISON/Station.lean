import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Chimes

/-!
# Posted requests owed after L, not after C is picked

Put in same Wait as Sector reg/Precal and others.

Calendar possibly still
unstitched to Warm roll.

`polite` exercises purchase purely arithmetic and
κ, gauge, β and row tests.

Doesn't include Furnace or Stake backing.

Forest F arbitrary; here Π→ issues to ALL on every V at clearance κ/s.

There
might be need to choose another chart hood rate for which those other physical
estimates also hold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Local RG.Supply
open scoped Topology BigOperators Classical
variable {G : Gauge} (J : ChartRatio G) (K : MapPrices) (W : ℕ → Stage) (C : KernelChoices)
    (i : ℕ) (ξ : Purse)

def shear (G : Gauge) (L : Side) := G.slopeConstant*Real.log (L.val)
structure Posts (L : Side) (l d s : ℝ) : Prop where
  monitor : Storefront i C W K L ξ s G
  clamp : ∀ n : ℕ,n ≤ 2→ ∀ x ∈ Set.Icc (s/2) s, ∀ y∈ Set.Icc (s/2) s, ∀ P R : BudgetPoint, P.B=walls y → R.B=walls x → TimeBand ξ.era ξ.goal L P R x y s n
  mile : 30 ≤ ξ.horizon
  melt x : x∈ Set.Icc (s/2) s → 2*shear G L ≤ x
  wool x : x∈ Set.Icc (s/2) s → 0 ≤ K.Ω i → ∀ P : Patch,P.J=i → P.L=L → P.Branches C G → ∃ u z,∀ β β',x/2 ≤ β→ β ≤ 3*x → x/2 ≤ β' → |β'-β|≤ (W i).drift+ shear G L →
    Dawn P (initials (G:=G) K W C i i) (K.α i) (K.η i) (K.Ω i) ξ.era.coast.Q u z (ξ.sends s) x β β'
  stamp x : x∈ Set.Icc (s/2) s →∀ (c f) (S : StepData c f) (T : Tube G S), S.patch.L=L → S.patch.J=i → S.patch.Branches C G → 100*(1+radiusB (retime x)) ≤ c.val →
      (initials K W C i i).Funds S T → Boosted T (initials K W C i i) (retime x) ∧ 0<d*fiery G (retime x) L ∧ 2*(d*fiery G (retime x) L)<firstRadius G ∧
        ∀ Y : Lantern G S, Y.hood=d*fiery G (retime x) L → ∀ β : ℝ, 0<β → ∀ D : Allocation G S (retime x) l, Coupler T Y J D β

structure Brevity (L : Side) : Prop where
  capital : capital C K i ≤ ξ.L
  width : 30≤ ξ.horizon
  pulse : Sizing G L (K.Ω i)
  credits : 8 * salary (load ξ.era) ≤ ξ.era.α ∧ 8 * salary ξ.era.coast.e ≤ ξ.era.α
  ceiling : Tab L (load ξ.era) ∧ Tab L ξ.era.coast.e

lemma polite (h : LocalRatio J) (L : Side) (hb : Brevity (G:=G) K C i ξ L) (l : ℝ) (hv : 0<l) : ∃ d : ℝ, 0<d ∧ ∀ᶠ s in atTop, Posts J K W C i ξ L l d s:= by
  obtain ⟨hc,hm,hS,⟨hx,hβ⟩,⟨hL,hF⟩⟩:= hb
  have ht:= forecasts i C W K L ξ G hc
  have he:= pedestals ξ.era (e:=2) ξ.goal L hL hF hx hβ
  have hh:= Perch.half.eventually_ge_atTop (2*shear G L)
  by_cases hz : ∃ P : Patch,P.J=i ∧ P.L=L ∧ P.Branches C G
  swap
  · refine ⟨1,zero_lt_one,?_⟩; filter_upwards [ht,he,hh] with s ht he hh; exact ⟨ht,he,hm,fun x H=>hh.trans H.1,fun x H h P i l w =>(hz ⟨P,i,l,w⟩).elim,fun x H c f P T i l w =>(hz ⟨P.patch,l,i,w⟩).elim⟩
  obtain ⟨P,hI,hP,H⟩:= hz
  have H' {V : Patch} (hI' : V.J=i) (hP' : V.L=L) : V=P:=by cases V; cases P; congr <;> simp_all
  subst L
  let T:= initials (G:=G) K W C i i
  obtain ⟨d,h',hf⟩:= coupling_issue J T h P H l hv
  obtain ⟨s₀,hs₀⟩:= eventually_atTop.mp (tall_limit.eventually ((booster P T H).and hf))
  have hv : 0≤ K.Ω i → ∃ U : ℝ,∀ᶠ t in atTop,∀ x∈ Set.Icc (t/2) t,∃ p,∀ β β',x/2≤β → β≤ 3*x →x/2≤β' → |β'-β|≤(W i).drift+shear G P.L → Dawn P T (K.α i) (K.η i) (K.Ω i) ξ.era.coast.Q U p (ξ.sends t) x β β' := fun H=> (herald P T (by assumption : P.Branches C G) (K.α i) (K.η i) (K.Ω i) hS (K.alpha_pos _) (K.eta_pos _) H _ ξ.foil _).imp fun x h=>h.2
  have hz :∀ᶠ t in atTop, 0≤ K.Ω i →∀ x∈ Set.Icc (t/2) t, ∃ U p,∀ β β',x/2≤β → β≤ 3*x →x/2≤β' → |β'-β|≤(W i).drift+shear G P.L → Dawn P T (K.α i) (K.η i) (K.Ω i) ξ.era.coast.Q U p (ξ.sends t) x β β':= by
    by_cases h:0≤ K.Ω i
    · obtain ⟨U,hp⟩:= hv h; exact hp.mono fun _ h _ x hv=> ⟨U,h x hv⟩
    exact Eventually.of_forall fun t he=> (h he).elim
  refine ⟨d,h',?_⟩; filter_upwards [ht,he,hh,Perch.half.eventually_ge_atTop s₀,hz] with s ht he hh hp hv
  refine ⟨ht,he,hm,fun x hx=>hh.trans hx.1,fun x hx' hk Q hQ hq hQ'=> H' hQ hq|>.symm ▸ hv hk x hx',?_⟩
  intro x hx' c f S T hP Hq HB hℓ hT
  obtain ⟨H1,h2,h3,h4⟩:=hs₀ x (hp.trans hx'.1)
  refine ⟨H1 S T (H' Hq hP) hℓ hT,h2,h3,fun Y hY β hβ D=> h4 c f S T (H' Hq hP) hℓ hT Y hY D β hβ⟩
end YM.PhysicalNext.InteractingRank
