import YM.TraceExtension.Prom.Port.Station
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Auction
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Local RG.Supply
open scoped Topology BigOperators Classical
variable {G : Gauge} (J : ChartRatio G) (K : MapPrices) (W : ℕ → Stage) (C : KernelChoices)
    (i j : ℕ) (ξ : Purse)
structure BrevitySky (L : Side) : Prop where
  capital : capitalSky C K i j ≤ ξ.L
  width : 30≤ ξ.horizon
  pulse : Sizing G L (max (K.Ω i) (K.Ω j))
  credits : 8 * salary (load ξ.era) ≤ ξ.era.α ∧ 8 * salary ξ.era.coast.e ≤ ξ.era.α
  ceiling : Tab L (load ξ.era) ∧ Tab L ξ.era.coast.e
open Atlas
lemma forecastsSky (i j : ℕ) (K : KernelChoices) (M : ℕ → Stage) (B : MapPrices) (L : Side) (U : Purse) (G : Gauge)
    (hU : capitalSky K B i j ≤ U.L) : ∀ᶠ s in atTop, StorefrontSky i j K M B L U s G := by
  let E := (RankCovariance.prepared K).centers i
  have he:= (bill_lo (LiftMark.shade_pos U.taylor)).eventually_ge_atTop E
  by_cases ht : (∃ P : Patch, P.J=i ∧ P.L=L ∧ P.Branches K G) ∧ 0≤ B.Ω i
  swap
  · filter_upwards [he] with s hs; exact ⟨hU,hs,fun x P h v t _ hx=> (ht ⟨⟨P,h,v,t⟩,hx⟩).elim⟩
  obtain ⟨⟨P,h,v,t⟩,hp⟩:=ht
  filter_upwards [he,confers P (initials B M K i j) (G:=G) t _ (B.η i) _ (lt_min (B.alpha_pos i) (B.alpha_pos j)) (B.eta_pos i) (hp.trans (le_max_left _ (B.Ω j))) U] with s hs hy
  refine ⟨hU,hs,fun x V he hv h hx h' =>?_⟩; rw [show V=P from ?_]; exact hy x hx
  cases P; cases V; congr <;> simp_all
lemma politeSky (h : LocalRatio J) (L : Side) (hb : BrevitySky (G:=G) K C i j ξ L) (l : ℝ) (hv : 0<l) : ∃ d : ℝ, 0<d ∧ ∀ᶠ s in atTop, PostsSky J K W C i j ξ L l d s:= by
  obtain ⟨hc,hm,hS,⟨hx,hβ⟩,⟨hL,hF⟩⟩:= hb
  have ht:= forecastsSky i j C W K L ξ G hc
  have he:= pedestals ξ.era (e:=2) ξ.goal L hL hF hx hβ
  have hh:= Perch.half.eventually_ge_atTop (2*shear G L)
  by_cases hz : ∃ P : Patch,P.J=i ∧ P.L=L ∧ P.Branches C G
  swap
  · refine ⟨1,zero_lt_one,?_⟩; filter_upwards [ht,he,hh] with s ht he hh; exact ⟨ht,he,hm,fun x H=>hh.trans H.1,fun x H h P i l w =>(hz ⟨P,i,l,w⟩).elim,fun x H c f P T i l w =>(hz ⟨P.patch,l,i,w⟩).elim⟩
  obtain ⟨P,hI,hP,H⟩:= hz
  have H' {V : Patch} (hI' : V.J=i) (hP' : V.L=L) : V=P:=by cases V; cases P; congr <;> simp_all
  subst L
  let T:= initials (G:=G) K W C i j
  obtain ⟨d,h',hf⟩:= coupling_issue J T h P H l hv
  obtain ⟨s₀,hs₀⟩:= eventually_atTop.mp (tall_limit.eventually ((booster P T H).and hf))
  have hv : 0≤ K.Ω i → ∃ U : ℝ,∀ᶠ t in atTop,∀ x∈ Set.Icc (t/2) t,∃ p,∀ β β',x/2≤β → β≤ 3*x →x/2≤β' → |β'-β|≤(W i).drift+shear G P.L → Dawn P T (min (K.α i) (K.α j)) (K.η i) (max (K.Ω i) (K.Ω j)) ξ.era.coast.Q U p (ξ.sends t) x β β' := fun H=> (herald P T (by assumption : P.Branches C G) (min (K.α i) (K.α j)) (K.η i) (max (K.Ω i) (K.Ω j)) hS (lt_min (K.alpha_pos _) (K.alpha_pos _)) (K.eta_pos _) (H.trans (le_max_left ..)) _ ξ.foil _).imp fun x h=>h.2
  have hz :∀ᶠ t in atTop, 0≤ K.Ω i →∀ x∈ Set.Icc (t/2) t, ∃ U p,∀ β β',x/2≤β → β≤ 3*x →x/2≤β' → |β'-β|≤(W i).drift+shear G P.L → Dawn P T (min (K.α i) (K.α j)) (K.η i) (max (K.Ω i) (K.Ω j)) ξ.era.coast.Q U p (ξ.sends t) x β β':= by
    by_cases h:0≤ K.Ω i
    · obtain ⟨U,hp⟩:= hv h; exact hp.mono fun _ h _ x hv=> ⟨U,h x hv⟩
    exact Eventually.of_forall fun t he=> (h he).elim
  refine ⟨d,h',?_⟩; filter_upwards [ht,he,hh,Perch.half.eventually_ge_atTop s₀,hz] with s ht he hh hp hv
  refine ⟨ht,he,hm,fun x hx=>hh.trans hx.1,fun x hx' hk Q hQ hq hQ'=> H' hQ hq|>.symm ▸ hv hk x hx',?_⟩
  intro x hx' c f S T hP Hq HB hℓ hT
  obtain ⟨H1,h2,h3,h4⟩:=hs₀ x (hp.trans hx'.1)
  refine ⟨H1 S T (H' Hq hP) hℓ hT,h2,h3,fun Y hY β hβ D=> h4 c f S T (H' Hq hP) hℓ hT Y hY D β hβ⟩

open Pump
variable {W K i j ξ J}
lemma proclaimSky {W d' d s : ℝ} {i : ℕ} {L : Side} {v : Purse} (B : MapPrices)(X:Sheet G) {j:ℕ}{J:ChartRatio G} (h : Ports (initials B X.profile X.kernel i j) J i L v W d' s) (hp : PostsSky J B X.profile X.kernel i j v L W d s) : PostsSky J B X.profile X.kernel i j v L W d' s:= by
  refine ⟨hp.monitor,hp.clamp,hp.mile,hp.melt,hp.wool,?_⟩
  intro x hx c f S T hL hv hk hs ht
  let Q:= h.localizes S.patch hv hL hk|>.march x hx
  obtain ⟨hp,H⟩:=Q.eligible S T rfl hs ht
  rw [← hL]; exact ⟨hp,Q.boom,Q.ride,fun Y h β hb D=>H Y D β h hb⟩
end YM.PhysicalNext.InteractingRank
