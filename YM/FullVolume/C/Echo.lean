import YM.FullVolume.C.Clockers
/-! Parsimony: untouched stratum coefficients only path and scalar reads.-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable (P : Match.Alliance H I 1 0) (hz:P.units=Equiv.refl _)
variable (hp:R.path=R'.path) (he:R.activities.reg=R'.activities.reg) (hk:R.activities.forced=R'.activities.forced)
variable (hf:R.clip=R'.clip) (hb:R.beta=R'.beta) (hy:R.p=R'.p)
section
include hp he hk hf hb hy
-- unused k,l allowed. Hard profiles unchanged
lemma peers (Y : Coat T F) (u : Air f G) (b:Park c f) :
    Polar.floating Y o.a R W X.table u (own (hatch S b)) X.halo (hatch S b) = Polar.floating Y o.a R' W X.table u (own (hatch S b)) X.halo (hatch S b):=by
  unfold Polar.floating; apply Finset.prod_congr rfl; intro i hi
  obtain ⟨i,_,rfl⟩:= Finset.mem_map.mp hi
  obtain ⟨u',c',⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,P,B,T₁⟩:=R'
  cases hp; cases he; cases hk; cases hf; cases hb; cases hy
  rcases i with i|i|i|i <;> rfl
lemma causal (Y : Coat T F) (b:Park c f) : Shield.shelter Y W o.a (hatch S b) R X.table X.halo = Shield.shelter Y W o.a (hatch S b) R' X.table X.halo:=by
  have h: areas R T X.halo Y.B=areas R' T X.halo Y.B:=by
    obtain ⟨u',c',⟨s,v,e1,k1⟩,p,b,t⟩:=R
    obtain ⟨U,C,⟨S,V,e2,k2⟩,P,B,T₁⟩:=R'; cases hp; cases he; cases hk; rfl
  unfold Shield.shelter; rw [h]
  rw [show troupe T R X.halo Y.B (hatch S b)=troupe T R' X.halo Y.B (hatch S b) from ?_]
  swap
  · obtain ⟨u',c',⟨s,v,e1,k1⟩,p,b,t⟩:=R
    obtain ⟨U,C,⟨S,V,e2,k2⟩,P,B,T₁⟩:=R'; cases hp; cases he; cases hk; rfl
  split_ifs; swap; rfl
  unfold Shield.seating Matter.ground; rw [h]; apply congr_arg likely; funext i
  unfold Shield.bars; simp_rw [peers hp he hk hf hb hy]

variable (χ)
lemma beaconL (b : Vines c f) (hh : Stir H b) (hi : Stir I b) (U : Config G c) :
    stream H χ U (vintage b hh)= stream I χ U (vintage b hi):=by
  unfold stream Gas.term; rw [← mana hh, ← mana hi]; rw [show Meadow.ground H=Meadow.ground I from ?_]; swap
  · unfold Meadow.ground Cash.unionP; rw [same_area (H:=H) (J:=I) hp he hk]
  have hz (i: Option (Fin b.fst)) : leaflet H χ U ((vintage b hh).2 i)=leaflet I χ U ((vintage b hi).2 i):= by
    unfold leaflet; apply congr_arg likely; funext r; unfold Stained.fringe; apply integral_congr_ae
    filter_upwards with z; exact causal hp he hk hf hb hy _ (b.2 i)
  refine congr_arg₂ HDiv.hDiv (congr_arg (fun z:ℝ=> coefficient (blocked (Meadow.ground I)) b.2*z) (Finset.prod_congr rfl fun i _=> hz i)) rfl

-- no ĸ' read even for AREA transform off healthy domain
include P hz
lemma rosen (i:Magazine H) (hi : ¬keep H i) (γ:ℝ): opus H (staple (J:=H) rfl rfl rfl) χ γ i=opus H P χ γ i:=by
  rcases i with i|i
  · change ¬i∉Set.range (booths H) at hi
    obtain ⟨i,rfl⟩:i∈Set.range (booths H):=not_not.mp hi
    ext V; change (-1:ℝ)*stream H χ V ((staple (H:=H) (J:=H) rfl rfl rfl).furrow _) = (-1)*stream I χ V (P.furrow _)
    rw [identifies P hp hz (same_area (H:=H) (J:=I) hp he hk)]
    exact congr_arg (fun x:ℝ=> (-1)*x) (beaconL χ hp he hk hf hb hy i.val i.property ((firstBatch hp (same_area (H:=H) (J:=I) hp he hk) i).property) V)
  change sounding _ _ R.beta _ _ = sounding _ _ R'.beta _ _; rw [hb]
lemma wires (d i) (hi : debris H d i) (γ:ℝ): (plusone H (staple (J:=H) rfl rfl rfl) χ γ).logRead i=(plusone H P χ γ).logRead i:=by
  ext U; change Rim c * (opus H _ χ _ _) _= Rim c * (opus H P χ _ _) _
  rw [rosen χ P hz hp he hk hf hb hy (pennant H i).2 hi.1]
end
end YM.PhysicalNext.Repeat.Meadow
