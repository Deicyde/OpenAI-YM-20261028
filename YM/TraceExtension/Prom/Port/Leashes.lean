import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leashes
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Pleas
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leashes for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Display.Sew Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec
     Push.SectorMeasure Next.SectorChange Paint
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) {O : HaarBudget G} (J : ChartRatio G) {d : ℕ}
    (ξ : Purse)
local notation "A"=> C.path.levels

local notation "Υ"=> C.path.levels.params k

local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "S"=> C.path.levels.clock.op i p
local notation "L"=> ξ.band
local notation "HP"=> C.path.levels.clock.hatBeta

-- purchase Dawn c-independent capacities
local notation "v"=> gas ξ.era.coast
local notation "WL"=> Station.widthSky C.path.levels ξ.band k
local notation "X"=> Atlas.clim C.path.levels i
local notation "x₀"=> Atlas.clim C.path.levels k
variable {hpar : CorridorSky C.path.levels ξ.band ξ k}

/-- Local output of previous red call at age i.
May compute sequentially; Bush is NOT a kernel compatibility premise. Uses old
stage price/r, path and room plus previously obtained bounds. -/
structure BushSky (H : ShowHoursSky J B ξ k w l r) (P : Rep G (C.side i p)) (hi : i≤k) (ht : WL≤ i) : Prop where
  used : P.p=Paint.inbox C i (H.oldPrices i hi ht)
  exactTree : P.path=(C.path.rep N p i).path
  exactClip : P.clip=(C.path.levels.params i).clip
  βgap : |P.beta-x₀|≤ x₀/8
  rated : P.Lawful (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (C.path.levels.clock.allowance i) (v X)
-- ramp top: Running on this history for every N & p eventually. Need Simple, not necessarily Bound.

include M in
lemma bush_startSky {a w} (H : ShowHoursSky J B ξ k w l r) (g : LaunchSky C k ξ w a) (hk : k≤N) (P : Rep G (C.side k p)) (hs : Paint.survivors C N k p g.pane P)
    (hx : |(C.path.rep N p k).beta-x₀| ≤ x₀/8) : BushSky (N:=N) B J ξ H P le_rfl ((Station.widerSky ..).trans (beforeSky ..)):= by
  obtain ⟨hh,hV,T,X',hg,hT⟩:= hs; let V:= C.path.rep N p k
  have hb : P.beta=V.beta:= hg.precise.2.2.2.2.2.1
  refine ⟨hg.precise.2.2.2.2.1,hg.precise.1,hg.precise.2.1.trans ((M.wilson.represents N p k hk).clip),?_,?_⟩
  · rw [hb]; exact hx
  have ht : (v x₀)= Real.exp (-Paint.trib ξ.era.coast.a x₀):=by unfold gas Paint.trib; ring_nf
  rw [ht]; exact hV
section
variable {he : i≤k} {hh : Station.widthSky C.path.levels ξ.band k ≤ i} {P : Rep G (C.side i p)} {H : ShowHoursSky J B ξ k w l r} (hi : CorridorSky C.path.levels ξ.band ξ k)
-- Coast charge: do not read β drifts from a different course.
include hi
lemma bush_pricesSky (Q : BushSky (N:=N) B J ξ H P he hh): X/2 ≤ P.beta ∧ P.beta≤2*X := by
  have hn:= abs_le.mp Q.βgap; have hz : 0 ≤ x₀:= (zero_le_one.trans (C.path.levels.fits.delayed _).le)
  constructor <;> linarith only [hz,H.warm _ hh he, hn.1,hn.2,(hi.court i hh he).2]
lemma bush_posSky (Q : BushSky (N:=N) B J ξ H P he hh) : 0 < P.beta:= lt_of_lt_of_le (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed _))) (bush_pricesSky B J ξ hi Q).1
lemma groomSky (Q : BushSky (N:=N) B J ξ H P he hh) :
    ∃ (g σ δ Y₁ z : ℝ),Meets C.path.levels i p P g Y₁ δ ∧ P.Lawful σ (C.path.levels.params i).paths Y₁ δ z:= by
  let V:=C.path.levels.clock; let K:=C.path.levels.params i; let g:= (Real.sqrt P.beta)⁻¹
  have hp : 0<X:= zero_lt_one.trans (C.path.levels.fits.delayed i)
  obtain ⟨hb,hc⟩:= bush_pricesSky B J ξ hi Q; have hx:0<P.beta:= lt_of_lt_of_le (half_pos hp) hb
  have hT := Q.used; let he' := H.oldPrices i he hh
  have hg : 0<g:= by unfold g; positivity
  have hj : P.beta*g^2=1:= by unfold g;rw [inv_pow,Real.sq_sqrt hx.le,mul_inv_cancel₀ hx.ne']
  refine ⟨g,K.width,V.allowance i,V.loopCap i, _,⟨Q.exactClip,hc.trans ?_,hj,hg,?_,?_,he'.allowance,le_rfl⟩,Q.rated⟩
  · change 2*X ≤ 4*X; linarith only [hp]
  · let h:= (C.path.levels.clock.hatCoupling i); have hh: (C.path.levels.clock.hatCoupling i)>0:= by unfold Calendar.hatCoupling; exact inv_pos.mpr (Real.sqrt_pos.mpr hp)
    change 0<h at hh; have hU:X*h^2=1:= by unfold h Calendar.hatCoupling; rw [inv_pow, Real.sq_sqrt hp.le, mul_inv_cancel₀ hp.ne']
    have hu : g ≤ h*2:= by nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (g:ℝ))]
    refine hu.trans ?_; rw [hT]; change h*2 ≤ h*hot X; gcongr; exact (show (2:ℝ)≤4 by norm_num)|>.trans he'.gain
  apply le_trans _ (historic A i).1.symm.le
  rw [hT]; have hz:= he'.provision
  change phase (Atlas.clim C.path.levels i) ≤ regular (Atlas.clim C.path.levels i); nlinarith only [show 2*phase X ≤ regular X from hz.2.2.1, alpha_phase _ hp]
end
end YM.PhysicalNext.InteractingRank
