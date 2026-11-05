import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Grows
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Bonfire
import YM.TraceExtension.Prom.Port.Soft.Postsale
import YM.TraceExtension.Prom.Port.Soft.Unlid
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Grows for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Display.Sew Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec
     Push.SectorMeasure Next.SectorChange Paint Function
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) (J : ChartRatio G) (ξ : Purse)
local notation "Λ"=> C.path.levels

local notation "L"=> ξ.band

variable (H : ShowHoursSky J B ξ k w l r) (Z : VentsSky B ξ J l r k) (O : LaunchSky C k ξ w a) (hN : k ≤ N)

variable (f : Course C N p k) (V : (i:ℕ)→Rep G (C.side i p))
local notation "WL"=> Station.widthSky C.path.levels ξ.band k
local notation "x₀"=> Atlas.clim C.path.levels k
structure WhipSky (i : ℕ) (h : WL ≤ i) : Prop where
  outer j (hs : i ≤ j) (he : j≤k) : BuoyantSky B J ξ (N:=N) H (V j) he (h.trans hs) ∧ f.Uses j (he.trans f.allow) (V j)
  stokes j (hp : i≤j) (he : j<k) : AriseSky B J ξ H he (h.trans hp) (N:=N) (V (j+1)) (V j)
  stops : Paint.survivors C N k p O.pane (V k)
include Z
-- end spark from true Law
lemma leafSky (p : ℕ) (ht : |(C.path.rep N p k).beta-x₀|≤ x₀/8) : ∃ V, WhipSky B J ξ H O (isohypse M hN p) V k ((widerSky ..).trans (beforeSky ..)):= by
  obtain ⟨P,H'⟩:=parser C hN M O.pane p
  let f:= isohypse M hN p; let V:= update (C.path.rep N p) k P
  have hb : V k=P:= update_self ..
  refine ⟨V,fun j hp he=> ?_,fun j hi he=> (he.not_ge hi).elim,hb.symm ▸ H'⟩
  obtain rfl:k=j:= le_antisymm hp he
  rw [hb]
  have ht:= bush_startSky B M J ξ H O hN P H' ht; have hp := cloth P ht.rated
  have hh:0 ≤ C.path.levels.clock.allowance k:= by unfold Calendar.allowance Calendar.hatCoupling; positivity
  refine ⟨⟨⟨ht.used,ht.exactTree,ht.exactClip,ht.βgap,?_⟩,{hp with patch:=?_}⟩,(lights C hN f M _ P H').settle.tied⟩
  · obtain ⟨p,⟨h,h₂,hM,⟨z,hz,hP⟩,hH⟩⟩:= hp.status; exact ⟨p,h,h₂,hM,⟨z,hz,fun i=>⟨(hP i).1,(hP i).2.1,(hP i).2.2.trans hh⟩⟩,hH⟩
  apply thin P hp.patch; rw [tsub_self,rollup];simp only [Nat.mul_zero,pow_zero,mul_one]
  exact (Z.rate k ((widerSky ..).trans (beforeSky ..)) le_rfl).permit Λ k rfl
lemma thicketSky (hb : 0≤ξ.band) (p x : ℕ) (h : WL ≤ x) (he : x≤k) (ht : |(C.path.rep N p k).beta-x₀|≤ x₀/8) : ∃ V, WhipSky B J ξ H O (isohypse M hN p) V x h := by
  let f:= isohypse M hN p
  induction he using Nat.decreasingInduction with
  | self=> exact leafSky B M J ξ H Z O hN p ht
  | of_succ i hi ih=>
    obtain ⟨V,hV⟩:= ih (h.trans (Nat.le_succ i))
    obtain ⟨hP,hF⟩:= hV.outer (i+1) le_rfl hi
    obtain ⟨Q,hQ⟩ := arousingSky B M J ξ H Z O.coup hN hi h hP hb
    let W:= update V i Q; have hu (u) (h:i<u): W u=V u:= update_of_ne (ne_of_gt h) ..; have hm: W i=Q:= update_self ..
    refine ⟨W,fun j hp he=> ?_,fun j hp he=> ?_,(hu k hi).symm ▸ hV.stops⟩
    · by_cases hz':i=j
      · subst j; rw [hm]; have hh:f.changeβ (i+1)=f.changeβ i:= (hyp M _ (show _ from hi) (p:=p)).trans (hyp M _ hi.le).symm
        refine ⟨hQ.lesions, ?_,hh.symm.trans (hF.coupling.trans hQ.still)⟩; unfold Course.vacuum; rw [f.flow_step _ i (hi.trans_le hN),show f.flow (bare _) (i+1) _=(V (i+1)).eval from hF.density,hF.coupling]; exact hQ.pushes.symm
      rw [hu _ (lt_of_le_of_ne hp hz')]; exact hV.outer _ (lt_of_le_of_ne hp hz') he
    by_cases hz':i=j
    · subst j; rw [hu _ (Nat.lt_succ_self _),hm]; exact hQ
    have ht:=lt_of_le_of_ne hp hz'; rw [hu _ (Nat.lt_succ_of_le hp),hu _ ht]; exact hV.stokes _ ht he
end YM.PhysicalNext.InteractingRank.Soft
