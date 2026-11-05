import YM.TraceExtension.Prom.Sway.Tilt
import YM.MergeProof.West.Tael
import YM.TraceExtension.Prom.Front.West.Esme
import YM.TraceExtension.Prom.Front.West.Lais
import YM.TraceExtension.Prom.Front.West.Lys
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Soft.Coupons
import YM.TraceExtension.Prom.Port.Soft.Grows
/-!
  Variant of YM.MergeProof.West.Tael for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Ribbon Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B: Binding C)(H:C.Makes)(h: G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r D) (O:HaarBudget G) (J:ChartRatio G) {i k N p D0 m n d s:ℕ}
set_option quotPrecheck false
local notation "AX" => C.path.levels
local notation "Y" => clim C.path.levels k
local notation "K" => stamp C.path.levels N p
variable (M:Tapes.Panel d) {z l v:ℝ}
local notation "ξ" => M.bag ((AX).clock.J k)
-- common detail use COUNTERPART P.taylor & Q. Ticket general independent full BudgetPoint. prove rebudget.

-- probably Ticket structure need pieces.S.

structure ActumSky (Z: LegacyCostSky B J (-3) z (M.bag ((C.path.levels).clock.J k)) k s d O l v)(V:RG.Rep G (C.side k p))(h:N>k):Prop where
   pays : Emblem H (M.bag ((C.path.levels).clock.J k)) k N p V
   acts : ∃ P:(i:ℕ)→ RG.Rep G (C.side i p),P k=V ∧ WhipSky B J (M.bag ((C.path.levels).clock.J k)) Z.hours Z.moves (isohypse H h.le p) P (Station.widthSky AX (M.bag ((AX).clock.J k)|>.band) k) le_rfl
lemma prospectSky (L:LegacyCostSky B J (-3) z ξ k s d O l v)(hk:N>k)(hQ:|(C.path.rep N p k).beta-Y| ≤ Y/8):∃ V:RG.Rep G (C.side k p), ActumSky B H O J M L V hk:=by
   let t:= ξ; have hc:0≤ t.band:=by unfold t;rw [M.factor];linarith only [M.huge,Nat.cast_nonneg (α:=ℝ) d]
   obtain ⟨V,hV⟩:= repertoiresSky B H J L (hN:=hk.le) hc hQ
   have he:= embroideredSky B J _ _ H L.hours L.token L.moves V hV hc
   have hf:= he.fixture (beforeSky ..) (le_refl k)
   refine ⟨V k, ⟨fun Z hZ=>hZ.symm ▸ he.stencil,hf.threshold,hf.budget,?_⟩,V,rfl,hV⟩
   have hv:= he.paths.canvas.radius; change _+10≤t.era.coast.Q at hv; change _ ≤ t.era.coast.Q; omega
include H h hp
section
open Accent
variable {Kz:Set (Points (m+1))} {d0 : Fin (m+1)→ℕ}
variable (hZ:∀ i≤d, generator G i≤z)
include hZ
lemma earningsSky (Δ : ℕ)(e u₀:ℝ) (U:ℕ→Tapes.Panel d)(hD:∀ i,(U i).θ=Δ)(hu:∀ i,(U i).currency=e)(hE:∀ i,(U i).arc ≤ u₀) (g:(i:Fin (m+1))→ C.label (d0 i))(hm:m+1 ≤ n)(hz:2≤n) (hi:∀ i,d0 i≤d)(ht:IsCompact Kz)(he:Kz ⊆ conf _) : ∀ᶠ k:ℕ in atTop,
    let α:= (U k).bag (C.path.levels.clock.J k)
    let s:= clim C.path.levels k
    ∀ (l v:ℝ) (L: LegacyCostSky B J (-3) z α k n d O l v),∀ N (p:ℕ)(hk:k<N) V (X:ActumSky B H O J (U k) L V hk),∀ x:Points (m+1),tested AX α.band k x ∈ Kz→∀ h:FitSky AX α.band k x,
    ∀ (T:(i:Fin (m+1))→ StampDuty C k N p (d0 i) α.taylor V α.era.coast.Q (stamp AX N p)),∀ f:(i:Fin (m+1))→ C.label (d0 i),(∀ i,Solves C (mag AX α.band k) (d0 i) k N p (T i).T (g i) (f i)) →
    ∀ (s : modes (Fin (m+1))) (_:s.val.Nonempty),
      (Ship.yardSky C α.band hk.le p).rootTest (C.beta N p) (fun U=> (Ship.invoiceSky (jointX g) (q_asked (C:=C) f) h N p U).part s) ≤ Ship.budget C.path.levels n k:=by
   let c:ℝ:=d+6
   have hc: 6 ≤ c:=by unfold c; linarith only [Nat.cast_nonneg (α:=ℝ) d]
   have ha (M:Tapes.Panel d): 0 < M.arc:=by linarith only [M.huge,Nat.cast_nonneg (α:=ℝ) d]
   have hQ (M:Tapes.Panel d) (t i:ℕ)(h: i ≤ d) : M.arc*i+saves C i ≤ (M.bag t).credit:=by
       have hz:= mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (show 0≤ M.arc from (ha _).le); linarith only [M.loose t,hz,Next.Rank.Tapes.savings C i,show (i:ℝ) ≤ d from Nat.cast_le.mpr h]
   have hr(i):= StampDuty.procureSky C h H (d0 i) Δ (g i)
   obtain ⟨u,hU⟩:= eventually_atTop.mp (Ship.banking C.path.levels O h)
   filter_upwards [mural_castSky hi g ht he H h c hc (fun i=> by unfold c; linarith only [Next.Rank.Tapes.savings C (d0 i),show (↑(d0 i):ℝ) ≤ ↑d from Nat.cast_le.mpr (hi i)]) Δ (fun k=> (U k).arc) (fun i=> (U i).huge) u₀ hE,
     eventually_all.mpr hr,eventually_all.mpr fun i=> (hat_rate AX h).eventually (tremor e (hZ _ (hi i))), eventually_ge_atTop (C.ref d), eventually_all.mpr (fun i=> eventually_ge_atTop (C.ref (d0 i))),Radian.commissioned AX h d 2 (by decide) chartHeat_pos,(hat_rate AX h).eventually Flux.timing, (AX).fits.deep.eventually_gt_atTop ((AX).clock.J u+1)] with k hM ht hv hh hl Hq hv' hK
   intro α l v L N p hN V X x hy hX T f hf; obtain ⟨he',P,rfl,hP⟩:=X
   let M:=U k
   let b:= α.band; let s:= clim AX k
   have hY:α.taylor=Δ:=(M.stable _).trans (hD _); have hy':b= M.arc:= M.factor _
   have hm' : WallsSky b hi g Kz α.taylor k:=by rw [hY,hy']; exact hM
   have hT:= L.age.allot.permitted; let m0:=Station.widthSky AX b k
   have het(i) : Perch.bill e s* Spindle.moneys C (d0 i) k N p (f i) ≤ Perch.bill (-8) s ∧ Rise.coin ((T i).W (f i))≤ α.principal s := by
      obtain ⟨T0,-,hW,hS⟩:= reborn (j':=α.era.coast.Q) (β:=P k) hY (T i) rfl rfl rfl; have hv : T0.T=(T i).T ∧ T0.W=(T i).W:=⟨hW,hS⟩
      have hφ:Solves C (mag AX M.arc k) _ k N p T0.T (g i) (f i):=by rw [hv.1, ←hy']; exact hf i
      obtain ⟨hj,he⟩:= ht i M.arc e (ha _).le (show e+M.arc*d0 i+saves C (d0 i) ≤ -8 by
         rw [← hu k, show (U k)=M from rfl,← M.vital 0]; linarith only [hQ M 0 (d0 i) (hi i), (M.bag 0).fits]) (hY ▸ L.moves.year) N p hN.le T0 _ hφ; rw [hv.2] at he; exact ⟨hj,he.trans (Glimmer.billed _ (hQ M _ _ (hi i)))⟩
   have hΩ:u ≤ m0:=by
      by_contra! he; have hh := hT.bracket m0 (le_refl _) ((widerSky ..).trans (beforeSky ..)); have hv:= (AX).fits.mono he.le; omega
   apply y_readySky B H J L (hf:=hh) hP (le_trans (ha M).le (Eq.le (M.factor _).symm)) (hU _ hΩ) hv' (fun h=> Hq _ _ h) hl hi T g f hf hm' hy hX hz hm _ (fun i=> (het i).2)
   · intro hd; let Q:= C.path.rep N p k; let y:= seatsSky C b x hN.le p; let r':= Hat s^z
     have hu:0 < r':=Real.rpow_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (C.path.levels.fits.delayed _)))) _
     have he: Edition.Spaced Q.p.B y:= by rw [show Q.p=(AX).budget k from (H.wilson.represents N p k hN.le).vac]; exact hd
     refine caughtXSky C N k p m f b x hN H hl _ hp.1 ⟨fun _ _ i hi j hj hh=> he i j hh⟩ (fun a=> (Extra.Multi.Occupancy.of_injective (injected _ y Q.p.B_pos he) a).trans (hp.2 k)) hu (fun i=> ?_)
     exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Spindle.paid_pos ..) (C.path.levels.params k).columns_ge) hu.le).trans (hv i _ (Spindle.money_nn ..) (het i).1)
   intro i; rw [Purse.cash,(U k).vital,hu]; exact (het i).1
end
end YM.MergeProof
