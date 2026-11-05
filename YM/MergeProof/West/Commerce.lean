import YM.MergeProof.West.Gede
import YM.MergeProof.West.Shacks
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis West Pump
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} (B : MapPrices)
variable (O : HaarBudget G) (J : ChartRatio G) {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
-- expose W shifts from same P.age; transportability with arbitrary further delay.Monetized M. K Legacy.Within Width bounds.
variable {ι:Type}[Fintype ι] {p m:ℕ→ℕ} {μ:ℕ→ℝ} {k P}
lemma y_tour (h: G.Simple)(he:Fortified (ι:=ι) X B p P k m) (H:∀ d,0≤μ d)(hx:∀ d,2 ≤ p d)(ht:∀ i,m i ≤ (w.L i).val) (hJ:LocalRatio J) (U:Wait Z) :∃ W:Wait Z, ∃ P':∀ d,ι → Tapes.Panel d,U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ (∀ d i,(P d i).arc=(P' d i).arc) ∧
    (∀ d i j,(P' d i).θ= (P' d j).θ ∧ ∀ k:ℕ, ((P' d i).bag k).era.coast.Q=((P' d j).bag k).era.coast.Q) ∧ ∀ χ, Clocked B O J W (fun d=> P' d χ) μ p k:=by
   choose W hv hw v z hV Ht hz hp using fun χ:ι=> retailers _ J (he.shops χ) ht (fun _=>1) (fun _ _=>1) (fun _ _=> zero_lt_one) hJ
   let P' := fun d χ=> curtain (P d χ) (v χ d) (hV χ d)
   have hh(χ) : PreStand X B (fun d=>P' d χ) k m:= recultivate X B (he.buys χ) (v χ) (hV χ) (hz χ)
   have hh' χ i j (hi:i∈ k j): Coul ((P' i χ).bag j) (p i) ∧ HLane ((P' i χ).bag j) (p i) (w.L j) ∧ reserveX (prepared X.kernel) (p i) j (P' i χ).θ (P' i χ).arc (w.L j).val:=by
      obtain ⟨⟨h1,h2,h3,h4⟩,⟨h5⟩,h6⟩:=he.lifts χ i j hi (w.L j) (ht j); exact ⟨⟨h1,h2,h3,h4⟩,⟨h5⟩,h6⟩
   have hyp (S:Finset ι) :∃ U':Wait Z, U.minLength ≤ U'.minLength∧ U.readyHere ≤ U'.readyHere ∧ U.window ≤ U'.window ∧ ∀ χ∈ S,Clocked B O J U' (fun d=> P' d χ) μ p k:=by
      induction S using Finset.induction with
      | empty=> exact ⟨U,le_rfl,le_rfl,le_rfl,by simp⟩
      | insert i S hi IH =>
        obtain ⟨Y,h1,h2,h3,h4⟩:= IH; obtain ⟨U',ha,hb,hc,hd⟩:= glide B O J (z i) (W i) μ p H hx h (hw i) hJ (hh i) ht (hh' i) (hp i) Y
        refine ⟨U',h1.trans ha,h2.trans hb,h3.trans hc,fun χ hi=> ?_⟩; rcases mem_insert.mp hi with rfl|hi; exact hd; exact printL B O J (h4 χ hi) U' ha hb hc
   obtain ⟨V,ha,hb,hc,hh⟩:= hyp univ; exact ⟨V,P',ha,hb,hc,fun i j=> rfl,fun d i j=> (he.same d i j),fun i=> hh _ (mem_univ _)⟩
-- also raise wheel bound at activated levels
lemma w_bound (U:Wait Z)(h:G.Simple):∃ W:Wait Z,U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ ∀ (A:Levels G),Paid W A→ ∀ i, W.readyHere (A.clock.J i) ≤ A.S.scale i→ Station.wheel A i ≤ A.clock.monitor i:=by
   have hp : Tendsto (Ship.preHat Z) atTop atTop := Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos h))
   choose x hx using fun j=> eventually_atTop.mp ((Next.Rank.Perch.bill_lo zero_lt_one).comp hp |>.eventually_ge_atTop ((w.L j).val:ℝ))
   let W:Wait Z:={U with readyHere:= fun j=>max (U.readyHere j) (x j) }
   refine ⟨W,le_rfl,fun j=>le_max_left ..,le_rfl,fun a h i hi=>?_⟩
   let j:= a.clock.J i; let s:= a.S.scale i
   have ht : Ship.preHat Z s=a.clock.hatBeta i:= by unfold Ship.preHat Calendar.hatBeta;rw [h.bar]
   rw [Atlas.fire_bill,wheel,h.lengths,clim,← ht]; exact hx j s ((le_max_right ..).trans hi)
-- Frequencies per commission, same indices & panel entries. Together with other waits. χ=main etc. orientation offsets.S.? add activations if needed.
structure Cutouts {C:Family G}(B:Binding C)(O:HaarBudget G)(μ:ℕ→ℝ)(p:ℕ→ℕ)(J:ChartRatio G) (P:∀ d,ι→ Tapes.Panel d) (i k:ℕ):Prop where
   limit : wheel C.path.levels k ≤ C.path.levels.clock.monitor k
   aisle (χ:ι) : ∃ l r,LegacyCost B J (-3) (μ i) ((P i χ).bag (C.path.levels.clock.J k)) k (p i) i O l r
lemma y_stead (h:G.Simple)(he:Fortified (ι:=ι) X B p P k m)(H:∀ d,0≤ μ d)(hx:∀ d,2 ≤ p d)(ht:∀ j,m j ≤ (w.L j).val)(hJ:LocalRatio J)(U:Wait Z) (hf:∀ i,∃ᶠ j in atTop,i∈k j):∃ W:Wait Z, ∃ P':∀ d,ι → Tapes.Panel d, U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ (∀ d i,(P d i).arc=(P' d i).arc) ∧
    (∀ d i j,(P' d i).θ= (P' d j).θ ∧ ∀ k:ℕ, ((P' d i).bag k).era.coast.Q=((P' d j).bag k).era.coast.Q) ∧ ∀ C : Family G,Paid W C.path.levels →∀ K:Binding C,K.prices=B → ∀ i:ℕ, ∃ᶠ j in atTop,Cutouts K O μ p J P' i j:=by
   obtain ⟨Y,P',h1,h2,h3,h4,h5,h6⟩:= y_tour B O J h he H hx ht hJ U
   obtain ⟨W,hv,hw,hp,he⟩:= w_bound Y h
   refine ⟨W,P',h1.trans hv,h2.trans hw,h3.trans hp,h4,h5,fun C hA K hz i=> ?_⟩
   let A:= C.path.levels; let L:= A.clock; have hC:=eventually_all.mpr (fun χ=> (printL B O J (h6 χ) W hv hw hp).rent C hA K hz)
   obtain ⟨t,ht⟩:= eventually_atTop.mp hC
   apply frequently_atTop.mpr; intro j
   obtain ⟨J0,hJ,h4,h5⟩:= ((hf i).and_eventually ((eventually_gt_atTop (L.J (max t j))).and (eventually_gt_atTop X.first))).exists
   obtain ⟨a,ha,hb,hl⟩:= hA.run J0 h5.le
   have hv:L.J a=J0:= hl a (by omega) (by omega)
   subst J0
   have hz : max t j ≤ a:= (lt_of_not_ge fun h=> not_lt_of_ge (A.fits.mono h) h4).le
   exact ⟨a,(le_max_right ..).trans hz,he A hA a ha,fun χ=> ht a ((le_max_left ..).trans hz) χ h5 ha hb (fun i hx hv=> hl i hx (by omega)) i hJ⟩
end YM.PhysicalNext.InteractingRank.Soft
