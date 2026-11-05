import YM.Pert.Dense.Portal
import YM.SharpGram.Dense.Width
/-!
# StationPort with a prescribed slim Wait

Don't ask the existing `Clocked` provider how large its window is; it only has a
sublin receipt. Return a Clocked *for* a resource specified at log scale, by
paying both of its necessary Tapes estimates within that window. Adapted from
MergeProof.West.{Shacks,Commerce}, Pert.Dense.Portal, reuses the actual
rank machinery.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis West Pump
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} (B : MapPrices)
variable (O : HaarBudget G) (J : ChartRatio G) {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
open SharpGram.Dense
lemma glideSlim {P k M} (d : ℕ→ℕ→ℝ) (wL : ℕ→ℝ) (m : ℕ→ℝ)(p:ℕ→ℕ) (hm : ∀ d,0 ≤ m d)(hx:∀ d,2 ≤ p d) (simple : G.Simple)
    (hw : ∀ i,0<wL i) (hJ : LocalRatio J) (hs : PreStand X B P k M) (hl : ∀ j,M j≤ (w.L j).val)
    (he:∀ i j,i∈ k j→ Coul ((P i).bag j) (p i) ∧ HLane ((P i).bag j) (p i) (w.L j)∧ reserveX (prepared X.kernel) (p i) j (P i).θ (P i).arc (w.L j).val)
    (hp : ∀ i j,i∈ k j →∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) ((P i).bag j) (wL j) (d i j) s)
    (U : Wait Z) (hU : U.window=slim Z) : ∃ (W : Wait Z), U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ W.window=U.window ∧ Clocked B O J W P m p k:= by
  have hδ:=hp
  have hp i j (h:i∈k j):= hs.reg i j h|>.2 (w.L j) (hl j)
  have ht : Tendsto (Ship.preHat Z) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos simple))
  choose! u hD hF using fun i j (h:i∈k j)=> polite J B X.profile X.kernel j ((P i).bag j) hJ (w.L j) (hs.potion _ _ h _ (hl j)).1 (wL j) (hw j)
  let t j:= (w.L j)
  have hQ (i j)(h:i∈k j) (n:ℕ)(hY:n ≤ p i) : ∀ᶠ s in atTop, let R:=(P i).bag j; Caff (G:=G) R (Ship.preHat Z s) (bump (t j).val R.band (Ship.preHat Z s)) (p i) n:=by
     obtain ⟨hs₁,hR,H⟩:= he i j h; let v:= (hp i j h).1
     exact ht.eventually (joys hs₁ _ hR v.bound.large v.bound.band v.credit (hx _) hY)
  have hE i j (h:i∈k j) := hs.potion i j h _ (hl j)|>.1
  have hΩ (i j)(h:i∈k j) := ht.eventually (pedestals (e:=p i) ((P i).bag j).era ((P i).bag j).goal (w.L j) (hE _ _ h).ceiling.1 (hE _ _ h).ceiling.2 (hE _ _ h).credits.1 (hE _ _ h).credits.2)
  have hh (j):= (eventually_all_finset (k j)).2 (fun i hi=> (ht.eventually ((hF i j hi).and (hδ i j hi))).and (((ht.eventually (clearingX (prepared X.kernel) (he _ _ hi).2.2 i)).and ((eventually_all_finset (range (p i+1))).2 (fun n hn=> hQ i j hi n (Nat.lt_succ_iff.mp (mem_range.mp hn))))).and ((late _ Z _ (hs.potion i j hi _ (hl j)).2 simple (by rw [(P i).factor j];linarith only [(P i).huge,Nat.cast_nonneg (α:=ℝ) i])).and (hΩ i j hi))))
  have heX(i j)(h:i∈k j) :
      ∀ᶠ s : ℝ in atTop,
        Ship.benchCost Z ((P i).bag j).band j s ≤ U.window j s ∧
        cardTest Z O j (p i) ((P i).bag j).band ((P i).bag j).era s ∧
        cardTest Z O j 2 ((P i).bag j).band ((P i).bag j).era s ∧
        SlotPrice ((P i).bag j) (m i) G (X.profile j) (w.L j) (Ship.preHat Z s) := by
    have hpos : 0 ≤ ((P i).bag j).band := by rw [(P i).factor]; linarith [(P i).huge,Nat.cast_nonneg (α:=ℝ) i]
    rw [hU]; exact (bench_slim simple _ j hpos).and ((reserves Z simple _ _ (by have h:=hx i; omega) _ hpos _ _).and
      ((reserves Z simple _ _ (by norm_num) _ hpos _ _).and (ht.eventually (annually _ _ (hp i j h).1 (hm i)))))
  choose t' Ht using fun j=> eventually_atTop.mp ((hh j).and ((eventually_all_finset (k j)).2 (fun i hi => heX i j hi)))
  let W : Wait Z := { U with readyHere := fun j => max (U.readyHere j) (t' j) }
  have hr j : t' j ≤ W.readyHere j := le_max_right ..
  refine ⟨W,le_rfl,fun j=> le_max_left ..,rfl,⟨fun C hk K hK=>?_⟩⟩
  have hX i j (h:i∈k j): ReadyRack O j ((P i).bag j) (m i) W:= by
    refine ⟨fun s hs=>?_,fun s hs=>( (Ht j s ((hr j).trans hs)).2 i h).2.2.2⟩
    obtain ⟨hx,_,he,_⟩ := (Ht j s ((hr j).trans hs)).2 i h
    exact ⟨he,hx⟩
  filter_upwards [vault_size C.path.levels simple] with a hT
  intro A j hx' hY hw hz i hj
  let y:= Ship.preHat Z (C.S.scale a); let L:= A.clock; let P':=(P i).bag j; let v:= (P i).patronize C (hm i)
  obtain ⟨⟨hf,hδ⟩,⟨hC,hρ⟩,hAdap,hW⟩ := (Ht j _ ((hr j).trans hY)).1 i hj
  obtain ⟨ho,hP⟩:= affords simple O v W hk (hX i j hj) hx' (show C.path.levels.clock.J a=j from rfl) hY hw hz
  have h : y=clim A a:= by unfold y Ship.preHat; change _=Calendar.hatBeta _ _; rw [Calendar.hatBeta,hk.bar]
  have hG': Paint.TableReady C a (-3) (load P'.era) P'.era.coast.a := ho.cost.pane
  have hy : Metering v O a (-3):=ho; have hf':Launch C a P' (-3) (m i):= ho.cost
  have hl' : ShowHours J K P' a (-3) (wL j) (d i j):=by
    refine ⟨?_,hP,hT _ ho.cost.coup,?_,?_⟩
    · unfold Ceremony; rw [hK, show C.path.levels.clock.J a=j from rfl, show C.path.levels.clock.kernel=_ from hk.kernel, show C.path.levels.clock.stage=_ from hk.stage, show C.path.levels.clock.factor=_ from hk.lengths]; exact h ▸ (Pump.proclaimed B X hδ.onRoad hf)
    · intro s hs hX'; have hi := hf'.coup
      have hr : C.path.levels.clock.J s=j:= hi.heft.plateau s hX' hs
      have hD : C.path.levels.params s=X.profile j:= by change A.clock.stage (C.path.levels.clock.J s)=_; rw [show A.clock.stage=_ from hk.stage,hr]
      have hw:= hi.court s hX' hs
      unfold Paint.TableReady; rw [hD]
      have hp:SlotPrice P' (m i) G (X.profile j) (w.L j) (clim A a):= h ▸ (hX i j hj).2 _ hY
      exact hp.dating _ hw
    · unfold Levels.params Calendar.params; rw [show C.path.levels.clock.J _ = j from rfl, show C.path.levels.clock.stage=_ from hk.stage, show C.path.levels.clock.factor=_ from hk.lengths]; exact h ▸ hAdap
  have he1: Charge A P'.band a (p i) O P'.era := held_at W A hk hx' rfl hY hw hz O (p i) P'.band P'.era (by
    intro v hv
    have he := (Ht j v ((hr j).trans hv)).2 i hj
    exact ⟨he.2.1,he.1⟩) simple
  have ht : wheel A a=(w.L j).val:=by unfold wheel; rw [hk.lengths]
  refine ⟨_,_,hf', he1,hl',?_,?_,?_,?_⟩
  · constructor; change Timing (initials K.prices A.clock.stage A.clock.kernel _ _) J _ _ P' _ _ _
    rw [hK, show A.clock.J a=j from rfl,hk.stage,hk.kernel,hk.lengths]; exact h ▸ hδ
  · change Eark (prepared A.clock.kernel) (p i) j i P'.taylor P'.band (wheel A a) (clim A a)
    rw [show P'.band= _ from (P i).factor j, show P'.taylor=_ from (P i).stable j,hk.kernel, ht,←h]; exact hC
  · intro n hn; change Caff P' (clim A a) (a - middle A P'.band a) (p i) n; rw [he1.allot.permitted.full,height,ht,← h,show A.clock.hatBeta a=y from h.symm]; exact hρ n (mem_range.mpr (Nat.lt_succ_iff.mpr hn))
  intro n hn; rw [show C.path.levels.clock.factor = _ from hk.lengths,←h]; exact hW n hn
variable {ι:Type}[Fintype ι] {p m:ℕ→ℕ} {μ:ℕ→ℝ} {k P}
lemma toursSlim (h: G.Simple)(he:Fortified (ι:=ι) X B p P k m) (H:∀ d,0≤μ d)(hx:∀ d,2 ≤ p d)(ht:∀ i,m i ≤ (w.L i).val) (hJ:LocalRatio J) (U:Wait Z) (hhU:U.window=slim Z) :∃ W:Wait Z, ∃ P':∀ d,ι → Tapes.Panel d,U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ W.window=U.window ∧ (∀ d i,(P d i).arc=(P' d i).arc) ∧
    (∀ d i j,(P' d i).θ= (P' d j).θ ∧ ∀ k:ℕ, ((P' d i).bag k).era.coast.Q=((P' d j).bag k).era.coast.Q) ∧ ∀ χ, Clocked B O J W (fun d=> P' d χ) μ p k:=by
   choose W hv hw v z hV Ht hz hp using fun χ:ι=> retailers _ J (he.shops χ) ht (fun _=>1) (fun _ _=>1) (fun _ _=> zero_lt_one) hJ
   let P' := fun d χ=> curtain (P d χ) (v χ d) (hV χ d)
   have hh(χ) : PreStand X B (fun d=>P' d χ) k m:= recultivate X B (he.buys χ) (v χ) (hV χ) (hz χ)
   have hh' χ i j (hi:i∈ k j): Coul ((P' i χ).bag j) (p i) ∧ HLane ((P' i χ).bag j) (p i) (w.L j) ∧ reserveX (prepared X.kernel) (p i) j (P' i χ).θ (P' i χ).arc (w.L j).val:=by
      obtain ⟨⟨h1,h2,h3,h4⟩,⟨h5⟩,h6⟩:=he.lifts χ i j hi (w.L j) (ht j); exact ⟨⟨h1,h2,h3,h4⟩,⟨h5⟩,h6⟩
   have hyp (S:Finset ι) :∃ U':Wait Z, U.minLength ≤ U'.minLength∧ U.readyHere ≤ U'.readyHere ∧ U'.window=U.window ∧ ∀ χ∈ S,Clocked B O J U' (fun d=> P' d χ) μ p k:=by
      induction S using Finset.induction with
      | empty=> exact ⟨U,le_rfl,le_rfl,rfl,by simp⟩
      | insert i S hi IH =>
        obtain ⟨Y,h1,h2,h3,h4⟩:= IH; obtain ⟨U',ha,hb,hc,hd⟩:= glideSlim B O J (z i) (W i) μ p H hx h (hw i) hJ (hh i) ht (hh' i) (hp i) Y (h3.trans hhU)
        refine ⟨U',h1.trans ha,h2.trans hb,hc.trans h3,fun χ hi=> ?_⟩; rcases mem_insert.mp hi with rfl|hi; exact hd; exact printL B O J (h4 χ hi) U' ha hb hc.symm.le
   obtain ⟨V,ha,hb,hc,hh⟩:= hyp univ; exact ⟨V,P',ha,hb,hc,fun i j=> rfl,fun d i j=> (he.same d i j),fun i=> hh _ (mem_univ _)⟩
-- also raise wheel bound at activated levels
lemma w_bound_window (U:Wait Z)(h:G.Simple):∃ W:Wait Z,U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ W.window=U.window ∧ ∀ (A:Levels G),Paid W A→ ∀ i, W.readyHere (A.clock.J i) ≤ A.S.scale i→ Station.wheel A i ≤ A.clock.monitor i:=by
   have hp : Tendsto (Ship.preHat Z) atTop atTop := Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos h))
   choose x hx using fun j=> eventually_atTop.mp ((Next.Rank.Perch.bill_lo zero_lt_one).comp hp |>.eventually_ge_atTop ((w.L j).val:ℝ))
   let W:Wait Z:={U with readyHere:= fun j=>max (U.readyHere j) (x j) }
   refine ⟨W,le_rfl,fun j=>le_max_left ..,rfl,fun a h i hi=>?_⟩
   let j:= a.clock.J i; let s:= a.S.scale i
   have ht : Ship.preHat Z s=a.clock.hatBeta i:= by unfold Ship.preHat Calendar.hatBeta;rw [h.bar]
   rw [Atlas.fire_bill,wheel,h.lengths,clim,← ht]; exact hx j s ((le_max_right ..).trans hi)

end YM.PhysicalNext.InteractingRank.Soft

namespace YM.Pert.Dense
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec Supply PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open YM.MergeProof YM.MergeProof.East
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ}
variable {Θ: Sheet G} (B: MapPrices) {L:Rolls Θ}{E:Protection L}{H:Delays E}{Z:Bar H}


open StationPort
variable (O₀ : HaarBudget G) (J₀ : ChartRatio G) (U:Wait Z)
lemma slim_wait_for (hG:G.Simple) {u:ℕ→ℕ} (hR:Relay Θ B u) (hu:∀ i,u i ≤ (L.L i).val)(hJ : LocalRatio J₀)
    (hh : U.window = SharpGram.Dense.slim Z) :
    ∃ (W:Wait Z), Thicker U W ∧ W.window=U.window ∧ ∃ S:StationPort W B O₀ J₀,S.Certified := by
   obtain ⟨b,P,ht,hP,hK⟩:= hR.bulletin
   let z j:= ∑ i∈Finset.range (j+1),Accent.generator G i
   have ho(i):0 ≤ Accent.generator G i:=by unfold Accent.generator; positivity
   obtain ⟨V,P',hm,hr,h0,hT,hθ,hE⟩:= toursSlim B O₀ J₀ hG hK (H:=fun j=>show 0≤z j from Finset.sum_nonneg fun _ _=> ho _) (hx:=fun _=>Nat.le_add_left 2 _) hu hJ U hh
   obtain ⟨W,hv,hw,hp,he⟩:= w_bound_window V hG
   let S:StationPort W B O₀ J₀:=⟨P',z⟩
   refine ⟨W,⟨hm.trans hv,hr.trans hw,(hp.trans h0).symm.le⟩,hp.trans h0,S,⟨?_,?_,?_⟩⟩
   · intro i; simp only [StationPort.arc,S,← hT]; exact ht i
   · intro i j h; exact Finset.single_le_sum (f:=Accent.generator G) (fun _ _=> ho _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
   intro C hA B₀ hB hC hu d
   have h := clockwork (B:=B) (p:=trays) (μ:=z) (U:=W) (u:=u) (fun i=>printL B O₀ J₀ (hE i) W hv hw hp.symm.le) hP he C hA B₀ hB d
   have hl:= (staging (n:=trays d) (z:=z d) (P' d) B₀ hC O₀ J₀ hG 0 hu (hθ d 0))
   filter_upwards [h, hl] with k hK hL hx
   exact hL (hK hx).limit (hK hx).aisle

end YM.Pert.Dense
