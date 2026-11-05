import YM.MergeProof.West.Bera
import YM.MergeProof.West.Lys

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis West Pump
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} (B : MapPrices)
variable (O : HaarBudget G) (J : ChartRatio G) {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
-- One panel family on actual old V any substage with Window. A-independent property tall.Price schedule independent C with threshold passive at ANY.C.PATH. Epoch β freeze.
structure Clocked (B:MapPrices)(O:HaarBudget G)(J:ChartRatio G) (U : Wait Z) (P:∀ d,Tapes.Panel d)(m:ℕ→ℝ)(p:ℕ→ℕ)(k:ℕ→Finset ℕ):Prop where
    rent : ∀ C : Family G, Paid U C.path.levels → ∀ K:Binding C,K.prices=B→∀ᶠ k₀ in atTop,
       let A:= C.path.levels; let j:=A.clock.J k₀
       X.first<j → U.readyHere j ≤ A.S.scale k₀ → U.window j (A.S.scale k₀) ≤ k₀ → (∀ i,k₀-U.window j (A.S.scale k₀) ≤ i → i ≤ k₀ → A.clock.J i=j) →
       ∀ i∈k j, ∃ l r, LegacyCost K J (-3) (m i) ((P i).bag j) k₀ (p i) i O l r
lemma printL {k P m p U} (h:Clocked B O J (Z:=Z) U P m p k)(W:Wait Z)(hs:U.minLength ≤ W.minLength)(hv:U.readyHere ≤ W.readyHere)(ht:U.window ≤ W.window): Clocked B O J W P m p k:=by
   constructor; intro C hc K hp
   filter_upwards [h.rent C (retains_budget hs (fun j=>⟨hv j,ht j⟩) hc) K hp] with i hj
   intro A j he hk hK hJ; let a:= A.S.scale i
   exact hj he ((hv j).trans hk) ((ht j a).trans hK) (fun k hk hℓ=> hJ k (le_trans (Nat.sub_le_sub_left (ht j a) i) hk) hℓ)
lemma glide {P k M} (d : ℕ→ℕ→ℝ) (wL : ℕ→ℝ) (m : ℕ→ℝ)(p:ℕ→ℕ) (hm : ∀ d,0 ≤ m d)(hx:∀ d,2 ≤ p d) (simple : G.Simple)
    (hw : ∀ i,0<wL i) (hJ : LocalRatio J) (hs : PreStand X B P k M) (hl : ∀ j,M j≤ (w.L j).val)
    (he:∀ i j,i∈ k j→ Coul ((P i).bag j) (p i) ∧ HLane ((P i).bag j) (p i) (w.L j)∧ reserveX (prepared X.kernel) (p i) j (P i).θ (P i).arc (w.L j).val)
    (hp : ∀ i j,i∈ k j →∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) ((P i).bag j) (wL j) (d i j) s)
    (U : Wait Z) : ∃ (W : Wait Z), U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ Clocked B O J W P m p k:= by
  obtain ⟨V,hL,hG,hV⟩:= served Z simple O U p (fun i=>(P i).arc) (fun j i=> ((P i).bag j).era) k (fun i=> by have h:=hx i;omega) (fun j=> by linarith only [(P j).huge,Nat.cast_nonneg (α:=ℝ) j]); have hδ:=hp
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
  choose t' Ht using fun j=> eventually_atTop.mp (hh j)
  let U': Wait Z:= { V with readyHere:= fun j=>max (V.readyHere j) (t' j) }
  obtain ⟨W,hW,hr,hX⟩:= tabled simple U' k O (fun i j=> (P i).bag j) m (fun i=> (P i).arc) (fun i=> by linarith only [ (P i).huge,Nat.cast_nonneg (α:=ℝ) i]) hm (fun i j=> (P i).factor j) (fun i j hv=> (hp i j hv).1)
  have hg j: V.readyHere j≤W.readyHere j ∧ t' j≤W.readyHere j:= max_le_iff.mp (hr j).1
  refine ⟨W,hL.trans hW,fun j=> (hG j).1.trans (hg j).1,fun j s=>((hG j).2 s).trans ((hr j).2 s),⟨fun C hk K hK=>?_⟩⟩
  filter_upwards [vault_size C.path.levels simple] with a hT
  intro A j hx' hY hw hz i hj
  let y:= Ship.preHat Z (C.S.scale a); let L:= A.clock; let P':=(P i).bag j; let v:= (P i).patronize C (hm i)
  obtain ⟨⟨hf,hδ⟩,⟨hC,hρ⟩,hAdap,hW⟩ := Ht j _ ((hg j).2.trans hY) i hj
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
  have hv:= hV j i hj; let β:= (P i).arc
  have he1: Charge A P'.band a (p i) O P'.era:=by
    rw [show P'.band=β from (P i).factor j]; let s:= C.S.scale a; have hw': V.window j s≤ W.window j s:= (hr j).2 _
    exact held_at V A (retains_budget (show V.minLength≤ W.minLength from ‹U'.minLength≤W.minLength›) (fun j=>⟨(hg j).1,(hr j).2⟩) hk) hx' rfl ((hg j).1.trans hY) (hw'.trans hw) (fun i hh hk=> hz i (le_trans (Nat.sub_le_sub_left hw' a) hh) hk) O (p i) β P'.era hv simple
  have ht : wheel A a=(w.L j).val:=by unfold wheel; rw [hk.lengths]
  refine ⟨_,_,hf', he1,hl',?_,?_,?_,?_⟩
  · constructor; change Timing (initials K.prices A.clock.stage A.clock.kernel _ _) J _ _ P' _ _ _
    rw [hK, show A.clock.J a=j from rfl,hk.stage,hk.kernel,hk.lengths]; exact h ▸ hδ
  · change Eark (prepared A.clock.kernel) (p i) j i P'.taylor P'.band (wheel A a) (clim A a)
    rw [show P'.band= _ from (P i).factor j, show P'.taylor=_ from (P i).stable j,hk.kernel, ht,←h]; exact hC
  · intro n hn; change Caff P' (clim A a) (a - middle A P'.band a) (p i) n; rw [he1.allot.permitted.full,height,ht,← h,show A.clock.hatBeta a=y from h.symm]; exact hρ n (mem_range.mpr (Nat.lt_succ_iff.mpr hn))
  intro n hn; rw [show C.path.levels.clock.factor = _ from hk.lengths,←h]; exact hW n hn
end YM.PhysicalNext.InteractingRank.Soft
