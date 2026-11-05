import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Royal
/-!
# Sale at joint wait level (from stage-1 Opacity.Pergola, additional
requirements at THAT receipt)

Include same votes while buying. Trim only after L. Paid on these wait gates
must come from the family -- do not buy fresh Wait and expect F value to
match. Keep all price specs on walls/heaters at the same Late couplings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} (B : MapPrices)
variable (O : HaarBudget G) (J : ChartRatio G) {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
open Pump
structure Vents {C : Family G} (B : Binding C) (v : Purse) (J : ChartRatio G) (l d : ℝ) (i : ℕ):Prop where
  great : let L:=C.path.levels.clock; let j:=L.J i
          Timing (initials B.prices L.stage L.kernel j j) J j (L.factor j) v l d (clim C.path.levels i)
lemma revolving {P k M} (d : ℕ→ℕ→ℝ) (wL : ℕ→ℝ) (m : ℕ→ℝ) (hm : ∀ d,0 ≤ m d) (simple : G.Simple)
    (hw : ∀ i,0<wL i) (hJ : LocalRatio J) (hs : PreStand X B P k M) (hl : ∀ j,M j≤ (w.L j).val)
    (hp : ∀ i j,i∈ k j →∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) ((P i).bag j) (wL j) (d i j) s)
    (U : Wait Z) (hP : ∀ d, ∃ᶠ j in atTop,d∈k j):
    ∃ (W : Wait Z), U.minLength ≤ W.minLength ∧ (∀ i,U.readyHere i ≤ W.readyHere i ∧ ∀ s,U.window i s ≤ W.window i s) ∧
      (∃ a, Paid W a) ∧ ∀ C : Family G, Paid W C.path.levels → ∀ K : Binding C, K.prices=B → ∀ i : ℕ,∃ᶠ j in atTop,
       let v:= (P i).patronize C (hm i); let t:= C.path.levels.clock.J j
       Tender v j ∧ Metering v O j (-3) ∧ ShowHours J K (v.current j) j (-3) (wL t) (d i t) ∧ Vents K (v.current j) J (wL t) (d i t) j:= by
  have hδ := hp
  have hp i j (h : i∈ k j) := hs.reg i j h|>.2 (w.L j) (hl j)
  have hV : Tendsto (Ship.preHat Z) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos simple))
  choose! u hD hF using fun i j (h:i∈k j)=> polite J B X.profile X.kernel j ((P i).bag j) hJ (w.L j) (hs.potion _ _ h _ (hl j)).1 (wL j) (hw j)
  have hh (j) := (eventually_all_finset (k j)).2 (fun i hi=> (hV.eventually ((hF i j hi).and (hδ i j hi))).and (hV.eventually (clearing (prepared X.kernel) (hp i j hi).2 i)|>.and (late _ Z _ (hs.potion i j hi _ (hl j)).2 simple (by rw [(P i).factor j];linarith only [(P i).huge,Nat.cast_nonneg (α:=ℝ) i]))))
  choose t ht using fun j=> eventually_atTop.mp (hh j)
  let U': Wait Z:= { U with readyHere:= fun j=>max (U.readyHere j) (t j) }
  obtain ⟨W,hW,hr,hX⟩:= tabled simple U' k O (fun i j=> (P i).bag j) m (fun i=> (P i).arc) (fun i=> by linarith only [ (P i).huge,Nat.cast_nonneg (α:=ℝ) i]) hm (fun i j=> (P i).factor j) (fun i j hv=> (hp i j hv).1)
  have hg j: U.readyHere j≤W.readyHere j ∧ t j≤W.readyHere j:= max_le_iff.mp (hr j).1
  refine ⟨W,hW,fun j=>⟨(hg j).1,(hr j).2⟩,Wait.ready W simple,fun C hk K hK i=>?_⟩
  apply frequently_atTop.mpr; intro k'
  let A:= C.path.levels; let L:=A.clock
  obtain ⟨t,ht'⟩:= eventually_atTop.mp (vault_size A simple)
  obtain ⟨j,hj,hv,hψ⟩:= ((hP i).and_eventually ((eventually_gt_atTop (L.J (max t k'))).and (eventually_gt_atTop X.first))).exists
  obtain ⟨a,hY,hw,hL⟩:= hk.run j hψ.le
  have hx:L.J a=j:= hL a (by omega) (by omega)
  obtain ⟨⟨hf,hδ⟩,hC,hAdap⟩ := ht j _ ((hg j).2.trans hY) i hj
  let v:= (P i).patronize C (hm i)
  obtain ⟨ho,hG⟩:= affords simple O v W hk (hX i j hj) hψ hx hY hw (fun i h hi=>hL _ h (by omega))
  have h : Ship.preHat Z (C.S.scale a)=clim A a:= by unfold Ship.preHat; change _=Calendar.hatBeta _ _; rw [Calendar.hatBeta,hk.bar]
  have ht : v.current a = (P i).bag j:=by unfold Cohesion.current;rw [show C.path.levels.clock.J _=_ from hx]; rfl
  have ha : max t k' ≤ a:= (lt_of_not_ge (fun h=>not_lt_of_ge (hx ▸ A.fits.mono h) hv)).le
  refine ⟨a, (le_max_right ..).trans ha,?_,ho,⟨?_,hG,ht' a ((le_max_left ..).trans ha) _ ho.cost.coup,?_,?_⟩,?_⟩
  · unfold Tender; rw [wheel,show C.path.levels.clock.factor=_ from hk.lengths, show C.path.levels.clock.J _=_ from hx,show C.path.levels.clock.kernel=_ from hk.kernel]; exact h ▸ hC
  · change Ceremony K J (v.current a) a _ _; unfold Ceremony; rw [hK, ht, show C.path.levels.clock.J _= j from hx, show C.path.levels.clock.kernel=_ from hk.kernel, show C.path.levels.clock.stage=_ from hk.stage, show C.path.levels.clock.factor=_ from hk.lengths]; exact h ▸ (Pump.proclaimed B X hδ.onRoad hf)
  · intro s hs hX'; have hi := ho.cost.coup
    change Station.width A (v.current a).band a≤ s at hX'
    have hr : C.path.levels.clock.J s=j:= (hi.heft.plateau s hX' hs).trans hx
    have hD : C.path.levels.params s=X.profile j:= by change A.clock.stage (C.path.levels.clock.J s)=_; rw [show A.clock.stage=_ from hk.stage,hr]
    have hw:= hi.court s hX' hs
    change Paint.TableReady C s (-3) (load (v.current a).era) (v.current a).era.coast.a
    unfold Paint.TableReady; rw [ht,hD]
    have hp:SlotPrice ((P i).bag j) (m i) G (X.profile j) (w.L j) (clim A a):= h ▸ (hX i j hj).2 _ hY
    exact hp.dating _ hw
  · refine (show Waltz (G:=G) (v.current a) (C.path.levels.params a) _ _ from ?_)
    unfold Levels.params Calendar.params; rw [show C.path.levels.clock.J _ = j from hx,ht, show C.path.levels.clock.stage=_ from hk.stage, show C.path.levels.clock.factor=_ from hk.lengths]
    exact h ▸ hAdap
  constructor; change Timing (initials K.prices A.clock.stage A.clock.kernel _ _) J _ _ (v.current a) _ _ _
  rw [ht,hK,hx,hk.stage,hk.kernel,hk.lengths]; exact h ▸ hδ
-- collect publication for active stage. Don't advertise off-stage positive Standing. d>0 not actually needed to use schedule gate outside Active.E.era
lemma retailers {P k M} (h : Shops B X k P M) (hv : ∀ i,M i ≤ (w.L i).val) (u : ℕ→ℝ) (K : ℕ→ℕ→ℝ)
    (hp : ∀ i j,0<K i j) (ht : LocalRatio J):∃ (W : ℕ→ℝ), u≤ W ∧ (∀ i,0<W i) ∧
      ∃ (v d : ℕ→ℕ→ℝ),∃ (hw : ∀ i j,0<v i j), v≤K∧(∀ i j, v i j ≤ ((P i).bag j).era.coast.a) ∧
        ∀ i j,i∈ k j →∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) (((curtain (P i) (v i) (hw i)).bag j)) (W j) (d i j) s:= by
  have hh j : ∀ᶠ W in atTop,∀ i∈k j,∃ a d, 0 < a ∧ 0 < d ∧
      ∀ (d' δ : ℝ),d≤d' → ∀ (hp :0<δ),δ ≤ a → ∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) (InteractingRank.trim ((P i).bag j) δ hp) W d' s:= by
    exact (eventually_all_finset ..).mpr fun i hi=> (h.poles j _ (hv j) i hi).mono (fun j h=> h _ ht)
  choose W hW hw using fun j=> ((hh j).and ((eventually_ge_atTop (u j)).and (eventually_gt_atTop (0:ℝ)))).exists
  let μ (i j:ℕ):= min (K i j) ((P i).bag j).era.coast.a
  have he i j:0<μ i j:= lt_min (hp i j) ((P i).bag j).era.coast.posA
  have hh (i j): ∃ v d : ℝ,∃ ζ:0<v,v ≤ μ i j ∧ (i∈k j →∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) (InteractingRank.trim ((P i).bag j) v ζ) (W j) d s):=by
    by_cases h:i∈ k j
    · obtain ⟨a,d,h,h₁,H⟩:=hW j i h
      let v:=min a (μ i j); exact ⟨v,d,lt_min h (he i j),min_le_right ..,fun _=>H d _ le_rfl _ (min_le_left ..)⟩
    exact ⟨μ i j,1,he i j,le_rfl,fun he=>(h he).elim⟩
  choose v d hv he ht using hh
  exact ⟨W,(fun i=> (hw i).1),(fun i=>(hw i).2),v,d,hv,(fun i j=> (he i j).trans (min_le_left ..)),(fun i j=> (he i j).trans (min_le_right ..)),ht⟩
end YM.PhysicalNext.InteractingRank.Soft
