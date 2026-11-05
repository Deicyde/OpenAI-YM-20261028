import YM.TraceExtension.Prom.Order.Offset
import YM.TraceExtension.Prom.Order.Porch
import YM.TraceExtension.Prom.Order.Vault
import YM.TraceExtension.Prom.Orion.Largo
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision Supply
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst  Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum Station Perch Tapes.West Atlas
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{X : Sheet G}(B:MapPrices){D: Rolls X}{b:Purse}{j u:ℕ}
section
private lemma arks (Q:Purse)(L:Side) (d:ℕ) (h:strideX X.kernel Q u j L)(hk:1 < (L.val:ℝ)): ∀ᶠ s in atTop, ∀ e≤Q.band,EarkSky (prepared X.kernel) u j d Q.taylor e L.val s := by
    let P:= prepared X.kernel; let t:=Q.taylor
    have he:= (eventually_all_finset (Finset.range (u+1))).2 fun n hn=> (Radian.gloss (h n (by have hh:= Finset.mem_range.mp hn;omega)) d).and
      ((Perch.bill_lo (show 0<Glimmer.fuel t n/4 from div_pos (Glimmer.fuel_real ..) (by norm_num))).eventually_ge_atTop (max (P.centers j) (P.centers (j-1))))
    filter_upwards [he,(Perch.bill_lo (by norm_num : 0<(1/4:ℝ))).eventually_ge_atTop (P.glass j d)] with s he hf e hE
    have ht n (hn : n ≤ u) := he n (Finset.mem_range.mpr (by omega))
    exact ⟨fun n hn=> (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (trainSky_at ..) (bump_s e _ hE _ hk s)) (by norm_num)).trans (ht _ hn).1,hf,fun n hn=> (ht _ hn).2⟩

private lemma caff_now (h:∀ i∈ farSky j,Roh X B j b u (D.L i)) (hC:Coul b u) (hp:2 ≤ u){δ:ℝ}(hd:0<δ)(hδ : δ ≤ b.era.coast.a)(hb:0≤ b.band):
    ∀ᶠ s:ℝ in atTop, ∀ n ≤ u,
      let T:=InteractingRank.trim b δ hd
      ∀ (y:ℝ)(m:ℕ), m ≤ bump (baseSky D j).val b.band s → Caff (G:=G) (vent T y) s m u n:=by
    let T:= InteractingRank.trim b δ hd
    let L:= baseSky D j
    have hx:= h (j-1) (mem_insert_of_mem (mem_singleton_self _))
    have hpT:= trimmed _ _ hd hδ (hx.reg j (mem_insert_self ..)).1
    have hl:HLane T u L:= ⟨hx.coast.run⟩
    filter_upwards [(eventually_all_finset (Finset.range (u+1))).2 fun n hn=> joys (show Coul T u from ⟨hC.tall,hC.flare,hC.pre,hC.far⟩) L hl hpT.bound.large hb hpT.credit (G:=G) hp (show n≤u by have ht:=mem_range.mp hn;omega)] with s he n hn T' y m hm
    have hv:=he n (mem_range.mpr (by omega))
    refine ⟨hv.horizon, (pow_le_pow_right₀ (pay_crest T.loan _) hm).trans hv.hikes,hv.flare,hv.lit,hv.bytes,hv.buys,hv.pastry,?_,hv.hiatus⟩
    exact ⟨hv.awaken.mark,hv.awaken.amplitude,hv.awaken.peak,hv.awaken.value⟩
private lemma rinksNow (b:Purse)(y s:ℝ){k l:ℕ}(h : k ≤ l)(ht : Racer b s l) : Racer (vent b y) s k:=by
    exact ⟨(pow_le_pow_right₀ b.running h).trans ht.log,(pow_le_pow_right₀ (pay_crest b.loan _) h).trans ht.one,(pow_le_pow_right₀ (pay_crest b.loan _) h).trans ht.two,ht.cone,(Nat.cast_le.mpr h).trans ht.family⟩
end
-- time warmth room.X.Consumer post binds X only via funds
structure ShelterSky (T: Levels G)(m:ℕ)(b:ℝ) : Prop where
   covers : AllowedSky T b m
   warm i (h:Station.widthSky T b m ≤ i) (hp:i ≤ m) : 3/4*clim T m ≤ clim T i ∧ clim T i ≤ clim T m
lemma far_members {T:Levels G}{b:ℝ}{m i:ℕ}(h: AllowedSky T b m)(ht:Station.widthSky T b m ≤ i)(he:i ≤ m) : T.clock.J i∈ farSky (T.clock.J m):=by
   simp only [farSky, mem_insert,mem_singleton]; have ht:= h.bracket i ht he; have hv:=T.fits.mono he; omega

-- expose geography reference: legacy.Waxroom can assume Claim.X tile; earned separately
def CapacitySky (D:Rolls X)(T:Purse)(W d s:ℝ)(O:HaarBudget G)(δ:ℝ)(Z:ChartRatio G)(h j p:ℕ): Prop:= ∀ (C:Family G) (B':Binding C), B'.prices=B→ ∀ k:ℕ,
   let A:= C.path.levels; let Y:=A.clock
   Y.kernel=X.kernel → Y.factor=D.L → Y.stage=X.profile → Y.J k=j → clim A k=s →
   (∀ T':Purse, CorridorSky A T'.band T' k → WaxroomSky A T' k) →
   ∀ y:ℝ, 0≤ y→ y ≤ T.band→ ShelterSky A k y → LegacyCostSky B' Z (-3) δ (vent T y) k h p O W d

set_option maxHeartbeats 660000 in
lemma office (hp:∀ i∈farSky j,Roh X B j b u (D.L i))(hJ: Coul b u)(hx:2≤u)(J:ChartRatio G)(h:LocalRatio J)(hb:0≤ b.band)(O:HaarBudget G)(z:ℝ)(n:ℕ)(hZ:0≤z): ∃ W d δ, ∃ he:0<δ, δ ≤ b.era.coast.a ∧ ∀ᶠ s in atTop,CapacitySky B D (InteractingRank.trim b δ he) W d s O z J u j n:=by
    obtain ⟨W,d,δ,hδ,hd,hV⟩:= allySky B hp hb J h
    let Q:= InteractingRank.trim b δ hδ; let L:= baseSky D j;let S:=X.profile
    have hk : j-1 ∈ farSky j:=mem_insert_of_mem (mem_singleton_self _); have hj:j∈farSky j:=mem_insert_self ..
    have he': Roh X B j b u L:= hp (j-1) hk; have ht0 : Regiment Q (S j) L:=trimmed b δ hδ hd (he'.reg j hj).1
    have hu(k i)(hk:k∈farSky j)(hi:i∈farSky j) : Steel Q (S i) (D.L k):= ⟨((hp k hk).reg i hi).2.1,((hp k hk).reg i hi).2.2⟩
    have he(k)(hk:k∈farSky j):= (hp k hk).merit k hk k hk le_rfl
    let f(i):= D.L i
    have hp (i)(hi : i∈ farSky j): ∀ᶠ s in atTop,
        (∀ x∈Set.Icc (s/2) s,∀ y∈Set.Icc (s/2) s,∀ P R : BudgetPoint,P.B=walls y→R.B=walls x→∀ n : ℕ,n ≤ u → TimeBand Q.era Q.goal (f i) P R x y s n) ∧
        SlotPrice Q z G (S i) L s ∧ (Station.ticket O (S i) u ≤ Real.log (Vac.Numbers.P s)/(16*u))∧ Costs (S i) G s:=by
       have hH : Tendsto (fun s:ℝ=> Real.log (Vac.Numbers.P s)/(16*u)) atTop atTop:= by
          have ht : (0:ℝ)<↑u:=by exact_mod_cast (show 0<u from lt_of_lt_of_le zero_lt_two hx)
          exact (Real.tendsto_log_atTop.comp (show Tendsto Vac.Numbers.P atTop atTop from Real.tendsto_exp_atTop.comp Perch.boil_rate)).atTop_div_const (by positivity)
       have hB:= (he i hi).1
       filter_upwards [pedestals Q.era (e:=u) Q.goal (f i) hB.ceiling.1 hB.ceiling.2 hB.credits.1 hB.credits.2,annually L z (trimmed b δ hδ hd (he'.reg i hi).1) (G:=G) hZ,hH.eventually_ge_atTop (Station.ticket O (S i) u), prediction G (S i)] with s ht hv hB hD
       exact ⟨fun x hp y he P R hx ht' n hn=> ht n hn x hp y he P R hx ht', hv,hB,hD⟩
    have pairs (i : ℕ × ℕ) (hi : i∈adjoining j): ∀ᶠ s in atTop,
        let k:= i.1;let l:=i.2
        (∃ v:ℝ,0≤v ∧ stretch L.val b.band s ≤ stretch (f k).val v s ∧
         ∀ y:ℝ,TimingSky (initials B S X.kernel k l) J k (f k) (vent Q y) v W d s ∧ PostsSky J B S X.kernel k l (vent Q y) (f k) W d s)∧
         ∀ P R : BudgetPoint,∀ x ∈ Set.Icc (s/2) s,∀ y∈Set.Icc (s/2) s,P.B=walls y → R.B=walls x→ P.B ≤ 2*R.B → P.supportExponent=(S k).supportExponent→ R.supportExponent=(S l).supportExponent → Lease (D.L k) P R (load Q.era) (acres Q x y) (Line Q.era Q.goal 0 s) (tinder Q s) (kinetics s) (gas Q.era.coast y):=by
       obtain ⟨h1,h2⟩:= mem_filter.mp hi; obtain ⟨h1,h3⟩:= mem_product.mp h1
       obtain ⟨v,hv,hQ⟩:= hV i.1 h1 i.2 h3 h2
       filter_upwards [hQ, stipendFeastsSky Q _ (f i.1) (hu _ _ h1 h1) _ (hu _ _ h1 h3)] with s hs ht
       exact ⟨⟨v,hv,hs⟩,ht⟩
    -- end use even i where p=0. hT etc
    have hT:strideX X.kernel Q u j L:= he'.commission
    have hLarge:= ht0.bound.large
    refine ⟨W,d,δ,hδ,hd,?_⟩
    filter_upwards [(eventually_all_finset (farSky j)).2 hp,(eventually_all_finset (adjoining j)).2 pairs,(caff_now B (b:=b) ‹_› hJ hx hδ hd hb), arks Q L n hT hLarge,
        on_time _ hLarge Q.era u,(bill_lo (LiftMark.shade_pos Q.taylor)).eventually_ge_atTop ((prepared X.kernel).centers j),sizes_CSky Q.era.coast.Q Q.horizon (L:=L.val) ht0.cockpit ht0.ability ht0.radius (G:=G)] with s hv hy hC hE hF hL hR
    intro C B' HAr k A Y hK hw hS hg ht hW y hY HY hN
    have hl (i): A.params i=S (A.clock.J i):= congr_fun hS _
    let U:= vent Q y; have hz : U.band=y:=rfl
    have hN':AllowedSky A U.band k:=hN.covers
    have hfP(i)(h : Station.widthSky A U.band k ≤ i) (hp:i ≤ k): clim A i ∈ Set.Icc (s/2) s:=by
        have hh:=hN.warm i h hp
        rw [← ht];exact ⟨by linarith only [hh.1,A.fits.delayed k],hh.2⟩
    have hf': Y.J k=j:= hg
    subst j
    have h : wheelSky A k= (L.val:ℝ):= by
       unfold wheelSky leastL; rw [show A.clock.factor=D.L from hw]; unfold L baseSky; rw [min_eq_right]; exact D.grow (Nat.sub_le ..)
    let lifeF:= hv _ hj|>.2.1
    have hLz : SlotPrice Q z G (A.params k) L (clim A k):= by rw [ht,hl]; exact lifeF
    let a:= middleSky A U.band k; have hQ : k-a ≤ bump L.val Q.band s:= by
        have hQs := hN'.full; rw [h,show A.clock.hatBeta k=s from ht] at hQs; exact hQs.trans (bump_s _ _ HY _ hLarge s)
    have hX : CorridorSky A U.band U k:= by
       have ha:Racer U (clim A k) (k-a):= by apply rinksNow Q y _ _ hLz.forward; rw [ht]; exact hQ
       obtain ⟨a₄,b₄,c,d,e,w,v,h',hJ'⟩:= hLz.cost
       exact ⟨hN.covers,ha,⟨a₄,b₄,c,d,e,w,v,h',hJ'⟩,fun i he hv=> ht.symm ▸ hfP i he hv⟩
    have hTar i (hi:Station.widthSky A U.band k ≤ i)(hx:i ≤ k): A.clock.J i∈ farSky (A.clock.J k):= far_members hN' hi hx
    have hin i (hi:Station.widthSky A U.band k ≤ i)(he:i < k): (A.clock.J (i+1),A.clock.J i) ∈ adjoining (Y.J k):= mem_filter.mpr ⟨mem_product.mpr ⟨hTar _ (hi.trans (Nat.le_succ i)) he,hTar i hi he.le⟩, A.fits.mono (Nat.le_succ i)⟩
    change LegacyCostSky B' J _ _ U k _ _ _ _ _
    refine ⟨⟨hLz.fees,hLz.money,hLz.order,hLz.asteroid,hX,?_⟩,?_,?_,?_,?_,?_,?_⟩
    · intro i h; have hf:=hLz.gauge i h; exact ⟨hf.mark,hf.amplitude,hf.peak,hf.value⟩
    · let m:=Station.widthSky A U.band k
      have hp:= (widerSky ..).trans (beforeSky A U.band k); refine ⟨⟨hN',?_⟩,?_,fun i hV hx=>hX.court i hV (hx.trans (beforeSky ..))⟩
      · unfold Ship.pot Calendar.monitor; rw[hl,show A.clock.hatBeta k=s from ht]; exact (hv _ (hTar m le_rfl hp)).2.2.1
      rw [h,show A.clock.hatBeta k=s from ht]; exact hF
    · refine ⟨?_,fun i hi hk=>?_,(fun p=> hR A p k h ht y hN' hfP),hW U hX,?_,fun i hi he=> (hN.warm i hi he).1,?_⟩
      · unfold optics; rw [show _= X.kernel from hK]; change _ ≤ LiftMark.tin (Atlas.clim A k) _; rw [ht]; exact hL
      · obtain ⟨a,v,w,hV⟩:= (hy _ (hin i hi hk)).1; intro A'; dsimp only [A']; rw [HAr,show C.path.levels.clock.kernel=_ from hK,show C.path.levels.clock.stage=_ from hS,show C.path.levels.clock.factor=_ from hw, show clim C.path.levels k=s from ht]
        exact (hV y).2
      · intro i hp hQ; unfold Paint.TableReady; rw [hl]; exact (hv _ (hTar i hQ hp)).2.1.dating _ (hfP i hQ hp)
      · intro i hi hZ; have h':= (hy _ (hin i hi hZ)).2
        intro x y' t P R he hc hd hl₁ hl₂; rw [show C.path.levels.params (i+1)=_ from hl (i+1)] at hl₁; rw [show C.path.levels.params i=_ from hl i] at hl₂
        rw [show C.path.levels.clock.factor=D.L from hw]; change Lease _ _ _ _ _ (Line _ _ 0 (clim A k)) (tinder _ (clim A k)) (kinetics (clim A k)) _; rw [ht]; exact h' P R x (hfP i hi hZ.le) y' (hfP (i+1) (hi.trans (Nat.le_succ i)) hZ) he hc hd hl₁ hl₂
    · refine ⟨fun i hi he=> ?_, fun i hi hk=>?_⟩
      · rw [hl, show Atlas.clim C.path.levels k=s from ht]; exact (hv _ (hTar i hi he)).2.2.2
      obtain ⟨b,hb,hH,hV⟩:= (hy _ (hin i hi hk)).1
      have hσ:k-i ≤ stretch L.val Q.band s:=by
         let w:=Station.widthSky A U.band k; have hμ := hN'.shift
         rw [h,show A.clock.hatBeta k=s from ht] at hμ; change a-w≤_ at hμ; change w ≤ i at hi
         change k-i ≤ bump _ _ _+more _ _; have hx : w ≤ a:= widerSky ..; have he : a ≤ k:= beforeSky ..; omega
      change ∃ b:ℝ, 0 ≤ b ∧ k-i ≤ stretch ((C.path.levels.clock.factor (C.path.levels.clock.J (i+1))).val:ℝ) b (clim C.path.levels k) ∧ _
      rw [show C.path.levels.clock.factor=D.L from hw,show Atlas.clim C.path.levels k=s from ht]
      refine ⟨b,hb,hσ.trans hH,?_⟩
      unfold tell; rw [HAr,show C.path.levels.clock.kernel=_ from hK,show C.path.levels.clock.stage=_ from hS]; exact (hV y).1
    · rw [show C.path.levels.clock.kernel=_ from hK, show wheelSky C.path.levels k=_ from h,show Atlas.clim C.path.levels k=s from ht]; exact hE y HY
    · intro n hn; rw [show Atlas.clim C.path.levels k=s from ht]; exact hC n hn y _ hQ
    intro n hn i hi hk x hx y' hΨ P R h1 h2
    simp only [show Atlas.clim C.path.levels k=s from ht] at hx hΨ
    rw [show C.path.levels.clock.factor=D.L from hw,show Atlas.clim C.path.levels k=s from ht]; exact (hv _ (hTar (i+1) (hi.trans (Nat.le_succ _)) hk)).1 x hx y' hΨ P R h1 h2 n hn
end YM.PhysicalNext.InteractingRank.Soft
