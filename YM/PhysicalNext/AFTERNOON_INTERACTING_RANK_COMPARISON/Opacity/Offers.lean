import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Gardener
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Mezzanine
/-!
# Full Opacity production at weak post (foliage branch).

Records chosen before output Rep post quantum-cost grant. Bound to canonical
χ.d profiles if chosen; permit operator universal. `Mesa` exposes for ALL
output representations with this BudgetPoint, since not relying on its E. Not
asserting `Resin` on that Type. `Profile` theater propagates existential. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Coffer Grid Next.Rank Perch Flux Vale Tapes EndpointLoadF16.DetLong
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x y W a e L C u d ε η g b s : ℝ} {p q : Pilot G S x} {v : Dyed G S} {J : ChartRatio G}
local notation "H0"=>retime x
-- Sensed arrivals (scale updates below purchased across all Ξ)
structure Seeks (v : Dyed G S) (P : Teller G) (d x : ℝ):Prop where
  funS : P.Funds S v.things
  chosen : v.arc=d*fiery G (retime x) S.patch.L
  paths : v.things.up=v.source.path
  clips : v.things.high=v.source.clip
  bp : v.bp.threshold=temp (retime x)
  period : 100*(1+radiusB (retime x)) ≤ c.val
  large : Bid.Larger (G:=G) S
  alongside : ∃ H K, Aff.Alongside H K v.things
  law : ∃ Γ δ w,v.source.Lawful P.top.width P.top.paths Γ δ w ∧ Γ ≤ betaF G (retime x) S.patch.L^(1/8:ℝ) ∧ δ ≤ retime x^(-(1/2):ℝ)
  head : v.source.p.supportExponent=P.top.supportExponent
  walls : v.bp.B=Perch.walls x ∧ v.source.p.B ≤2*v.bp.B
  beta : v.source.beta∈ Set.Icc (betaF G x S.patch.L/2) (2*betaF G x S.patch.L)
  flag : v.source.p.threshold=Paint.phase (betaF G x S.patch.L)

lemma hoops (P : Teller G) (J : ChartRatio G) (hJ : LocalRatio J) (D : Patch) (m d W t : ℝ) (hw : 0<W) (h : ∀ᶠ x in atTop,Wax.Peaking P x W m (2*d) D.L 200) (H : ∀ᶠ x in atTop, Granite J P D W d ε x) (e : ℝ) : ∀ᶠ s in atTop,
    ∀ x∈Set.Icc (s/2) s,∀ {c f : Side} (S : StepData c f) (v : Dyed G S), S.patch=D → v.ratio=J → Seeks v P d x → Footprint.reserve v.source.p.supportExponent e (Footprint.conversion S.ratio 1) t →
    Helps v P W d x m t e ∧ v.source.beta ≤ 4*(retime x):= by
  obtain ⟨r,hr⟩:= eventually_atTop.mp (h.and ((crossfade G D.L).and (burst_limit.and (tall_limit.eventually (H.and (((Rates.slow G D).eventually (ge_mem_nhds zero_lt_one)).and ((Wax.reserve_lane G D.L P.top.clip.relaxation P.top.clip.radius_pos).and ((small_span D).and (Work.E01.radiusB_tendsto.eventually_ge_atTop 2)))))))))
  filter_upwards [Perch.half.eventually_ge_atTop r, risibleQ,Perch.half.eventually_ge_atTop (G.slopeConstant*Real.log D.L.val),Perch.half.eventually_ge_atTop 1] with s hr' ht hX hw' x hx c f S v hS hv hz h₀
  subst D J
  have h := hr x (hr'.trans hx.1); obtain ⟨hM,hc,hB,ht',hy,hL,hs,hr⟩:=h
  let T:=v.things; let z:=fiery G (retime x) S.patch.L; let t' := v.source.p.threshold; let Y:=betaF G x S.patch.L
  have hF : v.source.p.threshold ∈ Set.Icc (z/2) (2*z):= hz.flag.symm ▸ hc.2.2
  have he : 1 ≤ x:= hw'.trans hx.1
  have h' : x ≤ Y:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hY:Y≤ 2*x:= by unfold Y betaF; linarith only [hX.trans hx.1]
  have hv: v.source.beta ≤4*(retime x):= le_trans hz.beta.2 (by change 2*Y≤_; linarith only [hY,hB.1])
  have hh (V : Tube G S) (h:P.Funds S V)(hp : 100*(1+radiusB (retime x)) ≤ c.val):= (ht'.permits.eligible S V rfl hp h).1
  have hK := ht'.permits
  obtain ⟨g,δ,w,hA,hQ⟩:=hz.law
  have hu : z ≤ 1 := by simpa only [Rates.allowance,Rates.pieces,pow_zero,mul_one,one_mul,pow_one] using hy
  have he':Chips v P W (retime x):=⟨⟨_,_,_,_,_,hA⟩,hz.chosen.symm ▸ hK.boom,hz.chosen.symm ▸ hK.size,hz.chosen.symm ▸ hK.ride,hz.paths,hz.clips,hJ,hh _ hz.funS hz.period,hw,hc.2.1,hu,hz.bp,lt_of_lt_of_le (half_pos (zero_lt_one.trans_le (he.trans h'))) hz.beta.1⟩
  refine ⟨⟨he',hz.large,hz.period,hz.alongside,hz.chosen,hz.beta,hz.flag,hF,?_,h₀,?_,hz.law,?_⟩,hv⟩
  · rw [hz.flag]; exact launched P hM rfl ht'.gallery (by omega) hs hK.boom (by linarith only [hK.boom,hK.ride]) hh
  · exact ⟨hz.walls.1.trans_le (wall_mono he (he.trans hB.1) hB.1),hz.walls.2,(ht _ _ hz.walls.1 hx).1⟩
  have he : v.source.clip=P.top.clip:= hz.clips.symm.trans hz.funS.high
  rw [he]; refine ⟨Work.E04.capacity P.top,Work.E04.lanes (he ▸ hA.paths) le_rfl v.source.p.threshold_pos.le one_pos (Work.E04.parent_separation _) ⟨hL.1,fun i hi=> hL.2 _ ?_⟩⟩
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hF.1 (Real.exp_pos _).le) hi

structure Mesa (J : ChartRatio G) (i : Purse) (P : Teller G) (D : Patch) (W d s : ℝ): Prop where
  march (x : ℝ) : x∈Set.Icc (s/2) s → March J P D W d (retime x)
  arrange {x:ℝ} (hx : x∈Set.Icc (s/2) s) {c f : Side} (S : StepData c f) (v : Dyed G S) : S.patch=D → v.ratio=J → Seeks v P d x →
    ∃ (H : Draft v P (retime x) W) (M : Plate v (retime x) W),∃ (hw : 0<W) (he : 0<fiery G (retime x) S.patch.L),∀ (o c' Γ δ w) (hR : v.source.Lawful o c' Γ δ w) (Q : Rep G c) (hq : Q.p=v.bp) (hT : 25*radiusB (retime x)+30≤ Q.p.B),
      let O:= Orchard.canopy S; let z:= fun j=>shiftZ O hq.symm (sprouting H M O j); let y:= betaF G x S.patch.L
      Opacity v.source Q z (L:=foliage H) H.enrolled hT hR (v.loading (retime x)) (J:=J) (D:=v.chi.profiles G S (retime x) W hw he) (load i.era) (acres i x y) (Line i.era i.goal 0 s) (tinder i s)
private lemma cared (i : Purse) (h : Helps v P W d x a u (Docking.increment (load i.era+1))) (H : Draft v P H0 W) (Q : Plate v H0 W) (hv : ∀ R:Rep G c,∀ hp:R.p=v.bp, Holdings (L:=Vale.foliage H) R (fun j=> shiftZ (Orchard.canopy S) hp.symm (sprouting H Q (Orchard.canopy S) j)) v.things (acres i x (betaF G x S.patch.L)) (Line i.era i.goal 0 s) (load i.era+1) (tinder i s))
    (he : Physical.Certified S v.things H0 g C η b) :
     let ht:= h.hats; ∀ (o c' Γ δ w) (hR : v.source.Lawful o c' Γ δ w) (R : Rep G c) (hq : R.p=v.bp) (hT : 25*radiusB (retime x)+30≤ R.p.B),
      let O:= Orchard.canopy S; let z:= fun j=>shiftZ O hq.symm (sprouting H Q O j); let y:= betaF G x S.patch.L
      Opacity v.source R z (L:=foliage H) H.enrolled hT hR (v.loading (retime x)) (J:=v.ratio) (D:=v.chi.profiles G S (retime x) W ht.heated ht.lives) (load i.era) (acres i x y) (Line i.era i.goal 0 s) (tinder i s):= by
  intro ht o c' Γ δ w hR R hq hT O z y; have hm(B:BudgetPoint)(hB:B=v.bp):
      let p:= fun i=> shiftZ O hB.symm (sprouting H Q O i)
      BodyGrant v.things v.source (foliage H) (v.chi.profiles G S (retime x) W ht.heated ht.lives) v.ratio B.threshold p (fun a=> (↑(v.loading (retime x) a):ℂ)) ∧ ∀ i A k V y,Display.Sew.Sound ((p i).weight A k V y):= by
    intro p; subst B; refine ⟨land H Q O ht.tall ht.heated ht.lives h.flag.1 he ht.paths ht.clips ht.data ht.beta,fun i A k V y=>?_⟩
    unfold p shiftZ; rw [Vale.contracts]; exact vouch _ -- namespace
  exact ⟨(hm _ hq).1,hv _ hq,fun s t=>vessels H Q R hR hq hT (s,t),(hm _ hq).2⟩ -- args

lemma vouches {K m t : ℝ} (P : Teller G) (D : Patch) (h : D.Branches P.bind G) (J : ChartRatio G) (hJ : LocalRatio J) (i : Purse)
    (ht : ∀ {c f : Side} (S : StepData c f), S.patch=D→ Footprint.reserve P.top.supportExponent (Docking.increment (load i.era + 1)) (Footprint.conversion S.ratio 1) t)
    (hQ : 0<t) (hv : ∀ᶠ x in atTop, Granite J P D W d ε x) (hδ : ∀ᶠ x in atTop, Wax.Peaking P x W m (2*d) D.L 200) (hm : 0< m) (ha : 0< K) (he :0<ε)
    (hp : 2*K ≤ m/2) (hW :0<W) (hd : 0≤d) (hl :2*i.era.coast.a ≤ K/4): ∀ᶠ s in atTop,Mesa J i P D W d s:= by
  let e:=Docking.increment (load i.era+1)
  have hB:0≤e:= by unfold e Docking.increment ucap load; linarith only [i.spend]
  obtain ⟨Q,H⟩:= EndpointLoadF16.DetLong.stores G D P h 2 1 20 le_rfl e hB
  obtain ⟨g,C,η,b,k,hg,hC,hη,hb,hk,H₁⟩:= Physical.late_price P D 20 (by decide) h hB
  obtain ⟨v,hA,hy⟩:=Barge.dredge P D h hd
  have ht' := foreshadows (η':=η) P Q J hJ D h hB (zero_le_one.trans hC) hg hb hk hQ hd hm ha hp
  obtain ⟨r,hr⟩:= eventually_atTop.mp (ht'.and (tall_limit.eventually (H.and (H₁.and (hy.and (hv.and (Work.E01.radiusB_tendsto.eventually_ge_atTop (Coverage.shutters D+1))))))))
  filter_upwards [hoops P J hJ D m d W t hW hδ hv e, Perch.half.eventually_ge_atTop r, Grid.yield i D G v (zero_lt_one.trans_le hA) ε K he ha hl] with s hL hs hJ'
  refine ⟨fun x hx => (hr x (hs.trans hx.1)).2.2.2.2.1.permits, fun {x} hx {c f} S v' hf hz H' =>?_⟩
  obtain ⟨hi,h,hS,hV,hg,hP⟩:=hr x (hs.trans hx.1); subst D J
  obtain ⟨H₀,H₂⟩:= hL x hx S v' rfl rfl H' (H'.head.symm ▸ ht S rfl)
  let Z:Draft v' P (retime x) W:= ⟨H₀.hats.boost,hP,H₀.hats.arc_pos,H₀.hats.vista⟩
  obtain ⟨hS,h3,h4⟩:= hS c f S v'.things rfl H'.period H'.funS
  have hh : noises v' v (retime x):= fun p hp=> hV S v'.things rfl H'.funS H'.period v'.source.beta v'.arc H₀.hats.beta H₂ H₀.hats.arc_pos H'.chosen.le p.park p.view p.tag p.key v'.chi hp
  obtain ⟨M,hM,hQ'⟩:=hi S v' W v rfl rfl H₀ h hh hS h3 h4
  refine ⟨Z,M,hW,H₀.hats.lives,cared i H₀ Z M ?_ hS⟩
  exact hJ' x hx S rfl v' P W M Z H'.beta.1 H'.walls.1 (ballot hg H₀.hats H'.period hh (zero_lt_one.trans_le hA) H'.large he.le H'.alongside H'.chosen) hM hQ'
end YM.PhysicalNext.InteractingRank.Pump
