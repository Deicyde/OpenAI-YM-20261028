import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Afresh
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ambit
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brushhold
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Chimes
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
open Bloch Laurent Progress.StationaryScenes Green Census Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F}  {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
variable {E:Type} {d C D A:ℝ} {j:ℕ}
def carat (I:Finset (Bond f)) (X : Coat T F) (V:Config G c)(d:ℝ)(Ñ:ChartRatio G) (p:Molecule S) (W a:ℝ)(l:ℕ) (t:F.Slice G × Air f G):= M.chimes (X.wrapY t.1) p I V d Ñ W a l t.2
lemma canv (U V: Config G f)(b : Directions G f) (h: Armor X a b U V): M.fond X a b U=M.fond X a b V:=by
  unfold fond; rw [M.turn.badge_area]; by_cases he: X.enforce (2*a) b (X.plaza (Footprint.enlargement S.ratio 0 X.B (RG.inspected M.crest)))=0
  · rw [he,mul_zero,mul_zero]
  rw [M.specific _ _ (h.venial _ he)]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (H:Cash W X.x μ L Q o C T R)(he:X.width=o.K) (hM:X.manifest) (I : Finset (Bond f)) {y:E}{V:E→Config G c}
variable (h:Glass P X V y j W)(hp: Canary G d A)(ha:8*o.a*Pressure.fiery G X.x S.patch.L≤d/2)
include H he hM h hp ha
omit he hM [FiniteDimensional ℝ E] in
lemma supple : Zest (fun (a:F.Slice G × Air f G) i=>M.floret (vary (X.wrapY a.1) (V i)) p W o.a Q.table (own p) Q.halo (course (X.wrapY a.1) d R.beta a.2 (V i))) y j:=by
  let Z:= X.wrapY; let B(a:F.Slice G × Air f G):=worldZ (Z a.1) R.beta a.2; let Y a z:= steer (Z a.1) d (fun i=> prune d (B a i)) (V z)
  let P(a:F.Slice G × Air f G)(i:E):=vary (Z a.1) (V i); let T' (t:F.Slice G × Air f G):=(Z t.1).input (B t)
  let K t y:= sweepZ (P t y) R.beta (Y t y); have hq : Zest Y y j := (h.foreshadow (Y:=Prod.fst) B hp).1
  have hX:=H.laws.data; have hv:=hX.room; have hr:=H.laws.intake
  have hv':0<o.a*X.t:=mul_pos o.large hv.fiery; have hx:4*o.a*X.t < Q.table.radius:= by have h':= hX.covers; rw [← hX.funds.length_eq] at h'; exact h'
  let L : Directions G f→ₗ[ℝ] Air f G := { toFun t:= WithLp.toLp _ (stand t),map_add' _ _:=rfl,map_smul' _ _:=rfl }
  have hK: Zest K y j := (((hq.plusminus (h.settles (Y:=Prod.fst) hv)).scalar (gStep R.beta)⁻¹).replay L.toContinuousLinearMap)
  unfold floret; split_ifs
  swap; · exact Zest.still _
  let t a z:= M.fond (P a z) o.a (Y a z) (T' a); let r:=p.erase (M.turn.badge S)
  have ht:Zest t y j:= (Zest.parallel M.profit (fun i=> M.earn (T' i))).paint (Zest.full (X.plaza (areas R T 0 X.B (M.turn.badge S))) _ (fun k _=> (hq.replay (ContinuousLinearMap.proj k)).wand (Glass.tip (X:=X) (2*o.a*X.t))))
  refine (ht.paint (Zest.full r _ (fun i _=> h.glassy T' (Y:=Prod.fst) hv Y hq hr (own p) Q.halo hv' hx Q.table_exists i hK))).congr ?_
  obtain ⟨q,hF⟩:=h.sails; filter_upwards [Silica.nearby X hp h.lifts hF,h.brews.1] with x hh hT i
  let u:= B i; let p':= P i x; let Y':= Y i x; let b:= steer (Z i.1) d u (V x); have hvA : Drivable (Z i.1) d A (V x):= ⟨hh.good⟩
  have he':Transfer p' b Y' (4*o.a *X.t):=⟨(fruit (Z i.1) hp (V x) u (a:=4*o.a*X.t) (by change 8*o.a*X.t ≤ _ at ha; nlinarith only [ha,hp.warm])).both⟩
  have hy := conquered (Z i.1) hp (V x) u hvA hv' ha
  let z:=course (Z i.1) d R.beta i.2 (V x)
  have hV:worldZ p' R.beta z=b:= Silica.proceeds _ _ hr.positive _ _; have hb: Armor p' o.a b (p'.input b) (T' i) := plastic hy hv'
  symm; apply congr_arg₂ (·*·)
  · change M.paidU _ _ (worldZ p' _ z)=_; rw [hV]; unfold paidU; rw [M.canv p' _ _ _ hb]
    unfold fond; apply congr_arg (_*·); exact Finset.prod_congr rfl fun j hj=> (Transfer.grain p' he' hv' j (2*o.a) (show 0<(2*o.a)*X.t from by rw [mul_assoc]; positivity) le_rfl).1
  unfold floating; rw [hV]; refine Finset.prod_congr rfl fun j hj=> ?_
  have h:=hb.reeled hv W Q.table (own p) Q.halo (show Intake _ _ p'.x R from hr) j z; exact h.trans (Transfer.carries p' he' hv' hv hT _ _ _ _ _ _ j)

lemma boosts  :
    let m:=(F.order G).prod X.dice; let g v:= M.carat I X (V v) d Q.table p W o.a Q.halo
    Meristem g y m j ∧ ∀ᶠ y in 𝓝 y, Integrable (g y) m := by
  intro m g
  have heq:=H.laws.data; have hv := heq.funds.length_eq;
  have hM :=heq.localP F X rfl he hM
  have ht:= (H.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [he]; exact heq.access
  let d' := lensS I G; let U i:=circuit d' (vary X (V i)).relating; let V':= circuit d' X.relating
  have hx: U y=V' := by unfold U V'; rw [h.lifts]; rfl
  have hF:= hM.sails.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM.sails I
  have hs : Bottom V'⁻¹ (1+payE o.eta o.gap o.ample (tubularPrice G L))⁻¹ := Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry
    hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) d R.beta t.2 (V v)
  let z(t:F.Slice G×Air f G):= Pond.swim d' t.2; have hZ : MeasurePreserving z m (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef d')
    apply hs.comp (show MeasurePreserving _ m X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t i:= Pond.swim d' (w t i)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) h hM.sails.room hp I ht.positive
  obtain ⟨B,hB,hk,hP⟩:= winglet (A:=U) (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>h.relate i.val j.val) hω
  let Φ i v:= M.floret (vary (X' i) (V v)) p W o.a Q.table (own p) Q.halo (w i v)
  have ht': 4*o.a*X.t < Q.table.radius := by
    have ht:=heq.covers; rw [←  hv] at ht; exact ht
  have hΨ : Zest Φ y j := M.supple X p H h hp ha
  obtain ⟨J,hJ,hH⟩:= hΞ.post
  obtain ⟨K,h₁,h₂⟩:=hΨ.post
  refine Meristem.points g m ?_ ?_
  · let K' t:=(J*B (z t)*K)*(1+((1+1)+1))^j
    rw [hx] at hk
    have hb : Integrable (B ∘ z) m := (hZ.integrable_comp hB.aestronglyMeasurable).2 hk
    refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
    filter_upwards [hH,h₂,hP] with i hi h hh s
    have hx' := hh s
    -- convert density origin
    rw [hx] at hx'
    exact (((hi s).paints hx').paints (h s)).trim
  obtain ⟨s,hY⟩:= h.sails; filter_upwards [nearby X hp h.lifts hY] with y hh'
  exact M.docks X (V y) I hp hh' measurable_fst measurable_snd ht hh Q.table_exists p

lemma chutes  :
    let m:=(F.order G).prod X.dice; let I:=edgesM S (H.unionP p) (X.B)
    let g v:= M.carat I X (V v) d Q.table p W o.a Q.halo
    (fun v=> M.cinema (vary X (V v)) p W o.a Q.table Q.halo (podium S G (H.unionP p) X.B)) =ᶠ[𝓝 y]
       fun v=>∫ y, g v y ∂m := by
  intro m I g; obtain ⟨_,ht⟩:= M.boosts (X:=X) p H he hM I h hp ha
  obtain ⟨v,hv⟩:= h.sails; have he₀:= H.laws.data
  filter_upwards [ht,nearby X hp h.lifts hv] with y hy hY
  rw [← chargedU (H.unionP p) (X.B)]; rw [integral_prod _ hy]
  exact M.transition X (V y) I hp hY p (he₀.localP F X rfl he hM).sails.fullC Q.buys (H.unionP p) (Finset.Subset.refl _) he₀.room H.laws.intake (he.symm ▸ he₀.access) Q.table_exists rfl
end Leaf
end YM.PhysicalNext.Repeat.Lotus
