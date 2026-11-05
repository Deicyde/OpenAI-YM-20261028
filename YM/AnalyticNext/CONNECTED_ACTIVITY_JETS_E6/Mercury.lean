import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Afresh
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ambit
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.March
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orin

/-! # Sector P.V moment Meristem on angular motion. Normalized one step
 with Camera gauges and Chronicles. Analytic formula tested exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {Ñ : ChartRatio G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E}
variable {z : Air f G} (H : Cash W s μ L Q o C T R) (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K)
variable (hq : Glass P X V x j W) (hC : Canary G A b) (he : 8*o.a*Pressure.fiery G s L ≤ A/2)

include H hX hM hK hq hC he
lemma boosts (p : Molecule S) (I : Finset (Bond f)) :
    let m:=(F.order G).prod X.dice; let g v:= rhythm I X (V v) A Q.table p R W o.a Q.halo
    Meristem g x m j ∧ ∀ᶠ y in 𝓝 x, Integrable (g y) m := by
  intro m g
  have heq:=H.laws.data; have hv := heq.funds.length_eq; rw [← hv,← hX] at he
  have hM :=heq.localP F X hX hK hM
  have ht:= (hX.symm ▸ H.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [hK,hX]; exact heq.access
  let A' := lensS I G; let U i:=circuit A' (vary X (V i)).relating; let V':= circuit A' X.relating
  have hx: U x=V' := by unfold U V'; rw [hq.lifts]; rfl
  have hF:= hM.sails.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM.sails I
  have hs : Bottom V'⁻¹ (1+payE o.eta o.gap o.ample (tubularPrice G L))⁻¹ := Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry
    hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) A R.beta t.2 (V v)
  let z(t:F.Slice G×Air f G):= Pond.swim A' t.2; have hZ : MeasurePreserving z m (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef A')
    apply hs.comp (show MeasurePreserving _ m X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t i:= Pond.swim A' (w t i)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) hq hM.sails.room hC I ht.positive
  obtain ⟨B,hB,hk,hP⟩:= winglet (A:=U) (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>hq.relate i.val j.val) hω
  let Φ i v:= Polar.floating (vary (X' i) (V v)) o.a R W Q.table (w i v) (own p) Q.halo p
  have ht': 4*o.a*X.t < Q.table.radius := by
    have ht:=heq.covers; rw [← hv, ← hX] at ht; exact ht
  have hΨ : Zest Φ x j := hq.thorn (Y:=Prod.fst) Prod.snd hM.sails.room hC ht p Q.halo Q.table_exists
    (mul_pos o.large hM.sails.room.fiery) he ht'
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
  obtain ⟨s,h⟩:= hq.sails; filter_upwards [nearby X hC hq.lifts h] with y hh'
  exact inshore I X hC (V y) hh' measurable_fst measurable_snd ht hh Q.table_exists p

lemma chutes (p : Molecule S) :
    let m:=(F.order G).prod X.dice; let I:=edgesM S (H.unionP p) (radiusB s)
    let g v:= rhythm I X (V v) A Q.table p R W o.a Q.halo
    (fun v=> bars (podium S G (H.unionP p) (radiusB s)) (vary X (V v)) p R Q.table W o.a Q.halo) =ᶠ[𝓝 x]
       fun v=>∫ y, g v y ∂m := by
  intro m I g; obtain ⟨_,ht⟩:= boosts H hX hM hK hq hC he p I
  obtain ⟨v,hv⟩:= hq.sails; have he:= H.laws.data
  filter_upwards [ht,nearby X hC hq.lifts hv] with y hy hY
  rw [← chargedU (H.unionP p) (radiusB s)]; rw [integral_prod _ hy]
  have hs: ground R T Q.halo X.B p=H.unionP p:= by unfold Coat.B; rw [hX]; rfl
  apply Flux.transition I X hC (V y) hY p (he.localP F X hX hK hM).sails.fullC Q.buys (H.unionP p) hs.le
    (hX.symm ▸ he.room) (hX.symm ▸ H.laws.intake) (show ShellAccess S G X.x W X.width o.γ from ?_) Q.table_exists
  · unfold I Coat.B; rw [hX]
  rw [hK,hX]; exact he.access

-- connection to FlareW. k return moment.
lemma coterie (Ξ : Utopia H j v d r C' χ) (F' : FlareW H Ξ A A' k) (hχ : X.χ=χ) (p : Molecule S) (ht : troupe T R Q.halo (radiusB s) p)
    (hv : Ac.Spark H.supportP p) (hy : Healthy (Pressure.temp X.x) (H.unionP p) X.V) (hV : Mode V x j v) :
    Brush j (A'*Ξ.meant p k) 1 (fun v=> bars (podium S G (H.unionP p) (radiusB s)) (vary X (V v)) p R Q.table W o.a Q.halo) x := by
  let I:= edgesM S (H.unionP p) (radiusB s)
  obtain ⟨f,hF,h,hX'⟩:= F'.tents E F X V x p hχ hM hX hK hy ht hv hV hq.lifts
  exact (((boosts H hX hM hK hq hC he p I).1.buds f hF zero_le_one h
    (Filter.Eventually.of_forall hX'))).shimmy (chutes H hX hM hK hq hC he p)
end YM.ConnectedActivityE6.Blaze.Flux
