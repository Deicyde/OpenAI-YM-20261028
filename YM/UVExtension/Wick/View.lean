import YM.UVExtension.Wick.Glisten
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
omit [FiniteDimensional ℝ E] in
lemma uv_brush (p : Molecule S) (I : Finset (Bond f)) :
    let m:=(F.order G).prod X.dice; let g v:= rhythm I X (V v) A Q.table p R W o.a Q.halo
    (∃ B, Integrable B m ∧ ∀ᶠ y in 𝓝 x, ∀ i, Brush j (B i) 1 (fun y=> g y i) y) ∧ (∀ᶠ y in 𝓝 x, Measurable (g y)) := by
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
  constructor
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

lemma uv_songs (p : Molecule S) (I : Finset (Bond f)) :
    let g v:= rhythm I X (V v) A Q.table p R W o.a Q.halo
    (∀ y, ContDiffAt ℝ (↑j) (fun i=>g i y) x)∧∀ k≤j,StronglyMeasurable (JetF g k x):=by
  intro g; obtain ⟨⟨B,hB,h⟩,hs⟩:= uv_brush H hX hM hK hq hC he p I
  refine ⟨fun t=>((mem_of_mem_nhds h) t).smooth,fun i hi=>?_⟩
  obtain ⟨u,hu,hU,hv⟩:= _root_.mem_nhds_iff.mp (h.and hs)
  apply Meristem.legs (f:=Function.swap g) hU (fun y t ht=> ((hu ht).1 y).smooth) (fun i hi=> (hu hi).2.stronglyMeasurable) hi hv
end YM.ConnectedActivityE6.Blaze.Flux
