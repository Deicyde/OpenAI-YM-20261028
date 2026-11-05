import YM.FullVolume.Florid.Plume
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
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (H:Cash W X.x μ L Q o C T R)(he:X.width=o.K) (hM:X.manifest) (I : Finset (Bond f)) {y:E}{V:E → Config G c}
variable (h:Glass P X V y j W)(hp: Canary G d A)(ha:8*o.a*Pressure.fiery G X.x S.patch.L≤d/2)
include H he hM h hp ha
lemma lstrong  :
    let m:=(F.order G).prod X.dice; let g v:= M.carat I X (V v) d Q.table p W o.a Q.halo
    ∀ i:ℕ,i ≤ j → StronglyMeasurable (JetF g i y) := by
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
  have hkM: ∃ B,Integrable B m ∧∀ᶠ y' in 𝓝 y,∀ i,Brush j (B i) 1 (fun y=> g y i) y' := by
    let K' t:=(J*B (z t)*K)*(1+((1+1)+1))^j
    rw [hx] at hk
    have hb : Integrable (B ∘ z) m := (hZ.integrable_comp hB.aestronglyMeasurable).2 hk
    refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
    filter_upwards [hH,h₂,hP] with i hi h hh s
    have hx' := hh s
    -- convert density origin
    rw [hx] at hx'
    exact (((hi s).paints hx').paints (h s)).trim
  have hvm:∀ᶠ y in 𝓝 y,Measurable (g y):=by
   obtain ⟨s,hY⟩:= h.sails; filter_upwards [nearby X hp h.lifts hY] with y hh'
   exact M.docks X (V y) I hp hh' measurable_fst measurable_snd ht hh Q.table_exists p

  obtain ⟨B,hK,hG⟩:= hkM; obtain ⟨D',hd,hS,hs'⟩:= _root_.mem_nhds_iff.mp (hG.and hvm)
  intro k hp
  apply Meristem.legs (j:=j) (f:= Function.swap g) hS (fun i s h=> ?_) (fun t h=> (show Measurable (g t) from (hd h).2).stronglyMeasurable) hp hs'
  have h := (show ∀ i,Brush j (B i) 1 (fun y=>g y i) s from (hd h).1) i; exact h.smooth

omit h he hM ha hp
lemma confined_s (Y:Support c)(ht : ground R T Q.halo X.B p⊆Y)(V:Config G c) (hI: I=edgesM S Y X.B) (a:ℝ):
   let B:= lensS I G; let f:= M.chimes X p I V d Q.table W a Q.halo
   confined (swim B) f:= by
    intro B f u v hh; unfold f chimes; rw [Flux.slab I X V u v hh d]; apply congrArg
    have hp:= congr_arg (pitch I X d R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    apply (M.census (X:=vary X V) (X':=vary X V) (l:=Q.halo) (Z:=Y) p (show Intake P T (vary X V).x R from H.laws.intake) H.laws.data.room Q.buys ?_ ht)
    refine ⟨Village.refl ..,fun i hi=> (Pond.observe B).mp hp i (?_), fun _ _=>Iff.rfl⟩
    unfold B; rw [hI,chargedU]; exact hi
end Leaf
end YM.PhysicalNext.Repeat.Lotus
