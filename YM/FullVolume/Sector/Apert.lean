import YM.FullVolume.Sector.Rink
/-! Reweight by keeping padding aligned. Only pay determinant on THIS lens poly. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
section orbit
variable {ι Ω E:Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {M:Measure Ω} [SFinite M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X:Coat T F) (I:Finset (Tubular f G)) {p:Ω × Air f G → E}
 -- family currency. (inherited measures; finance does not modify pole law). Payroll identity EXACT.
lemma root_lens (ht:X.relating.PosDef) (hh: StronglyMeasurable p) (he:∀ u v:Air f G, swim I u=swim I v→ ∀ x:Ω,p (x,u)=p (x,v)) (hp:Integrable p (M.prod X.dice)) (s:ℝ)(hs:0<s):
    let m:= M.prod X.dice; let f x:= Alabaster.walk (circuit I X.relating) s (swim I x.2) • p (x.1,s • x.2)
    Integrable f m ∧ (∫ x,p x ∂m)=(∫ x,f x ∂m):=by
  intro m f
  let g (x: Ω × Air _ G):Ω × Poll.Body I:= (x.1,swim I x.2)
  let l (x: Ω × Poll.Body I):= (x.1, Pond.spill I x.2)
  let V:= circuit I X.relating; have hv : V.PosDef:= ht.submatrix Subtype.val_injective
  let M' := M.prod (Poll.sweep V); have hK : MeasurePreserving g m M':=(MeasurePreserving.id M).prod (Pond.orbit ht.posSemidef I)
  let q:= p ∘ l; have hq : StronglyMeasurable q:= hh.comp_measurable (show Measurable l from measurable_fst.prodMk ((spill_m I).comp measurable_snd))
  have h x:p x=q (g x):= he x.2 (Pond.spill I _) (settled I _).symm x.1
  have hI : Integrable q M':=(hK.integrable_comp hq.aestronglyMeasurable).1 (hp.congr (ae_of_all m h))
  obtain ⟨hc,hM⟩:= earningsK (μ:=M) V hv hs q; let f'(x:Ω × Poll.Body I):= Alabaster.walk V s x.2 • q (x.1,s • x.2); have hF: Integrable f' M':=hM.1 hI
  have hZ : f=f' ∘ g:= by
    ext x; unfold f f'; simp only [Function.comp_apply]; apply congr_arg (fun z:E=> _ • z); exact he _ _ (Eq.trans (show swim I (s • x.2)=s • swim I x.2 from rfl) (settled I _).symm) _ -- order spiral
  have ht (p:Ω×Poll.Body I→E) (hp: AEStronglyMeasurable p M') : (∫ x,p (g x) ∂m)=∫ x,p x ∂M' := by rw [← hK.map_eq] at *; exact (integral_map hK.measurable.aemeasurable hp).symm
  rw [hZ]; exact ⟨(hK.integrable_comp hF.1).2 hF, (integral_congr_ae (ae_of_all _ h)).trans ((ht q hq.aestronglyMeasurable).trans (hc.trans (ht f' hF.1).symm))⟩
end orbit
-- V confinement along entire U.Chart. No Frame determinant on unused World.
section shifts
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (X:Coat T F) {V : E→ Config G c}
lemma confined_s {h:ℕ} {v:ℝ} (C:Config G c) (s:Molecule S) (I : Support c) (k:ℝ) (hp:500≤h)(hx:Matter.ground R T h X.B s⊆I) (H : Room P S T X.x)(ht:Intake P T X.x R) (Q:ChartRatio G) (a:ℝ) :
    let J:= edgesM S I X.B; let B:= lensS J G
    ∀ i u: Air f G, swim B i=swim B u→ recoil J X C k Q s R v a h i = recoil J X C k Q s R v a h u := by
  intro J B u v hh
  have hf:= congr_arg (Flux.pitch J X k R.beta C) hh; rw [pitch_alt,pitch_alt] at hf
  unfold recoil; rw [Flux.slab J X C u v hh]; apply congr_arg
  apply (Borough.flops (X:=vary X C) (X':=vary X C) (l:=h) (Z:=I) ?_ H hp (show Intake P T (vary X C).x R from ht) _ _ _ hx)
  exact ⟨Village.refl ..,fun i hi=> (Pond.observe B).mp hf i ((show podium S G I X.B=B from (chargedU (S:=S) I X.B).symm) ▸ hi), fun _ _=>Iff.rfl⟩
end shifts
end YM.ConnectedActivityE6.Empire
