import YM.UVExtension.Wick.Gaunt

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)

variable {z : Vines ι} {hv:z∈parade (betaF G x L) g}
namespace Lush
variable {J : Mixed.Costs} {v₀ : ℝ} (hK:Lush N hF z hv v₀ J) (hp:0≤v₀)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E} (he:V' τ=X.V) (hc': X.χ=χ)
    (hV:Mode V' τ j u)

set_option quotPrecheck false
variable (p:Molecule S) {i:ℕ} (hi:i≤j) (Z:Fin i→ E)
local notation "Φ"=>cockpit X A o.a W p R Q.table Q.halo V
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
local notation "S'"=>parade (ι:=ι) (betaF G x L) g
local notation "Γ'"=> (F.order G).prod X.dice
local notation "P'"=> (F.order G).prod (volume : Measure (Body (↥ X')))
-- reads of all level lamps
private def jack {E A F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f:A→ E→F) {i:ℕ} (x : E) (u:Fin i→E) (y:A):F:= iteratedFDeriv ℝ i (f y) x u

def blade (w':Vines ι) (y:F.Slice G × Air f G):ℂ:= iteratedFDeriv ℝ i (fun t=> Φ w' Z' (V' t) y) τ Z
-- ! check # blade implicit args; x notation. MAKE not section includes.

variable (hy:Healthy (temp X.x) (H.unionP p) X.V)
include hK he hc hX hm hr hS hi hV

-- real actual probe jet at theta sample.
lemma drums (w':Drums ι) (he':grown (betaF G x L) w w') (y:F.Slice G × Air f G) : blade (A:=A) (H:=H) (X:=X) (V':=V') (V:=V) (τ:=τ) p Z (hoist w') y=
    ↑(iteratedFDeriv ℝ i (fun t=> rhythm Z' X (V' t) A Q.table p (chunk R (blend V (w'∘some)) (w' none)) W o.a Q.halo (y.1,scaled (w' none) y.2)) τ Z :ℝ) := by
  let J:= (hF.mixture w' he').some; let v:=w' none; have hv:0<v:=J.laws.intake.positive
  let f t:= rhythm Z' X (V' t) A Q.table p (chunk R (blend V (w'∘some)) v) W o.a Q.halo (y.1,scaled v y.2)
  let L := Complex.ofRealCLM
  unfold blade; rcases y with ⟨y0,z0⟩
  have hp : ContDiffAt ℝ (↑j) f τ := by
    let hs:= (N.granted _ _ S T _ _ J hS rfl).2 E V' F X τ hX hc hr hm he hV
    exact (uv_songs J hX hm hr hs.1 N.bay N.foot p Z').1 _
  rw [show (fun t=> cockpit ..)=L ∘ f from funext fun t=>?_]
  exact congr_arg (fun k:E [×i]→L[ℝ] ℂ=>k Z) (L.iteratedFDeriv_comp_left hp (by exact_mod_cast hi))
  exact (jetcoin X A V _ _ v R W Q.table Q.table_exists z0 w' o.a p _ rfl hv Q.halo).symm
-- real pixel measurable.
lemma journeys (w':Drums ι) (hz:grown (betaF G x L) w w') : StronglyMeasurable (blade (A:=A) (H:=H) (X:=X) (V':=V') (V:=V) (τ:=τ) p Z (hoist w')) := by
  have h x':= drums N hS hF hX hm hc hr hK he hV p hi Z w' hz x' -- inspect
  let J:= (hF.mixture w' hz).some; let v:= w' none
  let g: E→ F.Slice G × Air f G→ℝ:=fun t=> rhythm Z' X (V' t) A Q.table p (chunk R (blend V (w'∘some)) v) W o.a Q.halo
  have hh:= (N.granted _ _ S T _ _ J hS rfl).2 E V' F X τ hX hc hr hm he hV
  have hg : StronglyMeasurable (JetF g i τ):= (uv_songs J hX hm hr hh.1 N.bay N.foot p Z').2 i hi
  have hY: StronglyMeasurable (fun y=> ((JetF g i τ y Z:ℝ):ℂ)):=Complex.continuous_ofReal.comp_stronglyMeasurable ((ContinuousMultilinearMap.apply ℝ _ _ Z).continuous.comp_stronglyMeasurable hg)
  have hp: Measurable (fun t:F.Slice G × Air f G=> (t.1,scaled v t.2)):=by unfold scaled; fun_prop
  rw [funext h]; exact hY.comp_measurable hp

include hy
lemma blossom (y : F.Slice G × Air f G): Bumps S' (fun s=>blade (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z s y):= by
  intro s f hs hm' hf; exact (Bower.crests N hS hF hX hm hc hr z hv he hV hs hm' hf hK.conduit p hy y Z').order i hi Z
lemma shiner (t:Vines ι) (ht:t∈parade (betaF G x L) g): StronglyMeasurable (blade (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z t):= by
  apply propagates Husk.strong (blossom N hS hF hX hm hc hr hK he hV p hi Z hy) (Festa.altitude (H:=H)) hF.margin hF.bound (journeys N hS hF hX hm hc hr hK he hV p hi Z) t ht

-- named bulb jet actual parameter. No j/hK in evaluation.
omit hK he hc hX hm hr hS hi hV hy

def plated (w : Vines ι) (y : F.Slice G × Body (↥ X')) := bulb (circuit X' X.relating) y.2 (w none)*blade (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z w (y.1,Pond.spill X' y.2)

def mercury (s : Vines ι) := ∫ v,plated (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z s v ∂P'

include hK he hc hX hm hr hS hi hV
lemma gold (w':Drums ι) (hT:grown (betaF G x L) w w') : mercury (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z (hoist w')=
    (↑(iteratedFDeriv ℝ i (fun t=> bars (podium S G (H.unionP p) (radiusB x)) (vary X (V' t)) p (chunk R (blend V (w'∘some)) (w' none)) Q.table W o.a Q.halo) τ Z:ℝ):ℂ):= by
  let Q':=(hF.mixture w' hT).some; let R':=chunk R (blend V (w'∘some)) (w' none); let u':=w' none; have hp:0<u':=Q'.laws.intake.positive
  let g:E→ F.Slice G× Air f G →ℝ:=fun t=> rhythm Z' X (V' t) A Q.table p R' W o.a Q.halo
  let G' := gStep u'; have hg':G'≠0:=(inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'; have he (z:Air f G):scaled u' (G' • z)=z:=inv_smul_smul₀ hg' z
  let fx t:= JetF g i τ t Z; let L':= X'; let U:= lensS Z' G
  let Q₀ (y:F.Slice G × Body (↥ U)):= fx (y.1,spill U y.2); let M:=circuit U X.relating
  have hh:= (N.granted _ _ S T _ _ Q' hS rfl).2 E V' F X τ hX hc hr hm ‹_› hV
  have H' := (boosts Q' hX hm hr hh.1 N.bay N.foot p Z').1.calls
  -- Bars V block on F O, no representative choices
  have hF': iteratedFDeriv ℝ i (fun t=> bars (podium S G (H.unionP p) (radiusB x)) (vary X (V' t)) p (chunk R (blend V (w'∘some)) (w' none)) Q.table W o.a Q.halo) τ Z=∫ t,fx t ∂Γ' := by
    have h' := ((chutes Q' hX hm hr hh.1 N.bay N.foot p).iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds
    change iteratedFDeriv ℝ i _ τ = iteratedFDeriv ℝ i (fun i=> ∫ t,g i t ∂Γ') τ at h'; exact (congr_arg (fun k:E [×i]→L[ℝ] ℝ=> k Z) (h'.trans (H'.2 i hi).2)).trans ((ContinuousMultilinearMap.apply ℝ (fun _:Fin i=>E) _ Z).integral_comp_comm (H'.2 i hi).1).symm
  rw [hF']; let Y':= hoist w';
  have heμ := (H.laws.data.localP _ X hX hr hm).sails.fullC; have hx:= sweeping X X' heμ; let μ:=(F.order G).prod (arch U X.relating)
  have hZ : ∀ z, plated (V:=V) (V':=V') (H:=H) (X:=X) (A:=A) (τ:=τ) p Z (hoist w') z= Complex.ofReal (tether M u' Q₀ z):= by
    rintro ⟨y,z⟩
    unfold plated; rw [drums N hS hF hX hm hc hr hK ‹V' τ = _› hV p hi Z w' hT]; rw [show hoist w' none=(u':ℂ) from rfl, voiced _ _ hp]
    unfold tether; dsimp only [Q₀]; rw [smul_eq_mul,Complex.ofReal_mul,Festa.spilling]; push_cast; rfl
  unfold mercury; simp_rw [hZ]; rw [integral_complex_ofReal,← axle _ M (heμ.submatrix Subtype.val_injective) hp]; apply congr_arg Complex.ofReal
  have ha: Measurable fx := ((ContinuousMultilinearMap.apply ℝ _ _ Z).continuous.comp_stronglyMeasurable (show StronglyMeasurable (JetF g i τ) from (uv_songs Q' hX hm hr hh.1 N.bay N.foot p Z').2 i hi)).measurable
  have hm' : Measurable Q₀ := ha.comp (measurable_fst.prodMk ((spill_m U).comp measurable_snd))
  change (∫ x,Q₀ x ∂μ)=_; rw [show μ=Measure.map _ Γ' from hx.map_eq.symm, integral_map hx.measurable.aemeasurable hm'.aestronglyMeasurable]; apply integral_congr_ae
  filter_upwards with y; rcases y with ⟨y,z⟩; apply Complex.ofReal_injective
  suffices h:((fx (y,spill U (swim U z)):ℝ):ℂ) = ((fx (y,z):ℝ):ℂ) from h
  let f w:= blade (V:=V) (V':=V') (H:=H) (X:=X) (A:=A) (τ:=τ) p Z (hoist w') (y,w)
  have ht' w:f (G' • w)= ((fx (y,w):ℝ):ℂ) := by
    have h:= drums N hS hF hX hm hc hr hK ‹_› hV p hi Z w' hT (y,G' • w)
    unfold f; apply h.trans; dsimp only; rw [he]
  rw [← ht', ← ht']; apply congr_arg (fun k:E [×i]→L[ℝ] ℂ=> k Z) (congr_arg (fun f=>iteratedFDeriv ℝ i f τ) (funext (fun t=>hF.confinement hX p (v:=hoist w') ?_ (V' t) y _ _ (?_))))
  · apply marching _|>.2; refine ⟨hT none,fun i=>?_⟩; exact (show ‖hoist w' (some i)‖= _ from Complex.norm_real (w' (some i))) ▸ lt_of_lt_of_le (mem_ball_zero_iff.mp (hT (some i))) hF.bound
  change G' • Pond.swim U (Pond.spill U (Pond.swim U z))=G' • Pond.swim _ _; rw [Pond.settled]
end Lush
end Bower
end YM.UVExtension.Wick
