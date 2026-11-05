import YM.UVExtension.Linden.Thread
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
    (M: PhysicalNext.Repeat.Lotus.Leaf R) (hl:Lines R V w (betaF G x L) M)
set_option quotPrecheck false
variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
local notation "bX"=> M.turn.badge S
local notation "Σ"=> parade (ι:=ι) (betaF G x L) g
variable (p:Molecule S) (hp: Healthy (temp X.x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V':E → Config G c} {τ:E}
    (ht: V' τ=X.V)(hV:Mode V' τ j u) (t:F.Slice G × Air f G) (q:Vines ι) -- S α
local notation "cA"=> (pilot M p X A Q.table (W:=W) o.a Q.halo V)
local notation "bA"=> (buffer M p X A Q.table (W:=W) o.a Q.halo V)
local notation "Λ"=> grown (ι:=ι) (betaF G x L) w
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
variable (Y: Mojo Q o L μ A x d v₁ j χ)
variable {m:Molecule S}
variable {U:Mixed.Costs} {z : Vines ι} {hz:z∈parade (betaF G x L) g} (B₀:Lush N hF z hz v₀ U) (h₀:0≤v₀)
local notation "Θ"=> (z none).re
variable {i:ℕ} (hi:i≤j) (Z:Fin i→ E)
local notation "Γ'"=> (F.order G).prod X.dice
local notation "Λx"=> flax (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
local notation "P'"=> (F.order G).prod (volume : Measure (Body (↥ X')))
include B₀ hS ht hV hX hp hm hr hc Y hi
lemma gilt (y:F.Slice G × Air f G): Bumps Σ (fun z=> Λx z y):= fun _ _ h hh ht'=> (harmony N hS hF M hX hm hc hr p hp ht hV Y B₀ Z' y h hh ht').order i hi Z
include hl
lemma glam (z:Vines ι)(hv:z∈parade (betaF G x L) g): StronglyMeasurable (Λx z):=by
  exact propagates Husk.strong (gilt N hS hF M hX hm hc hr p hp ht hV Y B₀ hi Z) (Festa.altitude (H:=H)) hF.margin hF.bound (stain N hS hF M hl hX hm hc hr p ht hV hi Z) z hv
omit hp B₀ Y

def foamF (w:Vines ι)(y:F.Slice G × Body (↥(lensS Z' G))) := bulb (circuit X' X.relating) y.2 (w none)* Λx w (y.1,Pond.spill X' y.2)
local notation "ℓ"=> foamF (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
def marsh (w:Vines ι):= ∫ y,ℓ w y ∂ P'
local notation "M!"=> marsh (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
-- defeq fighter
include N hF
lemma pine (w':Drums ι)(h:grown (betaF G x L) w w'): let Z0:= hl.leaf w' h
   M! (hoist w')= ↑(iteratedFDeriv ℝ i (fun t=> Z0.cinema (vary X (V' t)) p W o.a Q.table Q.halo (podium S G (H.unionP p) (radiusB x))) τ Z:ℝ) := by
  intro Z₀; let Q':=(hF.mixture w' h).some; let R':=chunk R (blend V (w'∘some)) (w' none); let u':=w' none; have hp:0<u':=Q'.laws.intake.positive
  let g:E→ F.Slice G× Air f G →ℝ:=fun t=> Z₀.carat Z' X (V' t) A Q.table p W o.a Q.halo
  let G' := gStep u'; have hg':G'≠0:=(inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'; have hb (z:Air f G):Wick.scaled u' (G' • z)=z:=inv_smul_smul₀ hg' z
  let fx t:= JetF g i τ t Z; let L':= X'; let U:= lensS Z' G
  let Q₀ (y:F.Slice G × Body (↥ U)):= fx (y.1,spill U y.2); let M':=circuit U X.relating
  have hh: Glass P X V' τ j W:= ((N.granted _ _ S T _ _ Q' hS rfl).2 E V' F X τ hX hc hr hm ht hV).1
  let D':Cash W X.x μ L Q o a T R':= hX.symm ▸ Q'; have hv: 8*o.a*Pressure.fiery G X.x S.patch.L ≤ A/2:=by rw [hX,Q'.laws.data.funds.length_eq]; exact N.foot
  have hB:X.B=radiusB x:=congr_arg _ hX; have hC: H.unionP p=D'.unionP p:= by change _= Matter.ground R T Q.halo (radiusB X.x) p; rw [hX]; rfl
  have H' := (Z₀.boosts (X:=X) p D' hr hm Z' hh N.bay hv).1.calls
  have hT : (fun v=> Z₀.cinema (vary X (V' v)) p W o.a Q.table Q.halo (podium S G (H.unionP p) (radiusB x)))=ᶠ[𝓝 τ] fun y=> ∫ i,g y i ∂Γ' :=by
     unfold g; rw [hC,← hB]; exact Z₀.chutes X p D' hr hm hh N.bay hv
  have hF': iteratedFDeriv ℝ i (fun v=> Z₀.cinema (vary X (V' v)) p W o.a Q.table Q.halo (podium S G (H.unionP p) (radiusB x))) τ Z=∫ t,fx t ∂Γ':=by
    exact (congr_arg (fun k:E [×i]→L[ℝ] ℝ=> k Z) ((hT.iteratedFDeriv ℝ i).eq_of_nhds.trans (H'.2 i hi).2)).trans ((ContinuousMultilinearMap.apply ℝ (fun _:Fin i=>E) _ Z).integral_comp_comm (H'.2 i hi).1).symm
  rw [hF']; let Y':= hoist w'
  have heμ := (H.laws.data.localP _ X hX hr hm).sails.fullC; have hx:= Wick.sweeping X X' heμ; let μ:=(F.order G).prod (arch U X.relating)
  have hZ : ∀ z, ℓ (hoist w') z= Complex.ofReal (tether M' u' Q₀ z):= by
    rintro ⟨y,z⟩; unfold foamF; rw [trav N hS hF M hl hX hm hc hr p ht hV hi Z w' h]; rw [show hoist w' none=(u':ℂ) from rfl, voiced _ _ hp]; unfold tether; dsimp only [Q₀]; rw [smul_eq_mul,Complex.ofReal_mul,Festa.spilling]; push_cast; rfl
  unfold marsh; simp_rw [hZ]; rw [integral_complex_ofReal,← axle _ M' (heμ.submatrix Subtype.val_injective) hp]; apply congr_arg Complex.ofReal
  have ha: Measurable fx := ((ContinuousMultilinearMap.apply ℝ _ _ Z).continuous.comp_stronglyMeasurable (show StronglyMeasurable (JetF g i τ) from (stepsM _ p D' hr hm Z' hh N.bay hv).2 i hi)).measurable
  have hm': Measurable Q₀ := ha.comp (measurable_fst.prodMk ((spill_m U).comp measurable_snd))
  change (∫ x,Q₀ x ∂μ)=_; rw [show μ=Measure.map _ Γ' from hx.map_eq.symm, integral_map hx.measurable.aemeasurable hm'.aestronglyMeasurable]; apply integral_congr_ae; filter_upwards with y; rcases y with ⟨y,z⟩; apply Complex.ofReal_injective
  let f w:= Λx (hoist w') (y,w)
  have ht' w:f (G' • w)= ((fx (y,w):ℝ):ℂ) := by
    unfold f; rw [trav N hS hF M hl hX hm hc hr p ht hV hi Z w' h]; dsimp only; rw [show Wick.scaled (w' none) (G' • w)=w from hb _]
  change ((fx (y,spill U (swim U z)):ℝ):ℂ)=↑(fx (y,z)); rw [← ht', ← ht']; apply congr_arg (fun k:E [×i]→L[ℝ] ℂ=>k Z) (congr_arg (fun f=>iteratedFDeriv ℝ i f τ) (funext (fun t=> surround (A:=A) hF M hl p (hoist w') (V' t) ((Concert.aperture hF).within ⟨w',h⟩) _ _ _ hX ?_))) --explicit
  change G' • Pond.swim U (Pond.spill U (Pond.swim U z))=G' • Pond.swim _ _; rw [Pond.settled]
end YM.UVExtension.Linden
