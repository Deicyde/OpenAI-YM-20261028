import YM.UVExtension.Linden.Shawl
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
variable {X}
section
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (M : PhysicalNext.Repeat.Lotus.Leaf R)(p : Molecule S) (HS:Cash W X.x μ L Q o C T R)(he:X.width=o.K) (hM:X.manifest) (I : Finset (Bond f)) {y:E}{V:E → Config G c}
variable (h:Glass P X V y j W)(hp: Canary G d A)(ha:8*o.a*Pressure.fiery G X.x S.patch.L≤d/2)
include HS he hM h hp ha
omit [FiniteDimensional ℝ E] in
lemma seeds :
    let m:=(F.order G).prod X.dice; let g v:= M.carat I X (V v) d Q.table p W o.a Q.halo
    (∃ B, Integrable B m ∧ ∀ᶠ i in 𝓝 y, ∀ x, Brush j (B x) 1 (fun i=> g i x) i) ∧ ∀ᶠ y in 𝓝 y, Measurable (g y) := by
  intro m g
  have heq:=HS.laws.data; have hv := heq.funds.length_eq;
  have hM :=heq.localP F X rfl he hM
  have ht:= (HS.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [he]; exact heq.access
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
  have hΨ : Zest Φ y j := M.supple X p HS h hp ha
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
  obtain ⟨s,hY⟩:= h.sails; filter_upwards [nearby X hp h.lifts hY] with y hh'
  exact M.docks X (V y) I hp hh' measurable_fst measurable_snd ht hh Q.table_exists p


lemma stepsM : let g v:= M.carat (X:=X) I (V v) d Q.table p W o.a Q.halo
    (∀ x, ContDiffAt ℝ (↑j) (fun i=>g i x) y)∧∀ k≤j,StronglyMeasurable (JetF g k y):=by
  intro g; obtain ⟨⟨B,hB,h⟩,hs⟩:= seeds M p HS he hM I h hp ha
  refine ⟨fun t=>((mem_of_mem_nhds h) t).smooth,fun i hi=>?_⟩
  obtain ⟨u,hu,hU,hv⟩:= _root_.mem_nhds_iff.mp (h.and hs)
  apply Meristem.legs (f:=Function.swap g) hU (fun y t ht=> ((hu ht).1 y).smooth) (fun i hi=> (hu hi).2.stronglyMeasurable) hi hv
end
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
    (M: PhysicalNext.Repeat.Lotus.Leaf R) (hl:Lines R V w (betaF G x L) M)
set_option quotPrecheck false
variable (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
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
include B₀ hS ht hV hX hp hm hr hc Y
lemma harmony (I : Finset (Bond f)) (T':F.Slice G × Air f G){U:Set ℂ} {f':ℂ→Vines ι}(hs:IsOpen U)(hpU:Set.MapsTo f' U Σ)(hv:DifferentiableOn ℂ f' U): Luster U τ j (fun t i=> cA (f' t) I (V' i) T'):=by
   rcases T' with ⟨y,z'⟩; let Y':= X.wrapY y
   apply Luster.mask (f:=fun t i=> bA (f' t) I (V' i) (y,z')) _ (fun t ht'=>bridge N hF M hX hm hr p ht hV _ _ _ (hpU ht')); unfold buffer; dsimp only
   apply (ringlet (X:=Y') N hS hF hX hm hc hr z hz ht hV hv z' I).times; split; swap; · exact Luster.resting contDiffAt_const
   have hp' := funds (X:=Y') N hS hF M hX hm hc hr ht hV Y B₀ z'
   apply (Luster.resting hp'.smooth).times; refine Luster.poll _ _ ?_
   intro i hi; have hp : Healthy (temp Y'.x) (H.supportP i) Y'.V := Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP (mem_of_mem_erase hi)) hp
   rcases i with i|i; swap; · exact bazar (X:=Y') N hS hF hX hm hc hr z hz ht hV hs hpU hv z' B₀.conduit i hp (Matter.own p)
   by_cases hh: Packets.connected S Q.halo X.B i
   · exact pinion (X:=Y') N hS hF hX hm hc hr z hz ht hV hpU hv z' B₀.conduit i hh hp (Matter.own p)
   refine (Luster.resting (f:=fun _:E=>(0:ℂ)) contDiffAt_const).mask (fun i _=> Eventually.of_forall fun y=> ?_); exact if_neg hh

def flax (q:Vines ι) (T':F.Slice G × Air f G):ℂ:= iteratedFDeriv ℝ i (fun t=> cA q Z' (V' t) T') τ Z
local notation "Λx" => flax (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
omit B₀ hp Y
include hl hF hi N
lemma trav (w':Drums ι) (hv:Λ w') (r:F.Slice G × Air f G) : Λx (hoist w') r=
     ↑(iteratedFDeriv ℝ i (fun t=> (hl.leaf w' hv).carat Z' X (V' t) A Q.table p W o.a Q.halo (r.1,Wick.scaled (w' none) r.2)) τ Z : ℝ):=by
   let J:= (hF.mixture w' hv).some
   let R':=chunk R (blend V (w'∘some)) (w' none)
   let f t:= (hl.leaf w' hv).carat Z' X (V' t) A Q.table p W o.a Q.halo (r.1,Wick.scaled (w' none) r.2); let L':= Complex.ofRealCLM
   have hS': Cash W X.x μ L Q o a T R' := hX.symm ▸ J; have ha:8*o.a*Pressure.fiery G X.x S.patch.L ≤ A/2:=by rw [hX,J.laws.data.funds.length_eq]; exact N.foot
   have hs: ContDiffAt ℝ (↑j) f τ:= (stepsM (hl.leaf w' hv) p hS' hr hm Z' ((N.granted _ _ S T _ _ J hS rfl).2 E V' F X τ hX hc hr hm ht hV).1 N.bay ha).1 _
   unfold flax; rcases r with ⟨y,z0⟩
   rw [show (fun i=>pilot ..)=L' ∘ f from funext fun i=> ?_]
   exact congr_arg (fun k:E [×i]→L[ℝ] ℂ=> k Z) (L'.iteratedFDeriv_comp_left hs (by exact_mod_cast hi))
   exact spark (H:=H) M hl p _ _ _ _ hv

lemma stain (w':Drums ι)(hv:Λ w') : StronglyMeasurable (Λx (hoist w')):=by
   let J:= (hF.mixture w' hv).some; let g:E→ F.Slice G × Air f G→ℝ:=fun t=> (hl.leaf w' hv).carat Z' X (V' t) A Q.table p W o.a Q.halo
   have ha:8*o.a*Pressure.fiery G X.x S.patch.L ≤ A/2:=by rw [hX,J.laws.data.funds.length_eq]; exact N.foot
   have hZ: StronglyMeasurable (JetF g i τ):=(stepsM _ p (hX.symm ▸ J) hr hm Z' ((N.granted _ _ S T _ _ J hS rfl).2 E V' F X τ hX hc hr hm ht hV).1 N.bay ha).2 i hi
   have he: StronglyMeasurable (fun y=> ((JetF g i τ y Z:ℝ):ℂ)):= Complex.continuous_ofReal.comp_stronglyMeasurable ((ContinuousMultilinearMap.apply ℝ _ _ Z).continuous.comp_stronglyMeasurable hZ)
   have hp: Measurable (fun t:F.Slice G × Air f G=> (t.1,Wick.scaled (w' none) t.2)):=by unfold Wick.scaled; fun_prop
   rw [funext (trav N hS hF M hl hX hm hc hr p ht hV hi Z w' hv)]; exact he.comp_measurable hp
end YM.UVExtension.Linden
