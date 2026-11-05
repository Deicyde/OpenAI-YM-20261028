import YM.UVExtension.Willow.Fires
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Willow
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
open PhysicalNext.Repeat
variable (K : Festa Q L H V b B) (hx:X.x=x) (hX : X.width=o.K) (hm:X.manifest)
    (p : Molecule S) (M:Lotus.Leaf R) (hl:Lines R V b (betaF G x L) M) -- using PhysicalNext.Repeat to open
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => grains X R W o.a Q.table Q.halo V M p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
local notation "Γ" => (F.order G).prod X.dice
local notation "Δ" => (F.order G).prod (volume : Measure (Body (↥Kp)))
def whorls (t:Vines ι) := ∫ y,lantern (H:=H) (V:=V) X p M t y ∂ Δ
local notation "A" => lantern (H:=H) (V:=V) X p M
include K H hx hl hX hm
lemma wrung (X':Drums ι) (hz:Λ X') : whorls (H:=H) (V:=V) X p M (hoist X')= ↑((hl.leaf X' hz).tithe X (Matter.own p) W o.a Q.table Q.halo p):=by
  let z:= hoist X'; let u:= X' none
  have hp := (H.laws.data.localP _ X hx hX hm).sails.fullC
  let R':= chunk R (blend V (X'∘some)) u; let M':= hl.leaf X' hz
  let I:= Kp; let c':= Pond.circuit I X.relating
  let H':= (K.mixture X' hz).some
  have hd:c'.PosDef:= hp.submatrix Subtype.val_injective
  have hu:0<u := breath (altitude (H:=H)) (show ((u:ℂ))∈ aisle _ from hz none)
  let f i:= M'.into X W o.a Q.table (Matter.own p) Q.halo p i; let g (i:F.Slice G × Body (↥I)):ℝ := f (i.1,Pond.spill I i.2)
  have hs:Intake _ _ X.x R':= hx.symm ▸ H'.laws.intake
  have hf:Measurable f:= M'.crystall X _ hs (by rw [hx,hX]; exact H.laws.data.access) Q.table_exists ..
  have hg: Measurable g:= hf.comp (measurable_fst.prodMk ((spill_m I).comp measurable_snd))
  have hh (i:F.Slice G× Body (↥I)) : A z i= (↑(tether c' u g i:ℝ):ℂ):= by
    unfold lantern; rw [trains X p M hl X' hz (H:=H)]; rw [show z none = (u:ℂ) from rfl,voiced _ _ hu]
    rw [tether]; unfold g; dsimp only; rw [Festa.spilling,smul_eq_mul]; push_cast; rfl
  unfold whorls Leaf.tithe
  change (∫ i,A z i ∂Δ)= Complex.ofReal (∫ i,f i ∂Γ)
  simp_rw [hh]; rw [integral_complex_ofReal,← axle _ c' hd hu]; apply congr_arg Complex.ofReal
  let μ:=(F.order G).prod (arch I X.relating); let P:= sweeping X I hp
  change (∫ i,g i ∂μ)=_; rw [show μ=Measure.map _ Γ from P.map_eq.symm, integral_map P.measurable.aemeasurable hg.aestronglyMeasurable]; apply integral_congr_ae; filter_upwards with v
  exact M'.concur (X.wrapY v.1) _ (X.wrapY v.1) ⟨Village.refl ..,(Pond.observe I).1 (Pond.settled ..),fun _ _=>Iff.rfl⟩ (show Room _ _ T X.x from hx.symm ▸ H.laws.data.room) Q.buys (by change ground R T Q.halo (radiusB X.x) p ⊆ _; rw [hx]; exact Finset.Subset.refl _) hs

omit hx K hl hX hm in
lemma quietL (h : M.turn.badge S∉ p): whorls (H:=H) (V:=V) X p M=0 := by
   funext v; unfold whorls lantern grains; dsimp only; simp_rw [if_neg h,mul_zero,integral_zero]; rfl

def treeP (X:Coat T F) (p : Molecule S) (z:Vines ι) := if Matter.standsIn X R Q.halo p then (Fintype.card S.Choices:ℂ)⁻¹*∑ i,whorls (H:=H) (V:=V) ((planted X p).taggedL i) p M z else 0
omit hm
lemma gates (d:Drums ι)(h:Λ d): treeP (H:=H) (V:=V) M X p (hoist d)= ↑((hl.leaf d h).bloom X W o.a Q.table Q.halo p):=by
   have hh: Matter.standsIn X R Q.halo p ↔ Matter.standsIn X (chunk R (blend V (d ∘ some)) (d none)) Q.halo p:= (Iff.rfl : Matter.standsIn X R Q.halo p ↔ Matter.standsIn X (chunk R (blend V (d∘ some)) (d none)) Q.halo p); unfold treeP Leaf.bloom; rw [hh]; split; swap; · rw [Complex.ofReal_zero]
   simp_rw [fun i=> wrung ((planted X p).taggedL i) K hx hX (planted_valid ..) p M hl d h]; unfold Leaf.steep likely; push_cast; rfl
end YM.UVExtension.Willow
