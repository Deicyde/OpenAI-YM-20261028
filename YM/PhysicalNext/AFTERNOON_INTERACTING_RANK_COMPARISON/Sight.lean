import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Beamline
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Exposure

/-!
# Compile one bunker (joint Haar/dust/ticket) integration in Rank

For *physical* inserted query. No coalescing between incompatible output
charts. Addresses V-gauge covariant; any overlapping halos paid
before seeking independence. No criterion from remote tolerance gates here.
Permit unforced outputs to use exactly `LocalOn`; if making a forced
output with final flags, all flags in the extent can additionally be read
(with their indicator, *on that V*).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Marker Value
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
    AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.RelativeLogdet AnalyticBridge.Sharp.Tags
    GaugeRoute
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {X X' : Support c} {x τ : ℝ} {U V : Config G c} {A B : Stores S}
    {F : Forest S.ratio} {T : Tube G S} {O : Orchard S} {k k' : Streak O} {P : Teller G}
namespace Nearby
variable {a : RoomView A x k.wood G} {b : RoomView B x k'.wood G} {l : Nearby X U V A B k k'}
lemma iced (h : nearby X a = amplify l b) (i : Frozen A x k.wood) (he : lumen S x X i.val.val) (j : Frozen B x k'.wood) (hi : i.val.val=j.val.val) : a.1 i = b.1 j := by
  let u : Unveiled X A x k.wood :=⟨i,he⟩
  rw [show j=(l.glows u).val from Subtype.ext (Subtype.ext hi.symm)]
  exact congr_fun (congr_arg Prod.fst h) u
lemma flammable (h : nearby X a = amplify l b) (i : Active A x k.wood) (he : lumen S x X i.val.val)
    (j : Active B x k'.wood) (hi : i.val.val=j.val.val) (o) : a.2 (i,o)=b.2 (j,o) := by
  let u : Chargeable G X A x k.wood:=⟨(i,o),he⟩
  rw [show (j,o)=(l.charges u).val from Prod.ext (Subtype.ext (Subtype.ext hi.symm)) rfl]

  exact congr_fun (congr_arg Prod.snd h) u
lemma add_dims (h : nearby X a = amplify l b) (H : X' ⊆ X) : nearby X' a = amplify (l.mono H) b := by
  apply Prod.ext
  · funext i
    exact iced h i.val (fun s hs=> H (i.property s hs)) _ rfl
  funext i; exact flammable h i.val.1 (fun s hs=>H (i.property s hs)) ((l.mono H).charges i).val.1 rfl i.val.2
lemma between_flags (hf : X ∩ flags τ U=X ∩ flags τ V) (H : X' ⊆ X) : X'∩flags τ U=X'∩ flags τ V := by rw [← Finset.inter_eq_left.mpr H]; rw [Finset.inter_assoc,Finset.inter_assoc, hf]
end Nearby

abbrev rotate_bus (x : ℝ) (z : Site c→G.El) (a : RoomView A x F G) :=
    ((sendFrozen S z x A F a.1),Curved.toGauge z A F x *ᵥ a.2)

abbrev Shader (G : Gauge) (S : StepData c f) (x : ℝ) (O : Orchard S) (E : Type*) := ∀ A : Stores S, ∀ k : Streak O, Config G c→RoomView A x k.wood G → E

def auditFlags (Y : Prop) (τ : ℝ) (X : Support c) (U V : Config G c) := Y → X ∩ flags τ U=X∩flags τ V

structure Sees {E : Type*} [MeasurableSpace E] (r : Shader G S x O E) (X : Support c) (Y : Prop) (τ : ℝ) : Prop where
  placed (A : Stores S) (k : Streak O) : ShellView (r A k)
  held {A B : _} {U V : _} {k k' : _} (p : Positioned x A U) (q : Positioned x B V) (h : Nearby X U V A B k k') (H : auditFlags Y τ X U V)
       (a b) (he : nearby X a = amplify h b) : r A k U a=r B k' V b
  spun {A : Stores S} {V : Config G c} (k : Streak O) (v : Site c→G.El) (m : Positioned x A V) (b) : r A k V b=r A k (Lattice.gauge v V) (rotate_bus x v b)

namespace Sees
section
variable {E E' : Type*} [MeasurableSpace E] [MeasurableSpace E'] {Y Z : Prop} {r : Shader G S x O E}
lemma larger (hr : Sees r X Y τ) (h : X ⊆ X') (H : Y→Z) : Sees r X' Z τ :=
  ⟨hr.placed,fun hp hq hl he a b hw => hr.held hp hq (hl.mono h) (fun hz=> Nearby.between_flags (he (H hz)) h) a b (Nearby.add_dims hw h),hr.spun⟩
lemma constant (u : E) : Sees (fun _ _ _ _=>u : Shader G S x O E) X Y τ:=
  ⟨fun _ _=>⟨fun _=>u,measurable_const,fun _ _ _=>rfl⟩,fun _ _ _ _ _ _ _ => rfl,fun _ _ _ _ => rfl⟩
lemma comp (hr : Sees r X Y τ) (g : E → E') (h : Measurable g) : Sees (fun A k V y=>g (r A k V y)) X Y τ := by
  refine ⟨fun A k=>?_,fun hp hq hl he a b hw => congr_arg _ (hr.held hp hq hl he a b hw),fun k v hm b=> congr_arg _ (hr.spun k v hm b)⟩
  obtain ⟨p,hp,hx⟩:=hr.placed A k; exact ⟨g ∘ p,h.comp hp,fun U hu p=>congr_arg _ (hx U hu p)⟩
lemma pair (hr : Sees r X Y τ) {g : Shader G S x O E'} (h : Sees g X Y τ) : Sees (fun A k V y=>(r A k V y,g A k V y)) X Y τ := by
  refine ⟨fun A k=>?_,fun hp hq hl he a b hw => Prod.ext (hr.held hp hq hl he a b hw) (h.held hp hq hl he a b hw),fun k v hm b=> Prod.ext (hr.spun k v hm b) (h.spun k v hm b)⟩
  obtain ⟨p,hp,hx⟩:=hr.placed A k; obtain ⟨q,hq,hy⟩:= h.placed A k; exact ⟨fun a=>(p a,q a),hp.prodMk hq,fun U hu a=> Prod.ext (hx U hu a) (hy U hu a)⟩
lemma cake {ι : Type*} [CommMonoid E] [MeasurableMul₂ E] {g : ι → Shader G S x O E} (s : Finset ι) (h : ∀ i∈s,Sees (g i) X Y τ) : Sees (fun A k V y=>∏ i∈s,g i A k V y) X Y τ:= by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact constant 1
  | @insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact ((h i (mem_insert_self ..)).pair (ih fun j hj=>h j (mem_insert_of_mem hj))).comp (fun z=> z.1*z.2) (measurable_fst.mul measurable_snd)
end
end Sees

private def lab (X : Support c) (a : Cupful G X A x F) : RoomView A x F G :=
  (fun i=> if h : lumen S x X i.val.val then a.1 ⟨i,h⟩ else 1, fun i=> if h : lumen S x X i.1.val.val then a.2 ⟨i,h⟩ else 0)
private lemma lab_meas (X : Support c) : Measurable (lab X (G:=G) (x:=x) (A:=A) (F:=F)) := by
  unfold lab
  refine Measurable.prodMk (measurable_pi_lambda _ fun i=>?_) (measurable_pi_lambda _ fun i=>?_)
    <;> split
    <;> first | exact (measurable_pi_apply _).comp measurable_fst | exact (measurable_pi_apply _).comp measurable_snd | exact measurable_const
private lemma snapshot (a : Cupful G X A x F) : nearby X (lab X a)=a := by
  apply Prod.ext
  · funext i; unfold nearby lab; dsimp only; rw [dif_pos i.property]
  funext i; unfold nearby lab; dsimp only; rw [dif_pos i.property]
lemma integrate_beam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {r : Shader G S x O E} {Y : Prop} (hr : Sees r X Y τ) (ht : Boosted T P x) (hp : Positioned x A U) (hq : Positioned x B V)
    (hm : Nearby X U V A B k k') (H : auditFlags Y τ X U V) :
    (Integrable (r A k U) (viewer T A x k.wood k.tag U) ↔ Integrable (r B k' V) (viewer T B x k'.wood k'.tag V)) ∧
      (∫ a, r A k U a ∂viewer T A x k.wood k.tag U)=(∫ a,r B k' V a∂viewer T B x k'.wood k'.tag V) := by
  let f₁ := r A k U; let f₂ := r B k' V
  let L := amplify (Nearby.same X U A k) (x:=x); let N:=amplify (x:=x) hm
  let g := f₁ ∘ lab X
  let Q₀:= closeup T X A x k.wood k.tag U
  have h1 : f₁=g ∘ L:=funext fun a=> (hr.held hp hp _ (fun _=>rfl) (lab X (L a)) a (snapshot ..)).symm
  have h2 : f₂=g ∘ N:=funext fun b=> (hr.held hp hq hm H (lab X (N b)) b (snapshot ..)).symm
  let μ:= viewer T A x k.wood k.tag U; let ν:= viewer T B x k'.wood k'.tag V
  have hμ:MeasurePreserving L μ Q₀:=beam ht.ready _ (ht.fogged _ _ _ _ hp); have hν:MeasurePreserving N ν Q₀:=beam ht.ready _ (ht.fogged _ _ _ _ hq)
  have hg : Measurable g:=((hr.placed A k).atLens hp).comp (lab_meas _)
  change (Integrable f₁ μ ↔ Integrable f₂ ν) ∧ (∫ a,f₁ a∂μ)=∫ a,f₂ a∂ν
  rw [h2,h1,hν.integrable_comp hg.aestronglyMeasurable,hμ.integrable_comp hg.aestronglyMeasurable]
  have h := integral_map (μ:=μ) hμ.measurable.aemeasurable (f:=g) hg.aestronglyMeasurable
  have hh := integral_map (μ:=ν) hν.measurable.aemeasurable (f:=g) hg.aestronglyMeasurable
  rw [hμ.map_eq] at h; rw [hν.map_eq] at hh
  exact ⟨Iff.rfl,h.symm.trans hh⟩

lemma whirl (ht : Boosted T P x) (hp : Positioned x A U) (k : S.Choices) (v : Site c→G.El) : MeasurePreserving (rotate_bus x v) (viewer T A x F k U) (viewer T A x F k (Lattice.gauge v U)) := by
  obtain ⟨-, -,-,hW⟩:= Curved.turned_law v A F x P T U k .endpoint 1 Chi.canonical 0 ht.funded (ht.fogged _ _ _ _ (hp.turn v))
  let L:=sendFrozen S v x A F
  have hu: MeasurePreserving L (piHaar G (Frozen A x F)) (piHaar G (Frozen A x F)):=
    measurePreserving_pi _ _ fun i : Frozen A x F=> G.preserve_two_sided (GaugeRoute.fine S v i.val.val) ((v (S.ratio.parent (i.val.val.1+step i.val.val.2)))⁻¹)
  exact hu.prod hW

lemma turn_beam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {r : Shader G S x O E} {Y : Prop} (hr : Sees r X Y τ) (ht : Boosted T P x) (hp : Positioned x A U) (k : Streak O) (v) :
    (∫ a, r A k (Lattice.gauge v U) a ∂viewer T A x k.wood k.tag (Lattice.gauge v U))=(∫ a, r A k U a∂viewer T A x k.wood k.tag U):= by
  have h:= whirl (F:=k.wood) ht hp k.tag v; let V:=Lattice.gauge v U; let μ:=viewer T A x k.wood k.tag U
  have hp' := integral_map (μ:=μ) h.measurable.aemeasurable (f:=r A k V) (((hr.placed A k).atLens (hp.turn v)).aestronglyMeasurable)
  rw [show Measure.map (rotate_bus x v) μ = viewer T A x k.wood k.tag V from h.map_eq] at hp'
  exact hp'.trans (integral_congr_ae (Eventually.of_forall fun a=> (hr.spun k v hp a).symm))

/-- At each physical tag, product of disjoint queries (all of the
H,K reachable here) passes ONE camera cost. -/
theorem peer_beams {ι E : Type} [Fintype ι] [RCLike E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ι → Support c) (r : ι → Shader G S x O E) {Y : ι→Prop} (hr : ∀ i,Sees (r i) (X i) (Y i) τ)
    (ht : Boosted T P x) (h : Pairwise (fun i j => Disjoint (X i) (X j))) (hp : Positioned x A U)
    (k : Streak O) (hm : ∀ i, Integrable (r i A k U) (viewer T A x k.wood k.tag U)) :
    Integrable (fun y=>∏ i,r i A k U y) (viewer T A x k.wood k.tag U) ∧
      (∫ y, (∏ i,r i A k U y) ∂viewer T A x k.wood k.tag U)=∏ i, ∫ y,r i A k U y ∂viewer T A x k.wood k.tag U:= by
  let f (i : ι) := r i A k U; let μ := viewer T A x k.wood k.tag U; let L (i) := closeup T (X i) A x k.wood k.tag U
  let Q : Measure ((i:ι)→ Cupful G (X i) A x k.wood):= Measure.pi L
  let p (i : ι) := f i ∘ lab (X i); let N := fun y i=> nearby (X i) (y : RoomView A x k.wood G)
  have hμ : MeasurePreserving N μ Q:= beam_family X h (ht.fogged A k.wood U k.tag hp)
  have hg i : MeasurePreserving (nearby (X i)) μ (L i):= beam ht.ready (Nearby.same (X i) U A k) (ht.fogged A k.wood U k.tag hp)
  have hf i: Measurable (p i):= (((hr i).placed A k).atLens hp).comp (lab_meas _)
  have hl i (y : RoomView A x k.wood G) : r i A k U y=p i (nearby (X i) y):= (Sees.held (hr i) hp hp (Nearby.same ..) (fun _=>rfl) (lab (X i) (nearby (X i) y)) y (snapshot ..)).symm
  have hκ (i:ι) : Integrable (p i) (L i):= ((hg i).integrable_comp (hf i).aestronglyMeasurable).mp ((hm i).congr (Eventually.of_forall (hl i)))
  have hm i : (∫ y,r i A k U y ∂μ)=∫ y,p i y∂L i:= by
    simp_rw [hl i]; rw [← (hg i).map_eq]
    exact (integral_map (hg i).measurable.aemeasurable (hf i).aestronglyMeasurable).symm
  let c (y : (i:ι)→ Cupful G (X i) A x k.wood) := ∏ i,p i (y i)
  have hc: Integrable c Q:= Integrable.fintype_prod_dep hκ
  have hb := integral_map hμ.measurable.aemeasurable (μ:=μ) (f:=c) (hμ.map_eq.symm ▸ hc.1); rw [hμ.map_eq] at hb
  have he y : (∏ i,r i A k U y)=(c ∘ N) y:=prod_congr rfl (fun i _=>hl i y)
  change Integrable _ μ ∧ (∫ y, (∏ i,r i A k U y) ∂μ)= _
  refine ⟨(hμ.integrable_comp hc.1|>.mpr hc).congr (Eventually.of_forall fun a=> (he a).symm),?_⟩
  calc
    _ = ∫ y,c (N y) ∂μ:= integral_congr_ae (Eventually.of_forall he)
    _ = ∏ i,∫ y,p i y∂L i := hb.symm.trans (integral_fintype_prod_eq_prod p)
    _ = _ := Finset.prod_congr rfl fun i _=> (hm i).symm
end YM.PhysicalNext.InteractingRank
