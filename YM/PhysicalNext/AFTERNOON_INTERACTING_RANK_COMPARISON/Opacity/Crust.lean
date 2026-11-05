import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bolt
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Beam
import YM.Push.STRESS_FLUX.Orbits


/-!
# Literal mask roster at the micro density

Keep every overlapping fine and drive entry and BOTH k tag arrays. At all
fields, ticket mass retains possibly far predictor. Reading locations remember orientations; Hears uses absolute addresses in this input. `arc` always post-L actual width. Nothing charged to cut approximate modes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S}
    {F F' : Forest S.ratio} {k k' : S.Choices} {X X' : Support c} {p q : Pilot G S x} {P : Teller G}
abbrev Fleck (_S : StepData c f) := Cell f ⊕ Bond c ⊕ Site c ⊕ Bond c ⊕ Bond f

def pursuit (S : StepData c f) (e : Wheel c): Equiv.Perm (Fleck S) := _root_.Equiv.sumCongr (shiftFaces e.1 (S.ratio.embed e.2)) <| _root_.Equiv.sumCongr (StepData.sendBonds e.1 e.2) <| Equiv.sumCongr (orient e) (Equiv.sumCongr (StepData.sendBonds e.1 e.2) (StepData.sendBonds e.1 (S.ratio.embed e.2)))
-- footprints (not stencils). Aff.points Finset

def foot (S : StepData c f): Fleck S → Support c := Sum.elim (startPos S) (Sum.elim pinPos (Sum.elim ({·}) (Sum.elim pinPos (Aff.points S))))
def toes (S : StepData c f) : Fleck S → Site c := Sum.elim (S.ratio.parent ∘ Prod.fst) (Sum.elim Prod.fst <| Sum.elim id (Sum.elim Prod.fst (Aff.home S)))

lemma footfall (S : StepData c f) (i : Fleck S): toes S i∈foot S i := by
  rcases i with i|i|i|i|i
  · exact Packets.contains S (.inl i)
  · exact Packets.contains S (.inr (.inl i))
  · exact mem_singleton_self _
  · exact Packets.contains S (.inr (.inl i))
  exact Aff.pin_origin ..
lemma strides (S : StepData c f) (i : Fleck S) (a : Site c) (h : a ∈ foot S i): separation (toes S i) a ≤ 1 := by
  rcases i with i|i|i|i|i
  · exact Packets.price_one S (.inl i) a h
  · exact Packets.price_one S (.inr (.inl i)) a h
  · rw [mem_singleton.mp h]; simp [toes]
  · exact Packets.price_one S (.inr (.inl i)) a h
  exact Aff.pin_radius i a h
lemma foot_ship (e : Wheel c) (i : Fleck S): pushed e (foot S i) = foot S (pursuit S e i):= by
  rw [pushed,Finset.map_eq_image]
  rcases i with i|i|i|i|i
  · exact (Locations.start_map ..).symm
  · exact (Locations.pin_map ..).symm
  · exact image_singleton ..
  · exact (Locations.pin_map ..).symm
  let s:=e.1; let b:=S.ratio.embed e.2
  change (Aff.points S i).image _=Aff.points S (sendEdge s b i)
  have hA (i : Bond f): (↑(Aff.points S i) : Set (Site c))=Next.SectorChange.points S i:= by ext; simp only [Aff.points,Next.SectorChange.points]; simp [pinPos]
  apply Finset.coe_injective; rw [coe_image,hA,hA]; exact (Tensor.moves_points ..).symm
namespace Dyed
variable (v : Dyed G S) (W : ℝ)

def door (p : Pilot G S x) (i : Bond f) := if h : i∈Aff.activeB p.key p.park (radiusB x) then Next.SectorChange.broad v.chi v.arc (v.tapeAt p (Milk.fundedB i h)) else 1
lemma active_door (j : Active p.key x p.park): door v p j.val.val=Next.SectorChange.broad v.chi v.arc (v.tapeAt p j):= dif_pos ((Milk.stillActive ..).2 j.property)
lemma doors_pay (p : Pilot G S x): doors v.chi v.arc (v.tapeAt p)=∏ i,door v p i:= by
  let I:= Aff.activeB p.key p.park (radiusB x)
  rw [← Finset.prod_subset (subset_univ I)]; swap; · intro i _ hi; exact dif_neg hi
  apply Finset.prod_bij (fun (j:Active p.key x p.park) _ => j.val.val)
  · exact fun j _=> (Milk.stillActive ..).2 j.property
  · exact fun _ _ _ _ h=>Subtype.ext (Subtype.ext h)
  · exact fun i hi=> ⟨Milk.fundedB i hi,mem_univ _,rfl⟩
  exact fun j _=> (active_door v j).symm

def ask (p : Pilot G S x): Fleck S → ℝ :=
  let U:=v.top p
  Sum.elim (Aff.fine p.key v.chi x U) (Sum.elim (Aff.wireMask p.key v.chi W x U p.tag p.view) (Sum.elim (fun j=> Aff.αSite U j p.tag) (Sum.elim (fun j=> Aff.αBond U j p.tag) (door v p))))

lemma pursues (p : Pilot G S x) (hp : Matched p) :
    (v.chi.distribute p.key x W (v.top p) p.tag p.view)*(Fintype.card S.Choices:ℝ)*S.likelihood (v.top p) p.tag * doors v.chi v.arc (v.tapeAt p)= ∏ i,ask v W p i := by
  rw [Cab.actual_tag, Aff.thread _ _ _ _ _ _ _ hp, doors_pay]
  simp only [Fleck,Fintype.prod_sum_type,ask,Sum.elim_inl,Sum.elim_inr]; field_simp
-- expose full core with sign later

def Playing (p : Pilot G S x):= (∏ i,ask v W p i) ≠0
lemma participates (hw : 0<W) (hD : 0<fiery G x S.patch.L) (p : Pilot G S x) (hp : Matched p) (h : Playing v W p) :
    Seeded p.key (v.top p) p.tag p.view x W ∧ Alive S (v.top p) p.tag ∧ doors v.chi v.arc (v.tapeAt p)≠0:= by
  unfold Playing at h; rw [← pursues v W p hp] at h
  obtain ⟨hp,hS⟩:= mul_ne_zero_iff.mp h; obtain ⟨hg,hk⟩:= mul_ne_zero_iff.mp hp
  refine ⟨(v.chi.profiles G S x W hw hD).actual _ _ _ _ (left_ne_zero_of_mul hg),?_,hS⟩
  by_contra h; exact hk (dead h)

-- standalone readability BEFORE any angular purchase
lemma top_read (h : Boosted v.things P x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) : ShellView (fun V y=> v.top (x:=x) ⟨A,F,k,V,y⟩) := by
  let O:= Orchard.alone S F
  let L: Lantern G S := ⟨v.chi,v.arc,hd,hr,O⟩
  obtain ⟨p,hp,hx⟩:= gazed_tag h L v.source.beta A ⟨(fun _=> 0),k⟩
  exact ⟨p,hp,fun V h y=> (hx V h y).symm⟩

lemma tape_read (h : Boosted v.things P x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (i : Active A x F) : ShellView (fun V y=> tapeAt v ⟨A,F,k,V,y⟩ i):= by
  let H (p : Config G c × RoomView A x F G) := (p.1,Dictionary.Print.backdrop x A F p.2)
  let g:= coupling v.source.beta
  refine ⟨_,(Dictionary.Print.shade_meas v.things x v.chi v.arc g h.funded k A F hd hr i.val.val).comp (show Measurable H from measurable_fst.prodMk ((recording x A F).comp measurable_snd)), fun V hp y=>?_⟩
  obtain ⟨s, hs⟩:= h.license A F V hp; obtain ⟨_,hb,hQ⟩:= h.enough A F V k hp
  have he:= Dictionary.Print.tinting v.things x v.chi v.arc g k i V h.produced hs hb hQ (Dictionary.Print.backdrop x A F y)
  dsimp only at he; rw [Dictionary.Print.rollback] at he; exact he.symm

lemma door_budget (h : Boosted v.things P x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (i : Bond f) : ShellView (fun V y=> door v (x:=x) ⟨A,F,k,V,y⟩ i):= by
  unfold door; dsimp only; by_cases he : i∈Aff.activeB A F (radiusB x)
  · simp_rw [dif_pos he]; obtain ⟨p,hp,hx⟩:= tape_read v h hd hr A F k (Milk.fundedB i he); exact ⟨_,(Next.SectorChange.broad_smooth v.chi _).continuous.measurable.comp hp,fun V he y=>congr_arg (Next.SectorChange.broad v.chi v.arc) (hx _ he y)⟩
  simp_rw [dif_neg he]; exact ⟨fun _ => 1,measurable_const,fun _ _ _=>rfl⟩
lemma footage (h : Boosted v.things P x) (hd : 0<v.arc) (hr : 2*v.arc<firstRadius G) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (i : Fleck S) : ShellView (fun V y=> ask v W (x:=x) ⟨A,F,k,V,y⟩ i):= by
  obtain ⟨u,hu,H⟩:= top_read v h hd hr A F k
  obtain ⟨h1,h2,h3,h4,h5⟩:= Canvas.gates_meas v.chi A x W k h.produced.branched ∅ v.source.activities hu (V:=fun p=>p.1) measurable_fst
  rcases i with i|i|i|i|i
  · exact ⟨_,h1 i,fun V h y=>congr_arg (fun c=> Aff.fine A v.chi x c i) (H _ h _)⟩
  · exact ⟨_,h2 i,fun V h y=>congr_arg (fun c=> Aff.wireMask A v.chi W x c k V i) (H _ h _)⟩
  · exact ⟨_,h3 i,fun V h y=>congr_arg (fun c=> Aff.αSite c i k) (H _ h _)⟩
  · exact ⟨_,h4 i,fun V h y=>congr_arg (fun c=> Aff.αBond c i k) (H _ h _)⟩
  exact door_budget v h hd hr A F k i
end Dyed
end YM.PhysicalNext.InteractingRank.Pump
