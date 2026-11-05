import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Interior

/-! # Stable readers

Our expensive, completion-relative purchasing `Viewport` was allowed
to invite MORE frozen arguments; account for that postage (doesn't
consume Z caps, is probability Haar, & all STILL located in X). At
handoff don't have that privilege: show that we anyway evaluate from
the *static* spaces and the integral price on the original Roster
letters exactly computes this **local** unforced coefficient. In
particular, no cross-V comparison of matrices rerolled after removing
defaults or arguing a test that fails at fixed y is absent from cost!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Arbor
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian Spot AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.Push.SectorMeasure
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment   Route SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art I D) (h : Lit D) (F : Forest S.ratio) (k₀ k : S.Choices) (V : Config G c)
    (i : Ensign S I) (hI : privilege D Z F V i)
local notation "x₀"=>D.betaHat
local notation "B"=>radiusB x₀
local notation "X₀"=>wood D Z i
local notation "K"=> Shipment.key D Z i
local notation "W₀"=>Route.Badge.near K
local notation "A₀"=>Shipment.station i
local notation "A₁"=>Route.patch x₀ V A₀
local notation "P"=> Native.kinetic D.tube F k₀ x₀

include hI
lemma powers : (A₀).flags ⊆ (A₁).flags := fun _ hi=> Finset.mem_inter.mp (hI.2.2.symm ▸ hi)|>.2
-- agreement even station's contradicting *outside* flag data.
lemma reads {k k' : S.Choices} {U V' : Config G c} (he : Tags.Synchronized X₀ k k') (hx : Agrees X₀ U V') :
    Physical.Reads X₀ A₀ A₁ F F U V' k k' := by
  refine ⟨hx,he.1,fun j hj=>he.2 j (hj (Finset.mem_insert_self ..)) (hj (by simp [pinPos])),fun _ _ _=>Iff.rfl,
    fun r hr=>?_,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩
  have h0 := hr (show r∈inspected ({r}:Support c) from Finset.mem_union_left _ (Finset.mem_singleton_self _))
  constructor
  · exact fun hv => powers D Z F V i hI hv
  exact fun ha=> hI.2.2 ▸ (Finset.mem_inter.mpr ⟨h0,ha⟩)

local notation "Y"=>indoor D Z i
include k h
lemma chilled (e : F.Free) (he : S.ratio.parent e.val.1∈Y) : chill A₀ x₀ F e ↔ chill A₁ x₀ F e := by
  have ht := reads D Z F V i hI (show Tags.Synchronized X₀ k k from ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩)
    (show Agrees X₀ V V from fun _ _ _=>rfl)
  have hr := ht.frozen_bits h.aperture.scale e.val (ledge D Z i _ he)
  rw [← Print.sees_frost x₀ _, ←Print.sees_frost x₀ _] -- sees_frost needs implicit etc
  exact Print.winter_read x₀ ht e.val h.aperture.scale (ledge D Z i _ he)

omit k h in
lemma advance (e : F.Free) (ht : chill A₀ x₀ F e) : chill A₁ x₀ F e := by
  have hp : (A₀).dome (10*B)⊆(A₁).dome (10*B) := by
    apply Corona.halo_mono le_rfl
    exact fun x hx=> Finset.mem_union.mp hx |>.elim (fun h=>Finset.mem_union_left _ h)
      (fun he=>Finset.mem_union_right _ (powers D Z F V i hI he))
  exact ht.imp (fun H=>hp H) (fun H=>hp H)

local notation "R₀"=> Badge.ribbon K F A₀
local notation "R₁"=> Badge.ribbon K F A₁

private def subIncl {α : Type} (a b : Finset α) (h : a ⊆ b) : ↥a ↪ ↥b :=
  ⟨fun i=>⟨i.val,h i.property⟩,fun _ _ ht=>Subtype.ext (congr_arg (fun i:↥b=>i.val) ht)⟩
lemma hoist : (R₀).frost ⊆ (R₁).frost := by
  intro a ha
  obtain ⟨hi,hj⟩:= (show _ ∧ S.ratio.parent a.val.1∈X₀ ∧ S.ratio.parent (a.val.1+Lattice.step a.val.2)∈X₀ from (Finset.mem_filter.mp ha).2)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,advance D Z F V i hI a hi,hj⟩
def frosted := subIncl _ _ (hoist D Z h F k V i hI)

lemma warm (a : F.Free) : a∈ (R₀).breeze ↔ a ∈ (R₁).breeze := by
  simp only [Badge.ribbon,Badge.tests,Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_congr_left fun he=> not_congr (chilled D Z h F k V i hI a (halo_subset (55*B) _ he.1))

def breathing : (R₀).lit G ↪ (R₁).lit G := Embedding.prodMap (subIncl _ _ (fun x hx=> (warm D Z h F k V i hI x).mp hx)) (Embedding.refl _)

abbrev Policy := (R₀).Page G

def print (p : (R₁).Page G) : Policy D Z F i :=
    (p.1 ∘ (frosted D Z h F k V i hI), p.2 ∘ (breathing D Z h F k V i hI))

set_option maxHeartbeats 50000 in
-- keep these defeq arguments out of the comparison on the big physical indices
omit k h hI in
private lemma reindex {x : ℝ} {X : Support c} {A A' : Stores S} (b : Badge S x X) {p : (b.ribbon F A').Page G}
    (hv : (b.ribbon F A).frost ⊆ (b.ribbon F A').frost) (hw : ∀ a, a∈ (b.ribbon F A).breeze ↔ a∈(b.ribbon F A').breeze)
    (e : F.Free) :
    let r:= Embedding.prodMap (subIncl _ _ (fun x hx=> (hw x).mp hx)) (Embedding.refl G.ColorIndex)
    let q : (b.ribbon F A).Page G := (p.1 ∘ subIncl _ _ hv,p.2 ∘ r)
    (b.embroider (x:=x) (F:=F) (O:=A) q).2 e.val=(b.embroider (F:=F) (O:=A') p).2 e.val := by
  intro r q
  unfold Badge.embroider; dsimp only; rw [dif_pos e.property,dif_pos e.property]
  by_cases h : e∈(b.ribbon F A).breeze
  · rw [dif_pos h,dif_pos ((hw e).mp h)]; -- tactic `rfl` might struggle with tape field defeq due transparency; explicit via Prod
    change tape (p.2 ∘ r) (⟨e,h⟩) = tape p.2 (⟨e,(hw e).mp h⟩ : ↥(b.ribbon F A').breeze); -- tape simp
    ext j; rw [tape_ap,tape_ap]
    unfold Function.comp; apply congr_arg p.2; unfold r; simp only [Embedding.prodMap, Embedding.coeFn_mk]; rfl
  rw [dif_neg h, dif_neg (mt (hw e).mpr h)]

lemma opt (p : (R₁).Page G) :
    Same S Y W₀ ((K).embroider (print D Z h F k V i hI p)) ((K).embroider p) := by
  refine ⟨fun r ht hx =>?_,fun r ht hx=>?_⟩
  · unfold Badge.embroider; dsimp only
    split; swap; rfl
    rename_i hh
    let w:F.Free:=⟨r,hh⟩
    have he : S.ratio.parent r.1∈X₀ := (ledge D Z i _ ht).center
    have hv : S.ratio.parent (r.1+Lattice.step r.2)∈X₀ := (ledge D Z i _ hx).center
    have ho : w∈ (R₀).frost ↔ w∈(R₁).frost := by
      unfold Badge.ribbon Badge.dreams; simp only [Finset.mem_filter,Finset.mem_univ,true_and,w,he,hv,and_self,and_true]; exact chilled D Z h F k V i hI w ht
    by_cases hz : w∈(R₀).frost
    · rw [dif_pos hz,dif_pos (ho.mp hz)]; rfl
    rw [dif_neg hz,dif_neg (mt ho.mpr hz)]
  by_cases he : r∉ F.trunks
  · exact reindex F (K) (hoist D Z h F k V i hI) (warm D Z h F k V i hI) ⟨r,he⟩
  unfold Badge.embroider; simp [of_not_not he]

-- entry representation of *actual* local Gaussian at station (Display
-- ordering would be by Hues; here leave it at `breeze`).
open Completion

def index (a : (R₀).lit G) : Full G f := (a.1.val.val,a.2)
def service : Gaussian.Table ((R₀).lit G) :=
    (cloudX D.tube x₀ k V A₀ F).submatrix (index D Z F i) (index D Z F i)

local notation "H"=>Shipment.theater D Z h F k₀ V

omit hI k in
lemma aired {k k' : S.Choices} {U V' : Config G c} (he : Tags.Synchronized X₀ k k') (hx : Agrees X₀ U V') :
    Arbor.service D Z F k U i=Arbor.service D Z F k' V' i := by
  let a := (A₀)
  have hr : Physical.Reads X₀ a a F F U V' k k' := ⟨hx,he.1,fun j hj=>he.2 j (hj (Finset.mem_insert_self ..)) (hj (by simp [pinPos])),fun _ _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩
  ext l t
  apply cloudX_read D.tube x₀ h.aperture hr
  have hv : S.ratio.parent t.1.val.val.1 ∈ W₀ := (Finset.mem_filter.mp t.1.property).2.2.1
  have hs : Shields X₀ _ (20*B) := widen' (covers_shield _ hv) (K).sewn
 
  exact hs.shrink (by omega)

omit k h hI in
private lemma light {x : ℝ} {X : Support c} {A A' : Stores S} (q : Badge S x X)
    (ht : (q.ribbon F A).breeze⊆(q.ribbon F A').breeze) (a : (q.ribbon F A).lit G) :
    let w:=Embedding.prodMap (subIncl _ _ ht) (Embedding.refl G.ColorIndex)
    let r : (q.ribbon F A').lit G ↪ In x A' F:=Ribbon.lighten (q.here F A')
    ((a.1.val.val,a.2) : Full G f)=Wires.active x A' F (r (w a)) := by
  intro w r
  rw [Wires.active,Wires.finger,Completion.sorted_first]
  rfl

lemma serviced (a b : (R₀).lit G) :
    Arbor.service D Z F k V i a b = (H).air i k (breathing D Z h F k V i hI a) (breathing D Z h F k V i hI b) := by
  have hr := reads D Z F V i hI (show Tags.Synchronized X₀ k k from ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩)
    (show Agrees X₀ V V from fun _ _ _=>rfl)
  let u:=breathing D Z h F k V i hI
  calc
    _ = (cloudX D.tube x₀ k V A₁ F) (index D Z F i a) (index D Z F i b) :=
      cloudX_read D.tube x₀ h.aperture hr _ _ (by
        have hv : S.ratio.parent b.1.val.val.1 ∈ W₀ := (Finset.mem_filter.mp b.1.property).2.2.1
        have hs : Shields X₀ _ (20*B) := widen' (covers_shield _ hv) (K).sewn
        exact hs.shrink (by omega))
    _ = _ := by
      let r : (R₁).lit G ↪ In x₀ A₁ F:= Ribbon.lighten ((K).here F A₁)
      rw [show index D Z F i a=Wires.active x₀ A₁ F (r (u a)) from ?_,show index D Z F i b=Wires.active x₀ A₁ F (r (u b)) from ?_]
      · exact Badge.cloud_earned D F A₁ k V h.toApp rfl ..
      · exact light F (K) (fun e he=>(warm D Z h F k V i hI e).mp he) b
      exact light F (K) (fun e he=>(warm D Z h F k V i hI e).mp he) a
end YM.PhysicalNext.Dictionary.Arbor
