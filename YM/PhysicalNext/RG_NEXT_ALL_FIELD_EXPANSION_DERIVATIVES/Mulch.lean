import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.Next.ROTATIONS.Response
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.SectorNext.RECONNECTED_LOCALITY.Weld


/-! # Splitting variants in the disjoint gas (scalar probability)

Use even when some ID types empty. No quotient of legs with overlapping Y variables;
this is on ALREADY independent footprints, not to exchange factor averaging.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Bower.Variants
open Function Filter Lattice RG Tree Push Push.SectorMeasure Finset MeasureTheory AbsoluteSums LogIdentity
open scoped Topology BigOperators Classical
variable {c : Side} {ι ν : Type}

def pairIn (s : Finset ι) (w : ↥s → ν) : ↥s ↪ (ν × ι) := ⟨fun i=> (w i,i.val),fun _ _ he=> Subtype.ext (congr_arg Prod.snd he)⟩

def labelL (p : (s : Finset ι) × (s → ν)) := univ.map (pairIn p.1 p.2)
lemma answer (s : Finset ι) (w : ↥s → ν) (i : ν × ι) : i∈labelL ⟨s,w⟩ ↔ ∃ a : i.2∈s,i.1=w ⟨i.2,a⟩ := by
  rcases i with ⟨b,i⟩; constructor
  · intro hi; obtain ⟨⟨j,hj⟩,ht,h⟩:= mem_map.mp hi; obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; exact ⟨hj,rfl⟩
  rintro ⟨a,ha⟩; have ht : b=w ⟨i,a⟩:=ha; simp only at a ha; subst b; exact mem_map_of_mem _ (mem_univ (α:=↥s) ⟨i,a⟩)
lemma facts (p : (s : Finset ι) × (s → ν)) : (labelL p).image Prod.snd=p.1 := by
  rcases p with ⟨s,p⟩; ext i; rw [mem_image]; constructor
  · rintro ⟨j,hj,rfl⟩; exact (mem_map.mp hj).elim fun i h=> (congr_arg Prod.snd h.2).symm ▸ i.property -- sign
  intro hi; exact ⟨_,mem_map_of_mem (pairIn s p) (mem_univ (⟨i,hi⟩:↥s)), rfl⟩
lemma label_safe : Injective (labelL (ν:=ν) (ι:=ι)) := by
  rintro ⟨s,w⟩ ⟨t,v⟩ h; have he : s=t := by rw [← show (image _ (labelL ⟨s,w⟩))=s from facts ⟨s,w⟩]; exact h ▸ facts ⟨t,v⟩ -- dependency rw
  subst t
  refine congr_arg (Sigma.mk s) (funext fun i=>?_)
  have ht : (w i,i.val) ∈ labelL ⟨s,w⟩ := (answer s w _).2 ⟨i.2,rfl⟩
  rw [h] at ht; exact ((answer s v _).1 ht).choose_spec
lemma outside {X : ι→ Support c} (h : ∀ i,(X i).Nonempty) {p : Finset (ν × ι)} (hp : Apart (X ∘ Prod.snd) p) : p∈ Set.range labelL := by
  let t := p.image Prod.snd
  have hh : Set.InjOn Prod.snd (p:Set (ν × ι)) := by
    intro i hi j hj he; by_contra hw
    obtain ⟨k,hk⟩ := h i.2; exact disjoint_left.mp (hp hi hj hw) hk (show k∈X j.2 from he ▸ hk)
  have he (i : ↥t) : ∃ v : ν,(v,i.val)∈p := by
    obtain ⟨v,hv,hx⟩ := mem_image.mp i.property; rw [← hx]; exact ⟨v.1,hv⟩
  choose g hg using he; refine ⟨⟨t,g⟩,?_⟩; ext i; rw [answer]; constructor
  · rintro ⟨a,w⟩; exact (show i=(g ⟨i.2,a⟩,i.2) from Prod.ext w rfl) ▸ hg _
  intro hi; have ha:= mem_image_of_mem Prod.snd hi; exact ⟨ha,congr_arg Prod.fst (hh hi (hg (⟨i.2,ha⟩:↥t)) rfl)⟩

variable [Fintype ν] (X I : ι → Support c) (D : Support c) (f : ι → ℝ)
abbrev gently (ν : Type) [Fintype ν] := gasTerm (X ∘ Prod.snd (α:=ν)) (I ∘ Prod.snd) D
  (fun p => (Fintype.card ν:ℝ)⁻¹*f p.2)
omit [Fintype ν] in
lemma attests (s : Finset ι) (v : ↥s → ν) : LogIdentity.Records X I D s ↔ LogIdentity.Records (X ∘ Prod.snd) (I ∘ Prod.snd) D (labelL ⟨s,v⟩) := by
  let Z:=labelL ⟨s,v⟩
  have h : Z.biUnion (I ∘ Prod.snd)= s.biUnion I := by rw [← show (Z.image Prod.snd).biUnion I=s.biUnion I from congr_arg (fun Z=> Z.biUnion I) (facts ⟨s,v⟩)]; rw [image_biUnion]; rfl
  unfold Records; rw [h]; refine and_congr_left fun _=>?_ ; constructor
  · intro hp i hi j hj hn
    obtain ⟨i,ht,rfl⟩ := mem_map.mp hi; obtain ⟨j,hv,rfl⟩:= mem_map.mp hj; exact hp i.property j.property (fun he=>hn (congr_arg (pairIn s v) (Subtype.ext he)))
  intro hp i hi j hj hn; exact hp (mem_map_of_mem (pairIn s v) (mem_univ (⟨i,hi⟩:↥s)))
    (mem_map_of_mem (pairIn s v) (mem_univ (⟨j,hj⟩:↥s))) (fun he=> hn (congr_arg Prod.snd he))
lemma each_label (s : Finset ι) (v : ↥s→ν) : gently X I D f ν (labelL ⟨s,v⟩)=(Fintype.card ν : ℝ)⁻¹^s.card*gasTerm X I D f s := by
  unfold gently gasTerm; rw [← attests]; split
  next h=> rw [labelL,prod_map]; change (∏ i : ↥s,(Fintype.card ν : ℝ)⁻¹*f i.val)=_; rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_coe,prod_coe_sort s]
  simp

variable (ν) [Nonempty ν] (hs : Summable (gently X I D f ν))
include hs
lemma total (hX : ∀ i,(X i).Nonempty) : Summable (gasTerm X I D f) ∧ (∑' p,gently X I D f ν p)=∑' p,gasTerm X I D f p := by
  let g := gently X I D f ν
  have h i : i∉Set.range labelL→ g i=0 := fun he=> if_neg (fun ht=> he (outside hX ht.1))
  let f := g ∘ labelL; have hf : Summable f := hs.comp_injective label_safe; have hg := hf.sigma' -- names
  have hc : 0 < (Fintype.card ν : ℝ) := by positivity
  have hv (s : Finset ι) : (∑' i,f ⟨s,i⟩)= gasTerm X I D ‹ι → ℝ› s := by
    unfold f g comp; rw [tsum_fintype]; simp_rw [each_label X I D]; simp
  constructor
  · simp_rw [hv] at hg; exact hg (fun i=> (hasSum_fintype _).summable)
  rw [← label_safe.tsum_eq (Function.support_subset_iff'.mpr h)]; change ∑' i, f i = _; rw [hf.tsum_sigma]; exact tsum_congr hv
end YM.PhysicalNext.Bower.Variants
