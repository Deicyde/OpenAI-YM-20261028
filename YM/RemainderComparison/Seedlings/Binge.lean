import YM.RemainderComparison.Seedlings.Tuft
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seedlings
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics
variable {G : Gauge} {c f L: Side} {P:Teller G} {D: RG.Stage} {R:Rep G f}
variable {ι:Type}{α:Type*}{S:StepData c f}{T:Tube G S}{Z:Finset (Head S)}{J:ConnectedActivityE6.Target G P}{o': ℝ}
variable {W p a μ :ℝ}{x : ℝ} {o:Target.Order G W}
   (X:ι→Portrait R α)(y:α)(H:Cash W x μ L J o a T R)
variable (b:Finset ι)
namespace BoxOf
variable (E:BoxOf H) (x₁:Site c)(r n:ℕ)
local notation "X₁"=>brand X y
local notation "U"=>Sleet.Staff (brand X y) H
local notation "rX"=> (neighbors r x₁)

local notation "P₀"=> hub X y H b E x₁ r n
variable {C F:Side} {R': RG.Rep G F} {S':StepData C F}{δ:Type}{T': Tube G S'} {u:ℝ}
variable (I:Cash W x μ L J o u T' R') (Y:δ→ Portrait R' α) (b':Finset δ)(E':BoxOf I) (x₂: Site C)
local notation "Q₀"=> hub Y y I b' E' x₂ r n
local notation "Z₁"=>brand Y y
local notation "U'"=>Sleet.Staff (brand Y y) I
local notation "rY"=>neighbors r x₂

-- lean implicit
variable (K: Warp (S:=S) b b' (S':=S'))
variable {H X y b E r n I Y b' E' x₁ x₂ K}
variable (hp: Boot X y H b E x₁ r n I Y b' E' x₂ K)
-- query functions.Boot sym independent. Proof ensures arity boots and mark transport even on rotations.M.Home flag veneers.
namespace Boot
include hp
-- existence reverse pure structural registration. Allows empty types of Π
omit hp
lemma undone {α β:Type*}[DecidableEq α][DecidableEq β][Nonempty α] (p:α→β) (S:Finset α)(T:Finset β)(h:Set.InjOn p S)(hp:S.image p=T):∃y:β→α, Set.InjOn y T ∧ T.image y=S ∧ ∀ i∈S, y (p i)= i:=by
   have hT : Injective (fun i:↥S=>p i.val):=fun i j hE=> Subtype.ext (h i.2 j.2 hE)
   let f:=Function.extend (fun i:↥S=>p i.val) (fun i:↥S=>i.val) (fun _=>Classical.arbitrary α)
   have he i (hi:i∈S) : f (p i)=i:= hT.extend_apply _ _ ⟨i,hi⟩
   have hh j (hj:j∈T) : f j∈ S ∧ p (f j)=j:=by rw [← hp] at hj; obtain ⟨i,hi,rfl⟩:= mem_image.mp hj; rw [he i hi]; exact ⟨hi,rfl⟩
   refine ⟨f,fun i hi j hj h=> ((hh i hi).2.symm.trans ((congr_arg p h).trans (hh j hj).2)),Finset.Subset.antisymm ?_ ?_,he⟩
   · intro i hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact (hh j hj).1
   intro j hj; exact Finset.mem_image.mpr ⟨p j, hp ▸ Finset.mem_image_of_mem p hj,he j hj⟩

-- reversed boot. Caress H.Prop.Distinct
include hp
lemma bootRev : ∃ g:Warp b' b (S':=S) (S:=S'), Boot Y y I b' E' x₂ r n H X b E x₁ g ∧ g.grow=K.grow.symm∧ (∀ i∈P₀,g.f (K.f i)=i) ∧ ∀ j∈Q₀,K.f (g.f j)=j:=by
   haveI : Nonempty (Head S):=⟨Opacity.key _ 0⟩
   obtain ⟨t,ht,hA,hp'⟩:= undone K.f (P₀) (Q₀) hp.valid hp.ports
   obtain ⟨g,hg,hQ,hy⟩:= undone K.halo (rX) (rY) hp.route hp.home
   set Xv: Warp b' b (S':=S) (S:=S'):=⟨t,K.grow.symm,g⟩
   have he {i} (hi:i∈Q₀) : t i∈P₀ ∧ K.f (t i) = i:=by
       rw [← hp.ports] at hi; obtain ⟨i,h',rfl⟩:=mem_image.mp hi; rw [hp' _ h']; exact ⟨h',rfl⟩
   refine ⟨Xv,⟨ht,hp.marks',hp.marks,hg,hQ,?_,?_,?_,hp.wages',hp.wages,?_,?_⟩,rfl,hp',fun i hi=> (he hi).2⟩
   · change g x₂=x₁; rw [← hp.parent, hy _ ((neighbors_mem ..).2 (by rw [separation_self]; omega))]
   · intro i hi j hj; rw [← hp.home] at hi hj; obtain ⟨i,hi',rfl⟩:= mem_image.mp hi; obtain ⟨j,hj',rfl⟩:=mem_image.mp hj -- names
     change _=separation (g _) (g _); rw [hy _ hi',hy _ hj']; exact (hp.sep _ hi' _ hj').symm -- infer
   · rw [← hp.flit,Finset.image_image]; calc
       _= (nearby H E x₁ r n).image id:= image_congr fun i hi=> hp' _ (mem_union_left _ hi)
       _=_:= Finset.image_id
   · intro i hi; change H.supportP (t i)= _
     rw [← (he hi).2, show t (K.f (t i))=t i from hp' _ (he hi).1, hp.admit _ (he hi).1, Finset.image_image]; symm; calc
        _= (H.supportP (t i)).image id:= image_congr fun a ha=> hy a (hp.stock (he hi).1 ha)
        _=_:= image_id
   intro i; change sign X₁ S _=t _
   conv_rhs=> rw [← show _=i from K.grow.apply_symm_apply i]
   exact (show t _=_ from (congr_arg t (hp.lands (K.grow.symm i))).trans (hp' _ (mem_union_right _ (mem_image_of_mem _ (K.grow.symm i).prop)))).symm

lemma footprint (V:Molecule S)(he: V⊆P₀): I.unionP (V.image K.f)=(H.unionP V).image K.halo:=by
   ext i; constructor
   · intro hi; obtain ⟨s,hs,hv⟩:=mem_biUnion.mp hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hs; rw [hp.admit j (he hj)] at hv; obtain ⟨i,h',rfl⟩:=mem_image.mp hv; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj,h'⟩)
   intro he'; obtain ⟨i,hi,rfl⟩:=mem_image.mp he'; obtain ⟨j,hj,hv⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ hj, (hp.admit j (he hj)).symm ▸ mem_image_of_mem _ hv⟩

-- any h persistent

def sprout (v:H.ThinP)(hv:v.val⊆P₀) : I.ThinP:=by
    let a:= v.val.image K.f
    refine ⟨a,⟨(?_),?_⟩⟩
    · unfold a; rw [hp.footprint _ hv]; exact Nonempty.image v.2.1 _
    obtain ⟨r,hᵣ,h',hh,hG⟩:= hp.bootRev
    rw [(hᵣ.stockSkin a (show a⊆ Q₀ from hp.ports ▸ image_subset_image hv)).whiteG]

lemma sprouted (v:H.ThinP)(hv:v.val⊆P₀) : (hp.sprout v hv).val=v.val.image K.f:= rfl
lemma traverses (v:H.ThinP)(hv:v.val⊆P₀) : I.smallAt (hp.sprout v hv)=(H.smallAt v).image K.halo:=hp.footprint v.val hv

-- ticket carries
omit hp

def labels {s:Finset ι} (a: ↥s≃↥b') (v:Finset ι)(hv:v⊆s) : Finset δ := v.attach.image (fun i => (a ⟨i.val,hv i.2⟩).val)
lemma labelsIn {α β:Type}{s:Finset α}{u:Finset β}(a:↥s ≃↥u)(v: Finset α)(hv:v⊆s) (i:β): i∈labels a v hv ↔ ∃ (j:↥s), j.val∈v ∧ (a j).val=i :=by
    constructor
    · intro h; obtain ⟨k,hk,hv'⟩:=mem_image.mp h; exact ⟨⟨_,hv k.prop⟩,k.prop,hv'⟩
    rintro ⟨j,hj,hk⟩; exact mem_image.mpr ⟨⟨j.val,hj⟩,mem_attach .., hk⟩
include hp
variable (ut:Drums (Typeface.brand X y) S)(hx:ut.val⊆ b)
def forte : Drums Z₁ S':=by
    refine ⟨labels K.grow ut.val hx,?_⟩
    intro i hi j hj hk; obtain ⟨s,hs,rfl⟩:=(labelsIn _ _ _ _).1 hi; obtain ⟨t,ht,rfl⟩:= (labelsIn _ _ _ _).1 hj
    have hK i : sign X₁ S (i:↥b).val∈ P₀:= mem_union_right _ (mem_image_of_mem _ i.2)
    rw [hp.lands,hp.lands] at hk
    exact congr_arg (fun i:↥b=> (K.grow i).val) (Subtype.ext (ut.prop hs ht (hp.valid (hK _) (hK _) hk)))
lemma forteV : (hp.forte ut hx).val=labels K.grow ut.val hx :=rfl
lemma insideV : (hp.forte ut hx).val⊆ b':=by rw [forteV]; intro i hi; obtain ⟨k,-,rfl⟩:= (labelsIn ..).1 hi; exact (K.grow k).2
lemma spansP : (hp.forte ut hx).reach= ut.reach.image K.f:=by
   change ((hp.forte ut hx).val.image _) = (ut.val.image _).image _
   rw [forteV]; ext i; constructor
   · intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; obtain ⟨s,h,rfl⟩:= (labelsIn ..).1 hj; rw [hp.lands]; exact mem_image_of_mem _ (mem_image_of_mem _ h)
   intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; obtain ⟨i,hi',rfl⟩:=mem_image.mp hj; let z:↥b:=⟨i,hx hi'⟩
   exact mem_image.mpr ⟨_,(labelsIn K.grow _ _ _).2 ⟨z,hi',rfl⟩,hp.lands z⟩
end Boot
end BoxOf
end YM.RemainderComparison.Seedlings
