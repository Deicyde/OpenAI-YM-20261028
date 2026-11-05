import YM.RemainderComparison.Seedlings.Urgent
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

def nearby := (E.heads n).filter fun i=> H.supportP i ⊆ neighbors r x₁
def hub : Molecule S:= nearby H E x₁ r n ∪ b.image (sign (Typeface.brand X y) S)
local notation "P₀"=> hub X y H b E x₁ r n
lemma manifested (s:U) (hp:Marvel X y H b E (k:=n) (r:=r) x₁ s)(i): (s.1.2 i).val ⊆ P₀:=by
   intro j hj; rcases mem_union.mp (hp.fair.decked i hj) with h|h; swap; exact mem_union_right _ h
   apply Finset.mem_union_left; have hz: H.supportP j ⊆ H.smallAt (s.1.2 i):= Finset.subset_biUnion_of_mem _ hj; exact mem_filter.mpr ⟨h,(hz.trans (Finset.subset_biUnion_of_mem (H.smallAt ∘ s.1.2) (mem_univ i))).trans hp.roam⟩

-- generic structural loom built from owner Stock & stellar.Clock positions. NOT an RG output estimate hypothesis. Map even through rotations where anchors differ.
variable {C F:Side} {R': RG.Rep G F} {S':StepData C F}{δ:Type}{T': Tube G S'} {u:ℝ}
variable (I:Cash W x μ L J o u T' R') (Y:δ→ Portrait R' α) (b':Finset δ)(E':BoxOf I) (x₂: Site C)
local notation "Q₀"=> hub Y y I b' E' x₂ r n
local notation "Z₁"=>brand Y y
local notation "U'"=>Sleet.Staff (brand Y y) I
local notation "rY"=>neighbors r x₂

-- independent of H ledger
structure Warp where
    f : Head S → Head S'
    grow : ↥b≃↥b'
    halo : Site c → Site C

-- lean implicit
variable (K: Warp (S:=S) b b' (S':=S'))
structure Boot : Prop where
   valid : Set.InjOn K.f (↑(hub X y H b E x₁ r n) : Set (Head S))
   marks : ∀ i∈b', ∃ j,(Y i).wing=Wing.logKey j
   marks' : ∀ i∈b, ∃ j,(X i).wing=Wing.logKey j
   route : Set.InjOn K.halo (neighbors r x₁) -- to Template masks only
   home : (neighbors r x₁).image K.halo=neighbors r x₂
   parent : K.halo x₁=x₂
   sep : ∀ i∈neighbors r x₁,∀ j∈neighbors r x₁,separation i j=separation (K.halo i) (K.halo j)
   flit : (nearby H E x₁ r n).image K.f= nearby I E' x₂ r n
   wages : ∀ i: ↥b', I.supportP (Palette.sign (Typeface.brand Y y) S' i.val)⊆ neighbors r x₂
   wages' : ∀ i: ↥b, H.supportP (Palette.sign (Typeface.brand X y) S i.val) ⊆ neighbors r x₁
   admit : ∀ i∈hub X y H b E x₁ r n, I.supportP (K.f i)=(H.supportP i).image K.halo
   lands : ∀ i:↥b, Palette.sign (Typeface.brand Y y) S' (K.grow i).val= K.f (Palette.sign (Typeface.brand X y) S i.val)
variable {H X y b E r n I Y b' E' x₁ x₂ K}
variable (hp: Boot X y H b E x₁ r n I Y b' E' x₂ K)
-- query functions.Boot sym independent. Proof ensures arity boots and mark transport even on rotations.M.Home flag veneers.
namespace Boot
include hp
lemma signals : (b.image (sign (Typeface.brand X y) S)).image K.f=b'.image (sign (Typeface.brand Y y) S'):=by
   ext i; constructor
   · intro hi; obtain ⟨k,hz,rfl⟩:=mem_image.mp hi; obtain ⟨i',hh,rfl⟩:= mem_image.mp hz; exact (show K.f _∈_ from hp.lands ⟨i',hh⟩ ▸ Finset.mem_image_of_mem _ (K.grow ⟨i',hh⟩).prop)
   intro hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; let i:= K.grow.symm ⟨j,hj⟩
   refine mem_image.mpr ⟨Palette.sign X₁ S i.val,mem_image_of_mem _ i.prop, (hp.lands i).symm.trans ?_⟩; unfold i; rw [Equiv.apply_symm_apply]
lemma ports : (P₀).image K.f=Q₀:=by unfold hub; rw [Finset.image_union,hp.flit,hp.signals]
lemma stock {i}(he:i∈ P₀) : H.supportP i⊆neighbors r x₁:=by
   rcases mem_union.mp he with h|h; exact (Finset.mem_filter.mp h).2
   obtain ⟨j,h',rfl⟩:= mem_image.mp h; exact hp.wages' ⟨j,h'⟩
lemma stockSkin (i)(h:i⊆P₀) : Youth.Seedless (i:Molecule S):=by
   intro t ht; rcases mem_union.mp (h ht) with z|z; exact E.finishes H n t (Finset.mem_filter.mp z).1 -- arity
   obtain ⟨j,h,rfl⟩:=mem_image.mp z; obtain ⟨k,hk⟩:=hp.marks' j h; exact Or.inr ⟨k,congr_arg (fun f:Wing=>f.badge S) hk⟩
end Boot
end BoxOf
end YM.RemainderComparison.Seedlings
