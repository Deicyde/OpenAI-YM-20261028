import YM.RemainderComparison.Seedlings.Binge
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
variable (s:Sleet.Staff (Typeface.brand X y) H)(hs: BoxOf.Marvel X y H b E (k:=n) (r:=r) x₁ s)
local notation "Va"=> words X y H b E r n x₁
local notation "Vb"=> words Y y I b' E' r n x₂
set_option quotPrecheck false
local notation "OF"=> Option (Fin s.1.1)
include hs
def flora : U' := ⟨⟨s.1.1, fun i:Option (Fin s.1.1)=> hp.sprout _ (BoxOf.manifested _ _ _ _ _ _ _ _ s hs i)⟩, fun i: Option (Fin s.1.1)=> hp.forte _ (hs.fair.located i)⟩
-- definable for all P proof-irrelevant; cofinal preservation of vacancy
local notation "S₀"=> Sleet.Base (brand X y) H
local notation "F₁"=> Sleet.Base (brand Y y) I
local notation "Kt"=> hp.flora s hs
lemma drum_shape (i:OF) : (hp.forte (s.2 i) (hs.fair.located i)).reach ⊆ ((Kt).fst.snd i).val:=by
   rw [hp.spansP]; change _ ⊆ ((s.1.2 i).val).image K.f; exact Finset.image_subset_image (hs.fair.valid i)
lemma wearied (i:OF) : (((Kt).fst.snd i).val) \ ((Kt).snd i).reach= (((s.1.2 i).val) \ (s.2 i).reach).image K.f:=by
   let V:=s.1.2 i; change V.val.image K.f \ (hp.forte (s.2 i) (hs.fair.located i)).reach=_
   rw [hp.spansP]; let Z:= (s.2 i).reach; have ht j (hj:j∈V.val):j∈P₀:= BoxOf.manifested _ _ _ _ _ _ _ _ _ hs i hj -- implicit
   have he : Set.InjOn K.f V.val:=hp.valid.mono fun i=>ht _
   ext j; constructor
   · intro h; obtain ⟨h,h'⟩:= Finset.mem_sdiff.mp h; obtain ⟨k,hk,rfl⟩:= mem_image.mp h; exact mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨hk,fun h=>h' (mem_image_of_mem _ h)⟩)
   intro h; obtain ⟨k,hk,rfl⟩:=mem_image.mp h; obtain ⟨hv,hL⟩:= mem_sdiff.mp hk
   refine Finset.mem_sdiff.mpr ⟨mem_image_of_mem _ hv,fun h=>?_⟩; obtain ⟨j,hj,hq⟩:=mem_image.mp h
   exact hL ((show j=k from he (hs.fair.valid i hj) hv hq) ▸ hj)
lemma reaches' : F₁ (Kt)=(S₀ s).image K.halo:=by
   have he i: I.smallAt ((Kt).1.2 i)=(H.smallAt (s.1.2 i)).image K.halo:=hp.traverses _ (BoxOf.manifested _ _ _ _ _ _ _ _ _ hs i)
   unfold Sleet.Base Captain.reachability; unfold unionOf; ext i; constructor
   · intro h; obtain ⟨j,hj,hp⟩:= mem_biUnion.mp h; dsimp only [Function.comp_apply] at hp; -- name shadow hp!
     rw [he j] at hp; obtain ⟨x,hy,rfl⟩:= mem_image.mp hp; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj,hy⟩)
   intro h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; obtain ⟨j,hj,hF⟩:= mem_biUnion.mp hx; refine mem_biUnion.mpr ⟨_, (mem_univ j),?_⟩; dsimp only [Function.comp_apply]; rw [he]; exact mem_image_of_mem _ hF
lemma marks_reach (i:OF) (j:δ): j∈ ((Kt).snd i).val ↔ ∃ x:↥b, x.val∈ (s.2 i).val ∧ (K.grow x).val=j := labelsIn K.grow _ (hs.fair.located i) _
lemma marvelous : Marvel Y y I b' E' (k:=n) (r:=r) x₂ Kt:=by
    refine ⟨⟨hs.fair.length,?_,?_,hp.drum_shape s hs,?_⟩,?_⟩
    · ext i; constructor
      · intro h; obtain ⟨x,hx,hv⟩:= mem_biUnion.mp h; obtain ⟨t,-,h⟩:= (hp.marks_reach s hs _ i).1 hv; rw [← h]; exact (K.grow t).prop
      intro h; let t:=K.grow.symm ⟨i,h⟩; have ht: t.val∈ Lyric.page X₁ H s.1 s.2:= by rw [hs.fair.atlas]; exact t.prop
      obtain ⟨x,hx,hv⟩:=mem_biUnion.mp ht; exact mem_biUnion.mpr ⟨x,mem_univ _,(hp.marks_reach s hs x i).2 ⟨t,hv,congr_arg Subtype.val (K.grow.apply_symm_apply _)⟩⟩
    · intro i hi j hj he; refine Finset.disjoint_left.mpr fun x hx hP=>?_; obtain ⟨t,ht,hr⟩:=(hp.marks_reach s hs _ x).1 hx; obtain ⟨b,hb,hB⟩:= (hp.marks_reach s hs _ x).1 hP
      rw [show b=t from K.grow.injective (Subtype.ext (hB.trans hr.symm))] at hb
      exact Finset.disjoint_left.mp (hs.fair.leaves (show _ from mem_univ i) (show _ from mem_univ j) he) ht hb
    · intro i; rw [hp.wearied]; intro j hj; obtain ⟨k,hk,rfl⟩:= mem_image.mp hj; have he : k∈ nearby H E x₁ r n:= mem_filter.mpr ⟨hs.fair.paid i hk, hp.stock (BoxOf.manifested _ _ _ _ _ _ _ _ s hs i ((mem_sdiff.mp hk).1))⟩; exact (Finset.mem_filter.mp (hp.flit ▸ mem_image_of_mem K.f he)).1
    rw [hp.reaches']; exact hp.home ▸ image_subset_image hs.roam

-- flora reverse. no conditions on g halos
variable (K': Warp (S:=S') b' b (S':=S)) (ht : Boot Y y I b' E' x₂ r n H X b E x₁ K') (hx:K'.grow=K.grow.symm)(hK:∀ i∈hub X y H b E x₁ r n,K'.f (K.f i)= i)
include ht hx hK
lemma shakeback : ht.flora (Kt) (hp.marvelous s hs)=s:=by
   let q:= ht.flora _ (hp.marvelous s hs)
   have hP: q.1.2=s.1.2:=by
      funext i; apply Subtype.ext
      change (((s.fst.snd i).val).image K.f).image K'.f=_; rw [image_image]
      apply Eq.trans (image_congr (show Set.EqOn _ id _ from ?_)) Finset.image_id
      intro x h; exact hK x (BoxOf.manifested _ _ _ _ _ _ _ _ _ hs i h)
   have he: q.2=s.2:=by
      funext i; have hm j: j∈ (q.2 i).val ↔ ∃ (w:↥b'),w.val∈ ((Kt).snd i).val ∧ (K'.grow w).val=j:= ht.marks_reach .. -- explicit
      apply Subtype.ext; ext j; constructor
      · intro h; obtain ⟨w,hw,rfl⟩:= (hm j).1 h; obtain ⟨x,hx',he⟩:= (hp.marks_reach s hs _ w.val).1 hw; rw [hx, ← show K.grow x=w from Subtype.ext he]; exact Equiv.symm_apply_apply K.grow x|>.symm ▸ hx'
      intro h; let x:↥b:=⟨j,hs.fair.located i h⟩
      refine (hm j).2 ⟨K.grow x,(hp.marks_reach s hs i _).2 ⟨x,h,rfl⟩,?_⟩
      rw [hx,K.grow.symm_apply_apply]
   exact Sigma.ext (Sigma.ext rfl (heq_of_eq hP)) (heq_of_eq he)
omit hs ht hx hK K'
def tell : (Va) → Vb := fun x=> let hp':= (shine X y H b E x₁).1 x.2; ⟨hp.flora x.val hp',(shine ..).2 (hp.marvelous _ hp')⟩
lemma bij_tell : Bijective hp.tell:=by
   obtain ⟨z,hz,h,hf,hx⟩:= hp.bootRev
   constructor
   · intro a b ht'; have hh i: hz.tell (hp.tell i)=i:= Subtype.ext (hp.shakeback i.val (show Marvel X y H _ E (k:=n) (r:=r) x₁ i.val from (shine ..).1 i.2) z hz h hf)
     exact (hh a).symm.trans ((congr_arg hz.tell ht').trans (hh b))
   intro i; refine ⟨hz.tell i,Subtype.ext ?_⟩
   apply hz.shakeback i.val (show Marvel .. from (BoxOf.shine ..).1 i.prop) K hp (by rw [h,Equiv.symm_symm]) hx -- syntax maybe
end Boot
end BoxOf
end YM.RemainderComparison.Seedlings
