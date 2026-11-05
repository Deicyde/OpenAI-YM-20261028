import YM.RemainderComparison.Seedlings.Paint
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
-- normalize with every marker 
variable (l:ι→ℝ)(l':δ→ℝ)(τ:ℝ)(s:Sleet.Staff (Typeface.brand X y) H) (hs: BoxOf.Marvel X y H b E (k:=n) (r:=r) x₁ s)
set_option quotPrecheck false
local notation "OF"=> Option (Fin s.1.1)
local notation "S₁"=> hp.flora s hs
local notation "S₀"=> Sleet.Base (brand X y) H
local notation "F₁"=> Sleet.Base (brand Y y) I
lemma consonant (hv:(∏ i∈b,l i)=τ*∏ i∈b',l' i): invests X₁ H s.1 s.2 l= τ*invests Z₁ I (S₁).1 (S₁).2 l':=by
   have he:= (hp.marvelous s hs).fair
   rw [Lyric.opus X₁ H _ _ hs.fair.leaves,hs.fair.atlas,Lyric.opus Z₁ I _ _ he.leaves,he.atlas]; exact hv
lemma aqua : BoxOf.regional (S₀ s) r↔ regional (F₁ (S₁)) r:=by
   rw [hp.reaches']; constructor
   · intro h i hi j hj; obtain ⟨a,ha,rfl⟩:= mem_image.mp hi; obtain ⟨p,hp',rfl⟩:=mem_image.mp hj; apply (neighbors_mem ..).2; rw [← hp.sep _ (hs.roam ha) _ (hs.roam hp')]; exact (neighbors_mem ..).1 (h _ ha hp')
   intro h i hi j hj; apply (neighbors_mem ..).2; rw [hp.sep _ (hs.roam hi) _ (hs.roam hj)]; exact (neighbors_mem ..).1 (h _ (mem_image_of_mem _ hi) (mem_image_of_mem _ hj))
lemma root : x₁∈ S₀ s ↔ x₂∈ F₁ (S₁):=by
   rw [hp.reaches']; constructor
   · intro h; rw [← hp.parent]; exact mem_image_of_mem _ h
   intro h; obtain ⟨t,hT,h⟩:= mem_image.mp h; exact hp.route (hs.roam hT) (show x₁∈ rX from (neighbors_mem ..).2 (by rw [separation_self]; omega)) (h.trans hp.parent.symm) ▸ hT
lemma cardReach : (F₁ (S₁)).card=(S₀ s).card:=by rw [hp.reaches']; exact card_image_of_injOn (hp.route.mono hs.roam)
lemma within (he:Aura X y H b E (k:=n) (r:=r) s): Aura Y y I b' E' (k:=n) (r:=r) (S₁):=⟨(hp.marvelous s hs).fair,(hp.aqua s hs).1 he.transit⟩
end Boot
section trajectory
variable (z:Site c)(χ:Chi)(l:ι→ℝ)(Δ: Set ι)(b₁:ℝ)
def fieldWork (E:BoxOf H)(b:Finset ι)(r n:ℕ) : Finset (Sleet.Staff (Typeface.brand X y) H):= (glints X y H b E r n).filter fun i=> z∈ Sleet.Base (brand X y) H i
def adopt (E:BoxOf H)(b:Finset ι)(r n:ℕ) (s:fieldWork (X:=X) (y:=y) (H:=H) z E b r n): words X y H b E r n z:=by
   have hx:=Finset.mem_filter.mp s.2; have ht := (blink X y H b E).1 hx.1; exact ⟨s.val,(shine X y H b E z).2 ⟨ht.beginF,ht.transit _ hx.2⟩⟩
lemma adopting {K b r n}(s:fieldWork (X:=X) (y:=y) (H:=H) z K b r n) : (adopt z K b r n s).val=s.val:=rfl
end trajectory
-- hp implicit? 
namespace Boot
include hp
lemma stroll (s:fieldWork (X:=X) (y:=y) (H:=H) x₁ E b r n):(hp.tell (adopt x₁ E b r n s)).val ∈ fieldWork (X:=Y) (y:=y) (H:=I) x₂ E' b' r n:=by
    obtain ⟨hx,hE⟩:=Finset.mem_filter.mp s.2
    let p:=adopt x₁ E b r n s; have hs: s.val ∈ words X y H b E r n x₁ := p.2
    let h:=(shine X y H b E x₁).1 hs
    change hp.flora s.val h ∈ _; refine mem_filter.mpr ⟨(blink ..).2 (hp.within _ h ((blink ..).1 hx)),(hp.root _ h).mp hE⟩
local notation "Va"=> fieldWork (X:=X) (y:=y) (H:=H) x₁ E b r n
local notation "Vb"=> fieldWork (X:=Y) (y:=y) (H:=I) x₂ E' b' r n
def forestal (s:Va): Vb:= ⟨_,hp.stroll s⟩
lemma bij_fore : Bijective hp.forestal:= by
    constructor
    · intro i j h; change (hp.forestal i)=_ at h; have hh := hp.bij_tell.1 (show hp.tell (adopt x₁ E b r n i)= hp.tell (adopt x₁ E b r n j) from Subtype.ext (show (hp.forestal i).val = (hp.forestal j).val from congr_arg Subtype.val h)); exact Subtype.ext (show (adopt x₁ E b r n i).val=(adopt x₁ E b r n j).val from congr_arg Subtype.val hh)
    intro i; let p : (words Y y I b' E' r n x₂):= adopt x₂ E' b' r n i; obtain ⟨s,h⟩:= hp.bij_tell.2 p; change hp.tell s=p at h
    have hx:= (shine X y H b E x₁).1 s.prop; have ht:=mem_filter.mp i.2; have he : hp.flora s.val hx=i.val:= congr_arg Subtype.val h
    have hh := (hp.aqua s.val hx).2 (he.symm ▸ ((blink Y y I _ _).1 ht.1).transit); have hf: s.val∈ Va:= mem_filter.mpr ⟨(blink ..).2 ⟨hx.fair,hh⟩,(hp.root s.val hx).mpr (he.symm ▸ ht.2)⟩
    exact ⟨⟨s.val,hf⟩,Subtype.ext he⟩
end Boot
end BoxOf
end YM.RemainderComparison.Seedlings
