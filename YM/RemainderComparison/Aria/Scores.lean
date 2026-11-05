import YM.RemainderComparison.Timbre.Spect
/-!
# Synchronization from primitive presentations

 Illustration for use by RG03. Registration hypothesis only about inputs.Reh.Ph.Mask.
 Keep the cost of any operation enlarging the supports beyond purchased heights;
 counts here are budget assumptions checked at actual widths.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aria
open Seedlings
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
open BoxOf Timbre
local notation "B"=> Pressure.radiusB x
variable {I:Type}(N k n r d:ℕ)
-- includes dormant slots. Credit enumerates SHORT entries from Extra E only.
-- hint all with footprint diameter small.Actual.Mask. Doesn't take value estimates.
structure Score (H:Cash W x μ L J o a T R)(I:Type) (k:ℕ) where
    book : ℕ→ Finset I
    charges : Monotone book
    index : Site c × I ↪ ℕ
    advice (s:Site c) i n : i∈book n→ s∈H.supportP (Opacity.key S (index (s,i))) ∧ H.supportP (Opacity.key S (index (s,i)))⊆neighbors k s
namespace Score
variable (X':Score H I k)
set_option quotPrecheck false
local notation "Lx"=> X'.index

def scoreCalling : (Site c×I)↪Head S:= X'.index.trans ⟨Opacity.key S,fun _ _ h=> Wing.logKey.inj (Team.badged _ h)⟩
local notation "θ"=> X'.scoreCalling H _ -- param order inspect

def wake := ((Finset.univ:Finset (Site c))×ˢ (X'.book n)).map (scoreCalling H k X')
local notation "Sc"=> Score.wake H k n X'

-- use at all launches

def pose : BoxOf H:=by
    refine ⟨fun n=>(trumpets H).heads n ∪ Score.wake H k n X', fun i j h=>Finset.union_subset_union ((trumpets H).ascends h) ?_, fun i j hj=>?_⟩
    · apply Finset.map_subset_map.mpr; exact Finset.product_subset_product (Subset.refl _) (X'.charges h)
    rcases mem_union.mp hj with h|h; exact (trumpets H).spans _ _ h
    obtain ⟨v,hv,rfl⟩:= Finset.mem_map.mp h; exact Or.inr ⟨_,rfl⟩
local notation "Xs"=> Score.pose H k X'

lemma stars (U V:Set ℕ) (h: ∀ i∉ U,i∉ V→ R.activities.regularOccurrence R.p i≠0 →∃ (x: Site c)(j:I)(n:ℕ),j∈ X'.book n∧X'.index (x,j)=i) : BoxOf.Grant H Xs U V:=by
    constructor
    · intro j h; obtain ⟨v,hp⟩:= (rooted H V).sees j h; exact ⟨v,mem_union_left _ hp⟩
    intro i hi hv ht; obtain ⟨v,j,n,hx,rfl⟩:=h _ hi hv ht
    exact ⟨n,mem_union_right _ (mem_map_of_mem (scoreCalling H k X') (Finset.mem_product.mpr ⟨mem_univ v,hx⟩))⟩ -- defeq issue
variable (s:Signed)(y':Site c)(w:R.activities.Moves s (S.ratio.embed y')) (z:Site c)
local notation "p₀"=> BoxOf.nearby H Xs
-- finer orientation. e anchors preserved. need Move symmetry preserving heads. cost layout.BoxOf doesn't assume LOOP.Label correspondence across valid R.Policy books. Use with ACTIVE custom Index.Tech.Auth guards.
structure Regional : Prop where
    entry : ∀ t:Signed,∀ v:Site c,∃ (p:R.activities.Moves t (S.ratio.embed v)),∀ n,((Score.wake H k n X').image (Turn.badge R p)=(Score.wake H k n X'))
lemma fort (hf:(Score.wake H k n X').image (Turn.badge R w)=(Score.wake H k n X')) : (p₀ z r n).image (Turn.badge R w)= p₀ (Lattice.affine s y' z) r n:=by
    let F:= Turn.badge R w
    have hp : ((Score.wake H k n X').filter (fun a=>H.supportP a⊆neighbors r z)).image (Turn.badge R w)= ((Score.wake H k n X').filter (fun a=> H.supportP a⊆neighbors r (Lattice.affine s y' z))):=by
       suffices h: ∀ x, x∈ _ ↔ F x∈ ((Score.wake H k n X').filter (fun a=> H.supportP a⊆neighbors r (Lattice.affine s y' z))) from Turn.display _ _ _|>.2 h |>.symm
       intro i; simp only [Finset.mem_filter]; refine and_congr ?_ ?_
       · conv_rhs => rw [← hf]
         constructor; intro hi; exact mem_image_of_mem _ hi; intro h; obtain ⟨x,h,h'⟩:=mem_image.mp h; exact F.injective h' ▸ h
       have hv : H.supportP (F i)= (H.supportP i).image (Lattice.affine s y'):= Turn.insignia T R w (J.halo) B i
       rw [hv,Turn.circle_wind]; exact (Finset.image_subset_image_iff (StepData.sendSites s y').injective).symm
    unfold BoxOf.nearby Score.pose; simp only [Finset.filter_union,Finset.image_union]; rw [hp]; exact congr_arg (· ∪ _ ) (Timbre.shines H s y' w r n z) -- check syntax
end Score
end YM.RemainderComparison.Aria
