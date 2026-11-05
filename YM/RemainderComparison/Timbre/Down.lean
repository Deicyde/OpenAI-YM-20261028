import YM.RemainderComparison.Seedlings.Mesh
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Timbre
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
open Meadow Turn BoxOf
local notation "B"=> Pressure.radiusB x
-- all active Music at structural stems. No density field oracle
local notation "Eʼ"=> Mint.verse R.path

-- don't rely defina.J

def trumpets : BoxOf H where
   heads k:= ((Meadow.tuck k).filter fun j=>Mint.verse R.path j≤ Pressure.radiusB x).map (Mint.disc S)
   ascends i j h k hp:=by
      obtain ⟨r,hk,rfl⟩:= Finset.mem_map.mp hp; exact mem_map_of_mem _ (mem_filter.mpr ⟨(Meadow.pocket ..).2 (((Meadow.pocket ..).1 (mem_filter.mp hk).1).trans h), (mem_filter.mp hk).2⟩)
   spans k i h:= by obtain ⟨r,hr,rfl⟩:=mem_map.mp h; exact Or.inl ⟨r,rfl,(mem_filter.mp hr).2⟩
lemma rooted (s:Set ℕ): Grant H (trumpets H) Set.univ s:= ⟨fun i h=>⟨Meadow.held i, mem_map_of_mem _ (mem_filter.mpr ⟨(Meadow.pocket ..).2 le_rfl,h⟩)⟩,fun i hi=>False.elim (hi (Set.mem_univ i))⟩

lemma chants (k:ℕ)(i: Music c f): Mint.disc S i ∈ (trumpets H).heads k ↔ Meadow.held i ≤ k ∧ Mint.verse R.path i≤ Pressure.radiusB x:=by unfold trumpets; simp [Meadow.pocket]
lemma knock (k:ℕ) (i : Head S)(h:i∈(trumpets H).heads k): ∃ j:Music c f,i = Mint.disc S j:=by obtain ⟨j,h,rfl⟩:= mem_map.mp h; exact ⟨j,rfl⟩
variable (sd:Signed)(i : Site c) (w:R.activities.Moves sd (S.ratio.embed i))
def rotate : Equiv.Perm (Music c f):= Equiv.sumCongr (Turn.sky sd (S.ratio.embed i)) (Equiv.sumCongr (Turn.sky sd (S.ratio.embed i)) (Equiv.sumCongr (Turn.sky sd (S.ratio.embed i)) (rotateMini sd i S)))
lemma belt (j:Music c f) : Turn.badge R w ((Mint.disc S) j)= Mint.disc S (rotate (S:=S) sd i j)∧Meadow.held (rotate (S:=S) sd i j)=Meadow.held j∧ Mint.verse R.path (rotate (S:=S) sd i j)=Mint.verse R.path j:=by rcases j with j|j|j|j <;> exact ⟨rfl,rfl,rfl⟩
-- genuine rotations budget.Ne ν orientation
lemma shines (r k:ℕ)(z:Site c) : (BoxOf.nearby H (trumpets H) z r k).image (Turn.badge R w)= BoxOf.nearby H (trumpets H) (Lattice.affine sd i z) r k :=by
   suffices h : ∀ j,j∈ BoxOf.nearby H (trumpets H) z r k ↔ Turn.badge R w j∈ BoxOf.nearby H (trumpets H) (Lattice.affine sd i z) r k from Turn.display _ _ _ |>.2 h |>.symm -- adjust arg result.
   intro j
   have hz j : H.supportP (Turn.badge R w j)= (H.supportP j).image (Lattice.affine sd i):= Turn.insignia T R w J.halo B j -- J/μ names inspect
   have hp j : j∈ (trumpets H).heads k ↔ Turn.badge R w j∈ (trumpets H).heads k:=by
      constructor
      · intro h; obtain ⟨p,rfl⟩:= knock _ _ j h; obtain ⟨ha,hx,h'⟩:= belt _ _ w p; rw [ha,Timbre.chants,hx,h']; exact (chants _ k p).1 h
      intro h; obtain ⟨q,hq⟩:= knock H k _ h; obtain ⟨p,rfl⟩:= (Timbre.rotate (S:=S) sd i).surjective q; obtain ⟨ha,hx,h'⟩:= belt _ _ w p; have he : j= _ := (Turn.badge R w).injective (hq.trans ha.symm); rw [he,Timbre.chants,← hx,← h']; rw [hq] at h; exact (Timbre.chants ..).1 h
   refine and_congr (hp _) ?_ |> (fun h=> (mem_filter.trans h).trans mem_filter.symm)
   rw [hz,Turn.circle_wind]
   exact (Finset.image_subset_image_iff (StepData.sendSites sd i).injective).symm
end YM.RemainderComparison.Timbre
