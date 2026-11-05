import YM.RemainderComparison.Harmonics.Needle
import YM.RemainderComparison.Creek.Observatory

/-!
# Aura book assembly: stock to eligible P plates

Masks paint AFTER summing exact addresses at real and star trajectory values.
Physical ties on inputs mortgages pure, all P preserved. Uses Φ-relative only
on uncut cores. Does not assert existence of an input stencil w/o Alma.
-/

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
variable (b:Finset ι) -- aimed marks. vac b=∅, BOTH films use turns of chosen pages, some may share WKey
local notation "Y"=>brand X y
local notation "MΓ"=> Sleet.Staff (brand X y) H
local notation "B"=> radiusB x
lemma stirred (j:ℕ)(p:MΓ)(k:Option (Fin p.1.fst))(hk:Opacity.key S j∈(p.1.snd k).val\(p.2 k).reach) (V:Config G c) (χ:Chi) (he: Lyric.string (Typeface.brand X y) H χ p.1 p.2 V≠0) : R.activities.regularOccurrence R.p j ≠0:=by
    intro ht; apply he
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_univ k) ?_)
    unfold toe Cascade.escort likely; rw [sum_eq_zero ?_,mul_zero]; intro r (_:r∈univ)
    unfold Team.picture; refine integral_eq_zero_of_ae ?_; filter_upwards with u
    unfold Team.grove; split
    next=>
      unfold likely; rw [sum_eq_zero ?_,mul_zero]; · rfl
      intro s hs; unfold Team.cinema; refine integral_eq_zero_of_ae ?_; filter_upwards with u; refine integral_eq_zero_of_ae ?_; filter_upwards with v
      unfold Team.floret; rw [Palette.label]; apply mul_eq_zero_of_right; split
      next hh=>
         apply mul_eq_zero_of_right
         refine Finset.prod_eq_zero hk ?_
         unfold Polar.ember Opacity.key; dsimp only [Sum.elim, Polar.logMoment,Polar.frost,Polar.nest]; rw [ht]; simp
      next=> rfl
    next=>rfl
-- coverage: stock monotone proof called via compiler.Probe levels cost-free not growth.Persistent. Pure ACTIVE enough
structure BoxOf (H: Cash W x μ L J o a T R) where
   heads : ℕ → Finset (Head S)
   ascends : Monotone heads
   spans n i : i∈heads n → (∃ j:Music c f, i=Mint.disc S j∧ Mint.verse R.path j ≤ radiusB x) ∨ ∃ j:ℕ,i=Opacity.key S j 

namespace BoxOf
variable (E:BoxOf H) {F': Finset ι}
local notation "SΓ"=> (Palette.sign (Typeface.brand X y) S)
local notation "RA"=> R.activities
include E
lemma finishes (m:ℕ) : Harmonics.Youth.Seedless (E.heads m):=fun _ hi=> (E.spans _ _ hi).imp (fun ⟨i,h,_⟩=>⟨i,h⟩) id
-- funding cross.A.No E primitives hypoth implicit if Hardware. Inputs owner.REAL κ poses
structure Grant (F F':Set ℕ) : Prop where
   sees i : Mint.verse R.path i≤radiusB x → ∃ n,(Mint.disc S) i∈E.heads n
   buds i : i∉F → i∉F' → (RA).regularOccurrence R.p i≠0 →∃ m, Opacity.key S i∈E.heads m

section roster
-- no active proof for apertured fossils until usage
structure Eligible (X:ι→Portrait R α)(y:α)(b:Finset ι)(n:ℕ) (p:Sleet.Staff (Typeface.brand X y) H) : Prop where
   length : p.1.1 ≤ n
   atlas : p.2 |> fun s=> Lyric.page (Typeface.brand X y) H p.1 s=b
   leaves : Lyric.Turns (Typeface.brand X y) H p.1 p.2
   valid i : (p.2 i).reach ⊆ (p.1.2 i).val
   paid i : ((p.1.2 i).val \ (p.2 i).reach) ⊆ E.heads n
variable {X y b H E}
lemma Eligible.suffices {n k p} (h: E.Eligible H X y b n p)(hq:n≤ k): E.Eligible H X y b k p:=⟨h.length.trans hq,h.atlas,h.leaves,h.valid,fun i=> (h.paid i).trans (E.ascends hq)⟩
lemma Eligible.located {p k} (h:E.Eligible H X y b k p) (i): (p.2 i).val⊆ b:=h.atlas ▸ (show (p.2 i).val ⊆ Lyric.page _ _ p.1 p.2 from Finset.subset_biUnion_of_mem (fun i=>(p.2 i).val) (mem_univ i))
lemma Eligible.decked {p k} (h:E.Eligible H X y b k p) (i):((p.1.2 i).val)⊆ E.heads k ∪ b.image (Palette.sign (Typeface.brand X y) S):=by
   intro j hj; by_cases he:j∈(p.2 i).reach; exact Finset.mem_union_right _ (Finset.image_subset_image (h.located i) he); exact Finset.mem_union_left _ (h.paid i (Finset.mem_sdiff.mpr ⟨hj,he⟩))
lemma signedPresent {p k} (h:E.Eligible H X y b k p) (i:ι)(hi:i∈b): (H.supportP (SΓ i)) ⊆ Sleet.Base (Typeface.brand X y) H p:=by
   rw [← h.atlas] at hi
   obtain ⟨j,hj,h₁⟩:= Finset.mem_biUnion.mp hi
   exact (Finset.subset_biUnion_of_mem H.supportP (h.valid j ((p.2 j).reaches_of h₁))).trans (Finset.subset_biUnion_of_mem (H.smallAt ∘ p.1.2) hj)
variable (H E X y b)
lemma candles (n:ℕ): {p| E.Eligible H X y b n p}.Finite:=by
    let I:= E.heads n ∪ b.image SΓ
    let V:Set H.ThinP:= {p|p.val⊆ I}; have hv: V.Finite := ((Finset.finite_toSet I.powerset).preimage (Subtype.val_injective.injOn (f:=(Subtype.val: H.ThinP→Molecule S)))).subset (fun i hi=> Finset.mem_powerset.mpr hi)
    let t:= Script.restrict b; let p k := Sigma.mk (β:=fun n=> Option (Fin n)→H.ThinP) k ∘ (fun j:Option (Fin k)→ ↥V => Subtype.val ∘ j)
    haveI : Fintype V:= hv.fintype
    let w (j:H.fragrances): Set MΓ:= Set.range fun i:Syllable (Y ∘ t) H j=> (⟨j,Script.label Y H t j i⟩:MΓ)
    apply Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic n) (fun i _=>Set.Finite.biUnion (Set.finite_range (p i)) (fun j _=> (show (w j).Finite from Set.finite_range _))))
    rintro ⟨⟨i,f⟩,s⟩ (h:E.Eligible H X y b _ _)
    have he j: s j∈ Set.range ((Script.drums Y t S):Drums (Y ∘ t) S ↪ Drums Y S):= (Script.pens _ _ _).2 (h.located j)
    choose g hg using he
    exact Set.mem_iUnion₂.mpr ⟨i,h.length,Set.mem_iUnion₂.mpr ⟨⟨i,f⟩,⟨fun j=>⟨f j,h.decked j⟩,rfl⟩,⟨g,Sigma.ext rfl (heq_of_eq (funext hg))⟩⟩⟩
end roster
end BoxOf
end YM.RemainderComparison.Seedlings
