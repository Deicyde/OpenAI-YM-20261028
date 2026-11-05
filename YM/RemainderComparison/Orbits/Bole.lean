import YM.RemainderComparison.Orbits.Trunk
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Orbits
open Funk
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι δ : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Aux Mosaic Verse Muse Apo Marker Push.Uniform Lapis Sienna Fare Boulevard Herbal WickReps Lyric Typeface
open Trio Next.Rank.Glyph Next.Rank.Exponential
variable (Q:ConnectedActivityE6.Target G P) (Ω:KernelChoices)
open Lobby Portal
open Pier Slide
variable {β:ℝ}{χ:Chi}{ιa ιb δa δb:Type}(P': BudgetPoint)
open WickReps Manor Flues Serif
open Seedlings BoxOf
variable (H:Cash W x μ L Q o C T R)(M:ι→Portrait R α)(y:α)(l:ι→ℝ)(Z:Set ι)(v:ℝ) (D:BoxOf H)
variable {r' k:ℕ}(o':ι→Site c)(Wc:Breeze.Careers ι δ c o' r' k)(wP:ι→ℝ)
local notation "Mʼ"=> Creek.theater H χ M y l Z v
local notation "Aʼ"=> Creek.Academy H χ M y l Z v k
local notation "Fʼ"=> Sleet.Staff (Typeface.brand M y) H
local notation "Sx"=> Wc.pocket
local notation "St"=> Wc.o'
open Creek
variable {fA:Side}
variable {Y:Stars→Side}(C':∀ i:Stars, Pier (Y i) G W x μ L Q o C β χ α)(S':δ→Pier fA G W x μ L Q o C β χ α)
variable (Sg:∀ i:Stars, BoxOf (C' i).reader) (Sm:∀ i:δ,BoxOf (S' i).reader)
-- Aura subs lift; build with classical non slow.Tape.Defeq
section Tube0
variable (T: Manor G c ι α ιa)(X:Set ιa)(V:Finset ιa)
def prefer : Finset X := (show {i:X|i.val∈ V}.Finite from (V.finite_toSet.preimage (show Set.InjOn Subtype.val _ from Subtype.val_injective.injOn))).toFinset
lemma prefers {i:X} : i∈ prefer X V ↔ i.val∈ V:= by rw [prefer,Set.Finite.mem_toFinset]; rfl
variable (h:(V:Set ιa)⊆ X) (r q:ℕ)(B:Manor.Basis T V r)
def branch : Basis (peel T X) (prefer X V) r:= ⟨fun x i=> B.support x i.val,fun x i=> B.sto x i.val,fun i h=> B.account i.val ((prefers ..).1 h),fun x i h=> B.location x i.val ((prefers ..).1 h)⟩
include h
lemma pillars (f:ιa→ℝ) : ∑ i∈ prefer X V, f i.val=∑ i∈V,f i:= by
    rw [show (∑ i∈ prefer X V, f i.val) =∑ i∈ (prefer X V).image Subtype.val,f i from (sum_image (g:=Subtype.val) fun i _ j _ h=> Subtype.val_injective h).symm]; congr 1; ext i; constructor
    · intro he; obtain ⟨j,h,rfl⟩:= Finset.mem_image.mp he; exact (prefers ..).1 h
    intro hi; exact Finset.mem_image.mpr ⟨⟨i,h hi⟩,(prefers ..).2 hi,rfl⟩
lemma choirA (u:α) : (peel T X).sector u (prefer X V) (branch T X V r B)= T.sector u V B:= by funext j U; exact pillars X V h (fun i=> B.support j i*T.solvent u i U)
lemma choirB (u:α) : Apo.slab (peel T X) (prefer X V) u= Apo.slab T V u:= by funext U; exact pillars X V h fun i=>T.solvent u i U
end Tube0
variable (SxN:ℕ)(Sp:δ→ℕ)
set_option quotPrecheck false
local notation "Pʼ"=> BoxOf.glints M y H (∅:Finset ι) D r' SxN
local notation "Qʼ"=> fun i=> BoxOf.words M y H (Wc.pocket i) D r' (Sp i) (Wc.o' i)
local notation "A₁"=> fun i=> BoxOf.glints (C' i).pose (C' i).starts (C' i).reader ∅ (Sg i) r' SxN
local notation "B₁"=> fun i=> BoxOf.words (S' i).pose (S' i).starts (S' i).reader (S' i).goal.val (Sm i) r' (Sp i) (WickReps.home fA r')
set_option quotPrecheck false

def grove : Root Q (Creek.theater H χ M y l Z v) (Creek.Academy H χ M y l Z v k) C' S' (r:=r'):= ⟨prefer Aʼ Pʼ, branch Mʼ Aʼ Pʼ r' (weights M y H ∅ D r' SxN χ l Z v),A₁,fun i=> weights (C' i).pose (C' i).starts (C' i).reader ∅ (Sg i) r' SxN χ (C' i).pay Set.univ 0,fun i=>prefer Aʼ (Qʼ i), B₁⟩
local notation "Lʼ"=> grove Q H M y l Z v D o' Wc C' S' Sg Sm SxN Sp
local notation "R₁"=> BoxOf.roots M y H D o' Wc
variable (i:Cargo.Inquiry (ιa:=Sleet.Staff (brand M y) H) (ιb:=ιb) Q C' S')
structure Traversal (P:Patch) : Prop where
    fibers : BoxOf.Valley Ω P H χ M y D r' SxN l Z v C' Sg
    links j : BoxOf.Launch Ω P H χ M y D (Wc.pocket j) r' (Sp j) l Z v (S' j) (Sm j) (Wc.o' j) (Cargo.sun o' Wc wP j)
structure Answers : Prop where
    grants j : ∀ t∈BoxOf.glints (C' j).pose (C' j).starts (C' j).reader ∅ (Sg j) r' SxN,t∈Pier.pays Q (C' j)
    debts j : ∀ t∈ (i.vacuum j).A,t∈ Pier.pays Q (C' j)→t∈BoxOf.glints (C' j).pose (C' j).starts (C' j).reader ∅ (Sg j) r' SxN
    sails j : ∀ t∈BoxOf.words (S' j).pose (S' j).starts (S' j).reader (S' j).goal.val (Sm j) r' (Sp j) (WickReps.home fA r'), t∈Pier.pays Q (S' j)
    valued j : ∀ t∈(i.marks j).A,t∈Pier.pays Q (S' j)→ t∈BoxOf.words (S' j).pose (S' j).starts (S' j).reader (S' j).goal.val (Sm j) r' (Sp j) (WickReps.home fA r')
    owns :∀ t∈ i.physicalA,t∈BoxOf.roots M y H D o' Wc → t∈ BoxOf.glints M y H ∅ D r' SxN∨∃ j:δ,t∈BoxOf.words M y H (Wc.pocket j) D r' (Sp j) (Wc.o' j)
variable (P₁:Patch)
variable (ht: Traversal Q Ω H M y l Z v D o' Wc wP C' S' Sg Sm SxN Sp P₁)(hh: Answers Q H M y D o' Wc C' S' Sg Sm SxN Sp i)
variable (hB: Bloom H χ)(hp:∀ i:Stars,Bloom (C' i).reader χ) (hz: P'.threshold=Pressure.temp x)(hv: Enlightened Ω P₁ P Q o x μ L χ)
include ht hh hB hp hz hv
lemma crown : Trunk Q P' Mʼ Aʼ R₁ o' Wc wP C' S' Lʼ i:=by
   have hP (i) (hi:i∈ Pʼ) := ((BoxOf.blink M y H ∅ D).mp hi).beginF
   have hf j (i)(hi:i∈ Qʼ j) := (BoxOf.shine M y H (Wc.pocket j) D (Wc.o' j) |>.1 hi)
   refine ⟨fun j hj=>?_,fun j i hi=>?_,fun u=>?_,fun u j=>?_,fun j i hi=> hh.grants j i hi,fun j i hi=>hh.debts j i hi.1 hi.2,fun j i hi=>hh.sails j i hi,fun j i hi=> hh.valued j i hi.1 hi.2,fun j hj=>?_⟩
   · exact BoxOf.grace M y H ∅ D χ l Z v (hP _ ((prefers ..).1 hj))
   · have hl := hf j i.val ((prefers ..).1 hi); refine ⟨?_,BoxOf.grace M y H (Wc.pocket j) D χ l Z v hl.fair⟩
     change Manor.halls Mʼ i.val⊆_; rw [Creek.point]; exact hl.roam
   · change WickReps.Sensible P' r' ((peel Mʼ Aʼ).sector u _ (branch Mʼ Aʼ Pʼ r' (weights M y H ∅ D r' SxN χ l Z v))) _; rw [choirA]; exact BoxOf.beams Ω P₁ H χ M y D r' SxN l Z v C' Sg P' ht.fibers hv hB hp hz u
     exact fun i hi=> (BoxOf.admittance M y H ∅ D χ l Z v (hP _ hi) (by simp)).1
   · change Matches (Apo.slab (peel Mʼ Aʼ) (prefer Aʼ (Qʼ j)) u) _ P' _ _ _; rw [choirB Mʼ Aʼ]; exact BoxOf.starlight Ω P₁ H χ M y D _ r' (Sp j) l Z v P' hv hB hz u (S' j) (Sm j) _ _ (ht.links j)
     exact fun t ht=> (BoxOf.admittance M y H (Wc.pocket j) D χ l Z v (hf j t ht).fair (Wc.admits j)).1
   rcases hh.owns j.val hj.1 hj.2 with h|⟨x,h⟩; exact Or.inl ((prefers ..).2 h); exact Or.inr ⟨x,(prefers ..).2 h⟩
end YM.RemainderComparison.Orbits
