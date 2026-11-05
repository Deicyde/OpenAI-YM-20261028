import YM.RemainderComparison.Orbits.Bole
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
variable (P₁:Patch)
variable (i:Cargo.Inquiry (ιa:=Sleet.Staff (Typeface.brand M y) H) (ιb:=ιb) Q C' S')
-- reads defined in Pose (exact payment spec). producer RG03. Goal pays includes POSITIVE.RT ringSet
structure Foilage : Prop where
    blank j : (C' j).goal=Next.Rank.Glyph.quiet (C' j).τ
    reads j : (C' j).reads= BoxOf.collection (C' j).pose (C' j).starts (C' j).reader (Next.Rank.Glyph.quiet (C' j).τ) ∪ {s|∃ n,s∈ BoxOf.glints (C' j).pose (C' j).starts (C' j).reader ∅ (Sg j) r' n}
    charts j : (S' j).reads= BoxOf.collection (S' j).pose (S' j).starts (S' j).reader (S' j).goal ∪ {s|∃ n,s∈ BoxOf.words (S' j).pose (S' j).starts (S' j).reader (S' j).goal.val (Sm j) r' n (WickReps.home fA r')}
set_option quotPrecheck false
variable (h: Foilage (r':=r') Q C' S' Sg Sm)
local notation "Ps"=> BoxOf.glints
local notation "Qv"=> BoxOf.words
include h
lemma trees (u: Stars) (t : Pier.staff Q χ (C' u)) : t∈Pier.pays Q (C' u)↔∃ n, t∈ BoxOf.glints (C' u).pose (C' u).starts (C' u).reader ∅ (Sg u) r' n:=by
    rw [Pier.pays,h.blank u,h.reads]; constructor
    · intro h; exact h.1.resolve_left fun hp=>hp h.2
    rintro ⟨n,ht⟩; have hz:= ((BoxOf.blink ..).1 ht).beginF
    refine ⟨Or.inr ⟨n,ht⟩,hz.leaves,Subtype.ext ?_⟩; exact hz.atlas.symm

lemma starred (j : δ) (t : Pier.staff Q χ (S' j)) : t∈Pier.pays Q (S' j) ↔ ∃ n,t∈ BoxOf.words (S' j).pose (S' j).starts (S' j).reader (S' j).goal.val (Sm j) r' n (WickReps.home fA r'):=by
    rw [Pier.pays,h.charts]; constructor
    · intro h; exact h.1.resolve_left fun hp=> hp h.2
    rintro ⟨n,ht⟩; have hz:= ((BoxOf.shine ..).1 ht).fair
    exact ⟨Or.inr ⟨n,ht⟩,hz.leaves,Subtype.ext hz.atlas.symm⟩
-- finite selection.
omit h
lemma notebook {α:Type*}(g:ℕ→Finset α)(h:Monotone g)(k:Finset α):(∀ᶠ m:ℕ in atTop,∀ i∈k, (∃ n:ℕ,i∈g n)→ i∈g m):=by
    refine (eventually_all_finset k).mpr fun i _=>?_; by_cases he: ∃ n,i∈g n
    · obtain ⟨n,hx⟩:=he; exact (eventually_ge_atTop n).mono fun s hs _=> h hs hx
    exact Filter.Eventually.of_forall fun _ h=> False.elim (he h)
include h
lemma answers : ∃ N Sm', Answers Q H M y D o' Wc C' S' Sg Sm N Sm' i:=by
   have hx (j:Stars) : ∀ᶠ m:ℕ in atTop,∀ t∈(i.vacuum j).A,t∈Pier.pays Q (C' j)→ t∈ BoxOf.glints (C' j).pose (C' j).starts (C' j).reader ∅ (Sg j) r' m:=
      (notebook _ (stars_for ..) (i.vacuum j|>.A)).mono fun _ he t ht hX=> he t ht ((trees Q C' S' Sg Sm h j t).1 hX)
   have hf (j:δ) : ∀ᶠ m:ℕ in atTop,∀ t∈(i.marks j).A,t∈Pier.pays Q (S' j)→ t∈ BoxOf.words (S' j).pose (S' j).starts (S' j).reader (S' j).goal.val (Sm j) r' m (WickReps.home fA r'):= (notebook _ (marks_for ..) (i.marks j|>.A)).mono fun _ he t ht hX=> he t ht ((starred Q C' S' Sg Sm h j t).1 hX)
   obtain ⟨m,hV,hP⟩:= ((eventually_all.mpr hx).and (notebook (fun i=>BoxOf.glints M y H ∅ D r' i) (stars_for ..) i.physicalA)).exists
   choose w hw hG using fun j=> ((hf j).and (notebook _ (marks_for M y H (Wc.pocket j) D r' (Wc.o' j)) i.physicalA)).exists
   exact ⟨m,w,fun j t ht=> (trees Q C' S' Sg Sm h j t).2 ⟨m,ht⟩, hV,fun j t ht=> (starred Q C' S' Sg Sm h j t).2 ⟨w j,ht⟩,hw,fun t ht h=> (show _ ∨ ∃ j n,t∈ BoxOf.words M y H (Wc.pocket j) D r' n (Wc.o' j) from h).imp (hP t ht) (fun ⟨j,h⟩=> ⟨j,hG j t ht h⟩)⟩ -- ellipsis

variable (hB: BoxOf.Bloom H χ)(hp:∀ i,Bloom (C' i).reader χ)(hz: P'.threshold=Pressure.temp x)(hv: Enlightened Ω P₁ P Q o x μ L χ)
variable (hf:∀ N M',Traversal Q Ω H M y l Z v D o' Wc wP C' S' Sg Sm N M' P₁)
local notation "R₁"=> BoxOf.roots M y H D o' Wc
include h hf hB hv hz hp
lemma willing : ∃ R',Trunk Q P' Mʼ Aʼ R₁ o' Wc wP C' S' R' i:=by
   obtain ⟨m,n,h⟩:= answers Q H M y D o' Wc C' S' Sg Sm i h; exact ⟨_,Orbits.crown Q Ω P' H M y l Z v D o' Wc wP C' S' Sg Sm m n i P₁ (hf m n) h hB hp hz hv⟩
end YM.RemainderComparison.Orbits
