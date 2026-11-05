import YM.RemainderComparison.Funk.Drummer
import YM.RemainderComparison.Seedlings.Dawn
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
-- Generic for models & actual.Plan Builder doesn't consume spectra physically. Marks roots.B.
variable (A:Manor G c ι α ιa)(F:Manor G c ι α ιb)(K:Set ιa) (E:Set ιa)(U:Set ιb)(Z:Set ι)
local notation "XΓ"=> Lobby.peel A K
local notation "M₁"=> Lobby.mural A F K
variable {r k:ℕ} (o':ι→Site c)(roots:ι→Support c)(Wc:Breeze.Careers ι δ c o' r k)(wP:ι→ℝ)
local notation "St"=> Cargo.sun o' Wc wP
variable {Y:Stars→Side}(C':∀ i:Stars, Pier (Y i) G W x μ L Q o C β χ α)(S':δ→Pier f G W x μ L Q o C β χ α)

-- one raw proposal using eligibility stopping tape.No limits geometry
structure Root where
   vac : Finset K
   basis : Manor.Basis (Lobby.peel A K) vac r
   star : ∀ i:Stars, Finset (Pier.staff Q χ (C' i))
   seated : ∀ i:Stars, Basis (Pier.vane Q χ (C' i)) (star i) r
   aims : δ→ Finset K
   moon : ∀ i:δ, Finset (Pier.staff Q χ (S' i))
structure Sap where
   vac : Finset ιb
   basis : Manor.Basis F vac r
   star : ∀ i:Stars, Finset (C' i).token
   seated : ∀ i:Stars, Basis (C' i).spill (star i) r
   aims : δ→ Finset ιb
   moon : ∀ i:δ, Finset (S' i).token
variable (R':Root Q A K C' S' (r:=r)) (T':Sap Q F C' S' (r:=r)) (i:Cargo.Inquiry (ιa:=ιa) (ιb:=ιb) Q C' S')
local notation "Pk"=> Wc.pocket
structure Ground : Prop where
   life j : 0 < Verse.load Z (Wc.pocket j).val
   mark j t : t∈ Wc.pocket j→ roots t ⊆ neighbors r (Wc.o' j)
   incomes j : (S' j).goal≠Next.Rank.Glyph.quiet (S' j).τ
structure Trunk : Prop where
   calls j : j∈R'.vac → (Lobby.peel A K).marks j=0
   life j t : t∈ R'.aims j→ (Lobby.peel A K).halls t ⊆ neighbors r (Wc.o' j) ∧ (Lobby.peel A K).marks t=(Wc.pocket j).val
   chants u : WickReps.Sensible P' r ((Lobby.peel A K).sector u R'.vac R'.basis) (fun i:Stars=> Manor.sector (Pier.vane Q χ (C' i)) u (R'.star i) (R'.seated i))
   hearth u i : WickReps.Matches (Apo.slab (Lobby.peel A K) (R'.aims i) u) (Apo.slab (Pier.vane Q χ (S' i)) (R'.moon i) u) P' r (Wc.o' i) (Cargo.sun o' Wc wP i)
   is j : (R'.star j:Set (Pier.staff Q χ (C' j)))⊆ Pier.pays Q (C' j)
   much j : ((i.vacuum j).A:Set (Pier.staff Q χ (C' j)))∩ Pier.pays Q (C' j) ⊆ R'.star j
   wane j : (R'.moon j:Set (Pier.staff Q χ (S' j)))⊆ Pier.pays Q (S' j)
   mulch j : ((i.marks j).A:Set (Pier.staff Q χ (S' j)))∩Pier.pays Q (S' j) ⊆ R'.moon j
   taken j : j.val∈(i.physicalA:Set ιa)∩E→j∈R'.vac∨∃ u:δ,j∈R'.aims u
structure Graft : Prop where
   calls j : j∈T'.vac → F.marks j=0
   life j t : t∈ T'.aims j→ F.halls t ⊆ neighbors r (Wc.o' j) ∧ F.marks t=(Wc.pocket j).val
   chants u : WickReps.Sensible P' r (F.sector u T'.vac T'.basis) (fun i:Stars=> Manor.sector (C' i).spill u (T'.star i) (T'.seated i))
   hearth u i : WickReps.Matches (Apo.slab F (T'.aims i) u) (Apo.slab (S' i).spill (T'.moon i) u) P' r (Wc.o' i) (Cargo.sun o' Wc wP i)
   is j : (T'.star j:Set (C' j).token)⊆ (C' j).owes
   much j : ((i.vacuum j).B:Set (C' j).token)∩ (C' j).owes ⊆ T'.star j
   wane j : (T'.moon j:Set (S' j).token)⊆ (S' j).owes
   mulch j : ((i.marks j).B:Set (S' j).token)∩ (S' j).owes ⊆ T'.moon j
   taken j : j∈(i.physicalB:Set ιb)∩U→j∈T'.vac∨∃ u:δ,j∈T'.aims u

variable (hp: Ground Q Z o' roots Wc S')(hf:Trunk Q P' A K E o' Wc wP C' S' R' i)(hh:Graft Q P' F U o' Wc wP C' S' T' i)
def shades (i:δ) := (R'.aims i).disjSum (T'.aims i)
def leafVac := R'.vac.disjSum T'.vac
local notation "V₁"=> leafVac Q A F K C' S' R' T'
def leaf :Basis (mural A F K) V₁ r:=by
    refine ⟨fun x j=> j.elim (R'.basis.support x) (T'.basis.support x), fun x j=>?_,fun j hj=>?_,fun x j hj=>?_⟩ <;> cases j with
    | inl j=> first| exact  R'.basis.sto x j | exact  R'.basis.account j (inl_mem_disjSum.mp hj) | exact  R'.basis.location x j (inl_mem_disjSum.mp hj)
    | inr j=> first| exact  T'.basis.sto x j | exact  T'.basis.account j (inr_mem_disjSum.mp hj) | exact  T'.basis.location x j (inr_mem_disjSum.mp hj)
local notation "Sx"=> shades Q A F K C' S' R' T'
include hf hh
lemma offered (j:δ)(t:K⊕ιb)(h:t∈Sx j): (M₁).halls t ⊆ neighbors r (Wc.o' j)∧ (M₁).marks t=(Wc.pocket j).val:=by cases t; exact hf.life _ _ (inl_mem_disjSum.mp h); exact hh.life _ _ (inr_mem_disjSum.mp h)
def make : (M₁).Quarry Set.univ δ roots r:=
   ⟨fun j=>⟨Wc.o' j,neighbors r (Wc.o' j),(neighbors_mem ..).2 (by rw [separation_self]; omega)⟩,fun _=>rfl, Sx, fun i=>(Pk i).val,
        hp.mark,fun j t h=> ⟨Set.mem_univ _, offered Q P' A F K E U o' Wc wP C' S' R' T' i hf hh j t h⟩,
        fun j t hx=> Finset.disjoint_left.mpr (fun x h he=>hx (Wc.pocket.injective (Finset.val_inj.mp (((offered Q P' A F K E U o' Wc wP C' S' R' T' i hf hh j _ h).2).symm.trans (offered Q P' A F K E U o' Wc wP C' S' R' T' i hf hh t _ he).2))))⟩
local notation "Dʼ"=> make Q P' A F K E U Z o' roots Wc wP C' S' R' T' i hp hf hh

def absorb : Cargo Q A F K roots C' S' r:= ⟨V₁,Orbits.leaf Q A F K C' S' R' T',Dʼ,fun i=>⟨R'.star i,T'.star i⟩,fun i=>⟨R'.moon i,T'.moon i⟩,fun i=>⟨R'.seated i,T'.seated i⟩⟩
local notation "Pt" => Orbits.absorb Q P' A F K E U Z o' roots Wc wP C' S' R' T' i hp hf hh
include hf hh hp
lemma pruned : Cargo.Striped Q A F K E U roots C' S' Pt i∧ Cargo.Underscore Q A F K Z roots C' S' o' Wc Pt wP P':=by
    refine ⟨⟨⟨fun j h=>?_,fun j h=>?_⟩,fun j=>⟨hf.is j,hf.much j,hh.is j,hh.much j⟩,fun j=>⟨hf.wane j,hf.mulch j,hh.wane j,hh.mulch j⟩⟩,⟨⟨fun u=>?_,fun u=>?_,fun j h=>?_⟩,⟨hp.incomes,fun u i'=>?_,fun u i'=>?_⟩,fun _=>rfl,fun _=>rfl,hp.life⟩⟩
    · rcases hf.taken j h with hV|⟨l,hV⟩; exact Or.inl (show Sum.inl j∈ V₁ from inl_mem_disjSum.mpr hV); exact Or.inr ⟨l,(show Sum.inl j∈ Sx l from inl_mem_disjSum.mpr hV)⟩
    · rcases hh.taken j h with hV|⟨l,hV⟩; exact Or.inl (show Sum.inr j∈ V₁ from inr_mem_disjSum.mpr hV); exact Or.inr ⟨l,(show Sum.inr j∈ Sx l from inr_mem_disjSum.mpr hV)⟩
    · rw [show Manor.sector (peel A K) u _ (chairs₁ A F K (Pt).chosen (Pt).seats)= (XΓ).sector u R'.vac R'.basis from (by funext j X; change (∑ i∈(R'.vac.disjSum T'.vac).toLeft,R'.basis.support j i*(XΓ).solvent u i X)=_; rw [toLeft_disjSum]; rfl)]
      exact hf.chants u
    · rw [show Manor.sector F u _ (chairs₂ A F K (Pt).chosen (Pt).seats)= F.sector u T'.vac T'.basis from (by funext j X; change (∑ i∈(R'.vac.disjSum T'.vac).toRight,T'.basis.support j i*F.solvent u i X)=_; rw [toRight_disjSum]; rfl)]
      exact hh.chants u
    · cases j; exact hf.calls _ (inl_mem_disjSum.mp h); exact hh.calls _ (inr_mem_disjSum.mp h)
    · change Matches (Apo.slab XΓ ((R'.aims i').disjSum (T'.aims i')).toLeft u) (Apo.slab _ (R'.moon i') u) P' r (Wc.o' i') _; rw [toLeft_disjSum]; exact hf.hearth u i'
    · change Matches (Apo.slab F ((R'.aims i').disjSum (T'.aims i')).toRight u) (Apo.slab (S' i').spill (T'.moon i') u) P' r (Wc.o' i') _; rw [toRight_disjSum]; exact hh.hearth u i'
omit hf hh
lemma stem (hf:∀ i,∃ R',Trunk Q P' A K E o' Wc wP C' S' R' (i:=i) (ιb:=ιb)) (ht:∀ i,∃ T',Graft Q P' F U o' Wc wP C' S' T' (i:=i) (ιa:=ιa)) : Cargo.Orchestra Q A F K E U Z roots C' S' o' Wc wP P':= by
    refine ⟨fun i=>?_⟩; obtain ⟨R',hf⟩:=hf i; obtain ⟨T',ht⟩:= ht i; exact ⟨_,pruned Q P' A F K E U Z o' roots Wc wP C' S' R' T' i hp hf ht⟩
end YM.RemainderComparison.Orbits
