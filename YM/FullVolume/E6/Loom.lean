import YM.FullVolume.Artes.Events
import YM.FullVolume.C.Songbook
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
structure Cad (G:Gauge) where
    fare:PlaqAxes→ℕ→ℝ
    d2:ℕ→(Fin 2→G.ColorIndex)→ℝ
    d3:ℕ→(Fin 3→G.ColorIndex)→ℝ
    d4:ℕ→(Fin 4→G.ColorIndex)→ℝ
-- Actual common dictionary; the proof is not by placing fresh marks at common zeros
abbrev Cad.path (V:Cad G): PathData G:=⟨fun i j=>(V.fare i j,Beacon.flag j),fun i=>⟨letter (t:=1) i,V.d2 i⟩,fun i=>⟨letter (t:=2) i,V.d3 i⟩,fun i=>⟨letter (t:=3) i,V.d4 i⟩⟩
abbrev Cad.pure (P:PathData G): Cad G:=⟨fun x y=>(P.row x y).1,fun i=>(P.loop i).coeff,fun i=>(P.cubic i).coeff,fun i=>(P.quartic i).coeff⟩
structure Era (G : Gauge)(S : StepData c f) where
    high : Clip
    low: Clip
    p:BudgetPoint -- incoming
    reg:ℕ→RegularAddress f
    hard:ℕ→ForcedAddress G f
structure Epoch (Λ:Era G S) where
    R : Towers S.patch.L
    up : Cad G
    down: Cad G
    e : ℕ→ Config G f→ℝ
    k : ℕ→ Config G f→ℝ
    beta:ℝ
    v:ℝ
namespace Epoch
variable {Λ:Era G S} (Z : Epoch Λ)
abbrev tubes: Tube G S:= ⟨Z.R,Z.up.path,Λ.high,Z.down.path,Λ.low⟩
abbrev kin: Rep G f:= ⟨(tubes Z).up,(tubes Z).high,⟨Λ.reg,Λ.hard,Z.e,Z.k⟩,Λ.p,Z.beta,Z.v⟩
variable {W x μ C:ℝ}{R:ConnectedActivityE6.Target G P}{o:Target.Order G W}
abbrev Port := Cash W x μ L R o C Z.tubes Z.kin
variable {Y:Epoch Λ} {Z} (I:Port (o:=o) (R:=R) (x:=x) (μ:=μ) (L:=L) (C:=C) Z) (H : Port (o:=o) (R:=R) (x:=x) (μ:=μ) (L:=L) (C:=C) Y)
lemma borne : I.supportP=H.supportP :=rfl
lemma tracts : Raw.extra Z.tubes Z.kin= Raw.extra Y.tubes Y.kin := rfl
lemma seam : I.smallAt=(fun i:I.ThinP=> H.smallAt i):= by rfl
lemma numbering : pennant H=(show ℕ ≃ Song.ballad H from pennant I):=rfl
lemma boundaries : badge H=(show ℕ ≃ _ from badge I):=rfl
lemma shape (p:BudgetPoint) : Beam.marquee H p= Beam.marquee I p:= rfl
lemma posts (p:BudgetPoint) : Song.posting p H = Song.posting p I:=rfl
private theorem charm (z) (h:Meadow.Stir I z):Meadow.Stir H z:=by
    refine ⟨h.small,fun i=>⟨?_,(h.each i).sizes,fun k=>?_⟩,h.moves⟩
    · exact (h.each i).hot
    exact (h.each i).earns k
lemma rosebud (v:ℕ) : Meadow.bouquet H v=(show Finset (Magazine H) from Meadow.bouquet I v):=by
    suffices he : ∀ j:Magazine I, (show Magazine H from j)∈ Meadow.bouquet H v ↔ j∈ Meadow.bouquet I v by ext i; exact he i
    rintro (i|i)
    · change Sum.inl (show H.fragrances from i)∈_ ↔ _; simp only [Meadow.bouquet,inl_mem_disjSum,Finset.mem_map]; constructor
      · rintro ⟨⟨j,h⟩,hp,hq⟩; refine ⟨⟨j,charm H I j h⟩,(Meadow.tunes _ _).mpr ((Meadow.tunes (H:=H) ⟨j,h⟩ _).1 hp),hq⟩
      rintro ⟨⟨j,h⟩,hp,hq⟩; exact ⟨⟨j,charm I H j h⟩,(Meadow.tunes _ _).mpr ((Meadow.tunes (H:=I) ⟨j,h⟩ _).1 hp),hq⟩
    exact inr_mem_disjSum.trans inr_mem_disjSum.symm
lemma sparks (p:BudgetPoint)(v:ℕ): Meadow.garnerAt H p =Meadow.garnerAt I p ∧ Meadow.panel H v= Meadow.panel I v:= by
    refine ⟨rfl,?_⟩
    ext i; rw [Meadow.petaled, Meadow.petaled,rosebud I H v]; rfl
end Epoch
end YM.ConnectedActivityE6.Lim
