import YM.FullVolume.Poesy.Poem
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
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
open Geo WilsonStartup
variable {M:Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){χ:Chi}(R:∀ n,Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
   {B:BudgetPoint}{v v':ℕ→ℝ} (h:Accord K H B v v') (hp:B.threshold=Pressure.temp x)(he:B.order≤ j)
namespace Accout
include I T R P' h hp he
abbrev clav {U:Epoch Λ}(H: Epoch.Port (o:=o) (R:=Q) (x:=x) (μ:=μ) (C:=C₀) (L:=L) U):= staple (H:=H) (J:=H) rfl rfl rfl
lemma poses (A:(I 0).fragrances→RegularAddress c)(hx:∀ z,(A z).support=perf (I 0) z) : Canopy B (Song.revolve (Sum.elim A (strings (K 0).down.path B))) (fun n=> choir (opus (I n) (clav (I n)) χ (v n))) (fun n=> choir (opus (T n) (clav (T n)) χ (v' n))):=by
     let G:= (clav (I 0)).furrow; let V i:= A (G.symm i)
     apply laurels; refine Canopy.splices ?_ (pathCue h c)
     have hA:= ((Draft.concordance I T R P' h.fore h.tail h.mirror B hp he V (fun z=> by unfold V; rw [hx, Song.reconnects (I 0) (clav _)]; change _=perf (I 0) z; rw [show _=z from G.apply_symm_apply z])).multiply (-1)).transI G.toEmbedding
     rw [show (fun i=> (fun j=> V j) (G.toEmbedding i))=A from funext fun i=> congr_arg A (G.symm_apply_apply i)] at hA; exact hA
omit hp he in
lemma chorals : Angel (fun i (j:Annual (I 0))=> fuse (I i) (clav (I i)) χ j) (fun i (j:Annual (I 0))=>fuse (T i) (clav (T i)) χ j):=by
     apply Angel.both _ Angel.empty; let g:= (clav (I 0)).tongs; let K:(Leaf (I 0))↪ (I 0|>.Chainbook):= (Embedding.subtype _).trans g.toEmbedding; exact (Draft.cardigan I T R P' h.fore h.tail h.mirror).forms K
lemma pallor : Canopy B (Beam.marquee (I 0) B).reg (fun i=> (plusone (I i) (clav (I i)) χ (v i)).logRead) (fun i=>(plusone (T i) (clav (T i)) χ (v' i)).logRead):=
   (poses I T R P' h hp he (Beam.dashboard (I 0)) (Beam.see _)).transI (pennant (I 0)).toEmbedding
lemma candles : Canopy B (Song.posting B (I 0)).reg (fun i=> (plusone (I i) (clav (I i)) χ (v i)).logRead) (fun i=>(plusone (T i) (clav (T i)) χ (v' i)).logRead):=
    (poses I T R P' h hp he (Song.locate (I 0)) (fun _=>rfl)).transI (pennant (I 0)).toEmbedding
omit hp he in
lemma lusters : Angel (fun i=> (plusone (I i) (clav (I i)) χ (v i)).hardRead) (fun i=> (plusone (T i) (clav (T i)) χ (v' i)).hardRead):=(chorals I T R P' h).forms (badge (I 0)|>.toEmbedding)
end Accout
end YM.ConnectedActivityE6.Lim
