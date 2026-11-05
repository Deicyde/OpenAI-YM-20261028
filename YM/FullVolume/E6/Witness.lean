import YM.FullVolume.E6.Fruits
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
open Pressure.Stores
namespace Finish
variable (h: Finish J K H)(U₀:ℕ→ Config G c)(V:ℕ→ Config G f)(T:ℕ→ Config G c)(s d:ℝ)
set_option quotPrecheck false
local notation "X"=> fun n=> (K n).tubes
local notation "X'"=> fun n=> (H n).tubes
include h
lemma visionsP (k i) (hd:0<d) : Glints J (fun n=>(X n).vision k d (U₀ n) i) (fun n=> (X' n).vision k d (U₀ n) i):=by
    rcases i with ⟨i,j|j⟩
    · let f(U:Config G c):= thinned (K 0).down.path Λ.low d S.patch.L.val k U (i,false)
      have hp n : ‖f (U₀ n)‖ ≤ ‖Real.sqrt Λ.low.direct‖* 2 := by
             let u:= toll (U₀ n) i; change ‖(if u=0 then (1:ℝ) else min 1 (d/u)) • _‖≤ _; have hu:0≤u:=G.chord_nonneg _; rw [norm_smul]; apply (mul_le_of_le_one_left (norm_nonneg _) _).trans
             · rw [Pressure.shoot,norm_smul]; exact mul_le_mul_of_nonneg_left ((G.curvature_norm _).trans (G.chord_le_two _)) (norm_nonneg _)
             split; · rw [norm_one]
             rw [Real.norm_of_nonneg (le_min zero_le_one (by positivity))]; exact min_le_left ..
      exact FullVolume.Shadow.flowers (f:=fun n=>f (U₀ n)) (x:=0) (Eventually.of_forall fun i=>by simpa using hp i)
    exact switch ((h.overC (Quincy.standards J U₀) (x:=(0:ℝ)) (j:=0) (i,true) k).crest) ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=>PathData.kept Λ.low d i.1 (U₀ n))
lemma movF (k i)(hd:0<d):Glints J (fun n=>(X n).Mv k d (U₀ n) i) (fun n=>(X' n).Mv k d (U₀ n) i):=
    ((Frill.buds Finset.univ fun j _=> keeping (h.taps (Quincy.standards J U₀) (j:=0) (x:=(0:ℝ)) i j k) (Frill.bare (h.visionsP U₀ d k j hd))).crest)
lemma movI (k i)(hd:0<d):Glints J (fun n=>(X n).Mw k d (U₀ n) i) (fun n=>(X' n).Mw k d (U₀ n) i):=
    ((Frill.buds Finset.univ fun j _=> keeping (h.toes (Quincy.standards J U₀) (j:=0) (x:=(0:ℝ)) i j k) (Frill.bare (h.visionsP U₀ d k j hd))).crest)
lemma movN (k i)(hd:0<d):Glints J (fun n=> zip ((X n).N k (U₀ n)) ((X n).vision k d (U₀ n)) i) (fun n=>zip ((X' n).N k (U₀ n)) ((X' n).vision k d (U₀ n)) i):=
    ((Frill.buds Finset.univ fun j _=> keeping (h.boots (Quincy.standards J U₀) (j:=0) (x:=(0:ℝ)) i j k) (Frill.bare (h.visionsP U₀ d k j hd))).crest)
lemma whole (i:Spot c f)(hs: 0<Pressure.temp s): Glints J (fun n=> principal (X n) s (V n) (U₀ n) (T n) i) (fun n=> principal (X' n) s (V n) (U₀ n) (T n) i):=by
   let R:= Pressure.Stores.till s; let d:=Pressure.temp s; let t:=Pressure.fiery G s S.patch.L
   have hv:=Quincy.standards (x:=(0:ℝ)) (j:=0) J V; have hu:= Quincy.standards (x:=(0:ℝ)) (j:=0) J U₀; have hF p:= h.overF hv p R; have hC p:= h.overC hu p R; have hT p:=Frill.bare (h.visionsP U₀ d R p hs) (n:=0) (x:=(0:ℝ)); have hG p:= Frill.bare (h.movF U₀ d R p hs) (n:=0) (x:=(0:ℝ)); have hI p:= Frill.bare (h.movI U₀ d R p hs) (n:=0) (x:=(0:ℝ)); have hN p:= Frill.bare (h.movN U₀ d R p hs) (n:=0) (x:=(0:ℝ)); have hz i:= Finish.raysK (S:=S) hu T i
   rcases i with i|i|i|i
   · exact (((Frill.bare (h.up.roof Λ.high V i R 1 t Nat.zero_lt_one)).add (Frill.buds Finset.univ fun j _=> (snowy (hG (i,j))).sub ((hG (i,j)).inn (hF (i,j))))).crest)
   · have hp : Frill J 0 (0:ℝ) (fun n _=> monetary S (T n) (U₀ n) i) (fun n _=> monetary S (T n) (U₀ n) i):= ((((Frill.still S.kernel.penalty).times (((hu i).glowing (Strand.banners J (fun n=> ((T n) i)⁻¹))).chordwise))).via (contDiff_id.div_const 2))
     exact ((hp.add ((snowy (hI i)).sub ((hI i).inn (hz i)))).crest)
   · have hp := (Frill.buds Finset.univ (ι:=Bool) fun j _=> ((hT (i,j)).inn (hC (i,j))).sub (snowy (hT (i,j)))).sub (Frill.bare (h.down.roof Λ.low U₀ i R S.patch.L.val d S.patch.L.property));
     have hz':= Frill.buds Finset.univ (ι:=Bool) fun j _=> (hT (i,j)).inn (((Frill.buds Finset.univ fun q _=> bearing (h.taps hu q (i,j) R) (hF q)).add (Frill.buds Finset.univ fun q _=> bearing (h.toes hu q (i,j) R) (hz q))).sub (hC (i,j)))
     have hM:= Frill.buds Finset.univ (ι:=Bool) fun j _=> ((hT (i,j)).inn ((hT (i,j)).sub (((Frill.buds Finset.univ fun q _=> bearing (h.taps hu q (i,j) R) (hG q)).add (Frill.buds Finset.univ fun q _=> bearing (h.toes hu q (i,j) R) (hI q))).add (Frill.buds Finset.univ fun q _=> bearing (h.boots hu q (i,j) R) (hN q))))).via (Q:=fun s:ℝ=> s/2) (contDiff_id.div_const _)
     exact (hp.add (hz'.add hM)).crest
   exact (snowy (hN i)).crest
lemma led (i:Spot c f)(hs:0<Pressure.temp s)(k:S.Choices) : Glints J (fun n=> yielding (X n) s (V n) (U₀ n) k i) (fun n=> yielding (X' n) s (V n) (U₀ n) k i):=by
   rcases i with i|i
   · let R:=Pressure.Stores.till s; have hF:=Quincy.standards (j:=0) (x:=(0:ℝ)) J V
     exact (((Frill.still Λ.high.direct).times (hF.pores i |>.flawing)).add (Frill.buds Finset.univ fun p _=> snowy ((h.overF hF (i,p) R).sub (Frill.bare (h.movF U₀ (Pressure.temp s) R (i,p) hs))))).crest
   exact h.whole U₀ V (fun n=>S.prediction (V n) k) s (.inr i) hs
end Finish
end YM.ConnectedActivityE6.Lim
