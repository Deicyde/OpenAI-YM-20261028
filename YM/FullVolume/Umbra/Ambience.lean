import YM.FullVolume.Poesy.Soles
import YM.FullVolume.Poesy.Nocturne
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
open Yard Ovens Ovens.Pipes
open Slide Marlin
lemma preTouch (B:BudgetPoint)(A: Listing G c) (k z:ℕ)(V V':ℕ→Trio.Offer G c)(f g: ℕ→ Trio.Offer G c) {D D':ℕ→ Collection.Source G c}(h:Canopy B A.reg (fun n=>(D n).logRead) (fun n=>(D' n).logRead))(hh: Angel (fun n=>(D n).hardRead) (fun n=> (D' n).hardRead))(hv:Canopy B (Marlin.leap k) V V')(ht:Angel f g) : Angel (fun n=> (Marlin.bison (D n) (V n) (f n)).logarithm) (fun n=> (Marlin.bison (D' n) (V' n) (g n)).logarithm):=by
    let d(n):= bison (D n) (V n) (f n); let d' n:= bison (D' n) (V' n) (g n); let f' n (i:Civ c):= Sum.elim (fun _=> (0:Config G c→ℝ)) (choir (-f n)) i; let g' n(i:Civ c):= Sum.elim (fun _=> (0:Config G c→ℝ)) (choir (-g n)) i
    have hl :Angel f' g':=by
         apply Angel.both Angel.empty
         have hx {P:ℕ→ Site c→ Config G c→ℝ}(h:Vented P):Vented (fun i=> choir (-P i)) :=by
             obtain ⟨w,hw,W⟩:=h.sup; refine ⟨_,(trep (ι:=Seat c) hw).climb (Song.rim_nn c),fun n v x=> ?_⟩
             unfold choir; dsimp only [Pi.smul_apply, Pi.neg_apply]; rw [norm_smul, Real.norm_of_nonneg (Song.rim_nn c)]; simp only [Function.comp_apply, Pi.neg_apply,norm_neg]; exact mul_le_mul_of_nonneg_left (W ..) (Song.rim_nn c)
         refine ⟨hx ht.a,hx ht.b,fun ⟨i,x⟩ b hb=>recover (F:=fun n=>f' n (.inr (i,x))) (H:=fun n=> g' n (.inr (i,x))) (fun V=>?_) b hb⟩
         exact (tendsto_iff_ultrafilter ..).mpr fun J hj=> ((ht.glints hj x (fun n=>i.view (V n))).bin (Q:=fun x:ℝ=> Song.Rim c* (-x)) (fun _ _=>continuousAt_const.mul continuousAt_id.neg)).shrank
    exact hl.forms (leanU c).toEmbedding
end YM.ConnectedActivityE6.Lim
