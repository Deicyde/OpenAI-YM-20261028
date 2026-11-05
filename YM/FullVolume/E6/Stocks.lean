import YM.FullVolume.E6.Purse
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
lemma snowy {E:Type}[NormedAddCommGroup E][InnerProductSpace ℝ E]{Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]{F H:ℕ→Y→E}{p:Y}(h:Frill φ j p F H): Frill φ j p (fun i x=> ‖F i x‖^2/2) (fun i x=> ‖H i x‖^2/2):= h.via ((contDiff_norm_sq ℝ).div_const 2)
namespace Finish
open Scroll
variable (h:Finish J K H)(hx: Quincy J j p U U)(V:ℕ→ Config G f)(s:ℝ)(k:S.Choices)
set_option quotPrecheck false
local notation "T"=> fun n=> (K n).tubes
local notation "T'" => fun n=> (H n).tubes
local notation "M" => fun n=> S.prediction (V n) k
local notation "t" => Pressure.Stores.till s
include hx
lemma raysK (V':ℕ→ Config G c)(i:Bond c):Frill J j p (fun n y=> Tube.Z S (V' n) (U n y) i) (fun n y=> Tube.Z S (V' n) (U n y) i):= (Frill.still _).fee (((hx i).glowing (Strand.banners J (fun n=>(V' n i)⁻¹))).songs)
include h
lemma effectiveP (i) : Frill J j p (fun n y=> effective (T n) t (V n) (M n) (U n y) i) (fun n y=> effective (T' n) t (V n) (M n) (U n y) i):=by
   refine Frill.sub ?_ (h.highV hx t i); rcases i with i|i
   · exact h.overF (Quincy.standards J V) i t
   exact raysK (S:=S) hx (M) i
lemma fringeC (i:Cell c) : Frill J j p (fun n y=> stormD (T n) t (U n y) i) (fun n y=>stormD (T' n) t (U n y) i):=by
    let W (n:ℕ)(y:E):=canopyF (T n) t (U n y); have hc (i:Twin c):= h.overC hx (Prod.mk i.1 i.2 : Twin c) t
    refine Frill.buds Finset.univ (fun p _=> (((hc (i,p)).inn ((hc (i,p)).sub (((Frill.buds Finset.univ fun j _=> bearing (h.taps hx j (i,p) t) (h.higherF hx j t)).add (Frill.buds Finset.univ fun j _=> bearing (h.toes hx j (i,p) t) (h.higherI hx j t))).add (Frill.buds Finset.univ fun j _=> bearing (h.boots hx j (i,p) t) (h.higherN hx j t)))))).via (contDiff_id.div_const 2))
lemma driftK (i:Cell c): Frill J j p (fun n y=> stormL (T n) t (V n) (M n) (U n y) i) (fun n y=> stormL (T' n) t (V n) (M n) (U n y) i):=
    Frill.buds Finset.univ (fun q _=> (h.overC hx (i,q) t).inn (((Frill.buds Finset.univ fun j _=> bearing (h.taps hx j (i,q) t) (h.overF (Quincy.standards J V) j t)).add (Frill.buds Finset.univ fun j _=> bearing (h.toes hx j (i,q) t) (raysK (S:=S) hx (M) j))).sub (h.overC hx (i,q) t)))
lemma manor (i: Spot c f) (b:Bool): Frill J j p (fun n y=> loft (T n) s (V n) k (U n y) b i) (fun n y=> loft (T' n) s (V n) k (U n y) b i):=by
    rcases i with i|i|i|i
    · cases b
      · apply Frill.add (Frill.bare (h.up.roof Λ.high V i t 1 _ Nat.zero_lt_one)); exact Frill.buds Finset.univ fun q _=> (snowy (h.higherF hx (i,q) t)).sub ((h.higherF hx (i,q) t).inn (h.overF (Quincy.standards J V) (i,q) t))
      exact ((Frill.still Λ.high.direct).times ((Quincy.standards J V).pores i|>.flawing)).add (Frill.buds Finset.univ fun q _=> snowy (effectiveP h hx V s k (.inl (i,q))))
    · exact ((Frill.still _).times (((hx i).glowing (Strand.banners J (fun n=> ((M n) i)⁻¹))).flawing)).add (snowy (effectiveP h hx V s k (.inr i)))
    · exact ((Frill.still (-Λ.low.direct)).times (hx.pores i|>.flawing)).add ((driftK h hx V s k i).add (fringeC h hx s i))
    exact snowy (h.higherN hx i t)
open Raw Polar
lemma ridge (i:LogLetter c f): Frill J j p (fun n y=> Polar.nest (T n) s (U n y) (V n) (K n).kin i) (fun n y=> Polar.nest (T' n) s (U n y) (V n) (H n).kin i):=by
    have hb:Frill J j p (fun n _=> -Raw.orientation*(K n).beta) (fun n _=> -Raw.orientation*(H n).beta):= (Frill.still _).times (Frill.bare h.beta)
    rcases i with i|i|i|i|i|i
    · exact (Frill.bare (h.price i V)).neg
    · exact hb.times (Frill.bare (stare (letter («t»:=2) i.2.2) _ _ _ Λ.p (h.up.2.2.1 i.2.2) _))
    · exact hb.times (Frill.bare (stare (letter («t»:=3) i.2.2) _ _ _ Λ.p (h.up.2.2.2 i.2.2) _))
    · exact (Frill.still (-Raw.orientation)).times (Frill.bare (stare (letter («t»:=1) i.2.2) _ _ _ Λ.p (h.up.2.1 i.2.2) _))
    · exact hb.times (Frill.bare (h.up.tears Λ.high (fun n=>pull i.1 0 (V n)) _ _ t 1 Λ.p.threshold))
    exact hb.neg.times (h.down.paired (hx.turn i.1) _ _ _ _)
end Finish
end YM.ConnectedActivityE6.Lim
