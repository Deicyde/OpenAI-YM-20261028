import YM.FullVolume.E6.Stocks
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
open Polar
lemma canto {F:ℕ→ℝ}{b:ℝ}(h:∀ i,F i∈Icc 0 b): Frill (J:Filter ℕ) j p (fun i _=>F i) (fun i _=>F i):= Frill.bare (FullVolume.Shadow.sails isCompact_Icc (Eventually.of_forall h))
lemma harms (h:Finish J K H)(H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin): Frill J j p (fun n _=> Real.log (measure_g Q.table (K n).beta)) (fun n _=> Real.log (measure_g Q.table (H n).beta)):=by
   obtain ⟨g,hg,ha,hv⟩:=springy H₀ h
   let f(x:ℝ):= Real.log (measure_g Q.table x)
   have hh:ContinuousAt f g:=by
       apply ContinuousAt.log (f:=fun x=> measure_g Q.table x); unfold measure_g gStep; fun_prop (disch:=first | positivity)
       have he:= Q.table_exists.scale; unfold measure_g gStep; positivity
   exact Frill.bare ⟨_,hh.tendsto.comp ha,hh.tendsto.comp hv⟩
lemma hifi (χ:Chi)(b:ℝ)(V:ℕ→ Config G f)(he:Quincy J j p U U)(i:Bond c)(A:Stores S)(t k) : Frill J j p (fun n y=> Mask.noise A χ i t b (V n) k (U n y)) (fun n y=> Mask.noise A χ i t b (V n) k (U n y)):=by
    have hv:= ((he i).glowing (Strand.banners J (fun n=> ((S.prediction (V n) k i))⁻¹))).chordwise; let f(x:ℝ):=χ.read (x/(b*t)^2) -- order.W*b
    unfold Mask.noise Chi.innerShare Pressure.wire; simp_rw [div_pow]
    have ht:= hv.via (Q:=f) ((χ.smooth.of_le (show (j:WithTop ℕ∞)≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp (contDiff_id.div_const _))
    split; · exact (Frill.still _).sub ht
    exact ht
variable [FiniteDimensional ℝ E]
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(hQ: ∀ n,Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(he:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j v)(ht:∀ᶠ i in (J: Filter ℕ), Z.Viable (U i p))
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
local notation "R"=> radiusB Z.x
variable {w w':ℕ→ E→ Directions G f}{z z':ℕ→ E→ Air f G}
lemma mantle (hu:Frill J j p w w') (X:Finset (Bond f))(d:ℝ): Frill J j p (fun n y=> (D n y).enforce d (w n y) X) (fun n y=> (D' n y).enforce d (w' n y) X):= Frill.pears X (fun i _=> lamps (K:=K) (H:=H) (Z:=Z) (U:=U) i hu d)
include hQ he ht h hz
lemma portico (hu:Frill J j p w w')(s:Signed)(q:Spot c f) : Frill J j p (fun n y=> Vine.costs (D n y) (w n y) s q) (fun n y=>Vine.costs (D' n y) (w' n y) s q):=by
    refine Frill.buds (parents q) fun i hi=>?_ ; change Frill _ _ _ (fun n y=> pot (D n y) s i (w n y)) (fun n y=> pot (D' n y) s i (w' n y)); by_cases hh:(D 0 p).selected s (spot S i)
    · exact (snowy (ponds hQ hz h he ht (s,i) hh hu)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_pos (show (D n y).selected _ _ from hh)).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_pos (show (D' n y).selected _ _ from hh)).symm)
    exact (Frill.still (0:ℝ)).alter (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_neg (show ¬(D n y).selected _ _ from hh)).symm) (Eventually.of_forall fun n=> Eventually.of_forall fun y=> (if_neg (show ¬(D' n y).selected _ _ from hh)).symm)
lemma rootage (hu:Frill J j p w w')(V:ℕ→ Config G f)(s:Signed)(i)(b): Frill J j p (fun n y=> Polar.rootface (D n y) (w n y) (V n) b s i) (fun n y=> Polar.rootface (D' n y) (w' n y) (V n) b s i) := (h.manor ((scaleG he).turn s) (fun n=> pull s 0 (V n)) Z.x (Oriented.choice s Z.k) i b).sub (portico hQ hz h he ht hu s i)
include H₀
lemma flowing (hu:Frill J j p w w')(V:ℕ→ Config G f)(A:Stores S): Frill J j p (fun n y=> Polar.plumeLog (D n y) o.a (K n).kin Q.table (w n y) (V n) A) (fun n y=>Polar.plumeLog (D' n y) o.a (H n).kin Q.table (w' n y) (V n) A):=by
    let I:=A.dome (304*R); let L':= (D 0 p).plaza I
    have ha: Frill J j p (fun n y=> chalky (D n y) (w n y) (V n) A) (fun n y=> chalky (D' n y) (w' n y) (V n) A):= (Frill.still _).times (Frill.buds Finset.univ fun i _=> Frill.buds (posted (turnStore i A) (200*R)) fun j _=> rootage hQ hz h he ht hu V i j false)
    have hf: Frill J j p (fun n y=> crispy (D n y) A) (fun n y=>crispy (D' n y) A):= (Frill.still _).times (Frill.buds Finset.univ fun i _=> Frill.buds (posted (turnStore i A) (200*R)) fun j _=> portico hQ hz h he ht (levied H₀ hQ hz h he ht) i j)
    have hx:= harms (j:=j) (p:=p) h H₀; exact (((((Frill.bare h.beta).neg).times (ha.add hf)).add (Frill.buds (visit A (200*R)) fun i _=> charges H₀ hz h he ht i)).add (Frill.buds L' fun i _=> gears (H:=H) (U:=U) H₀ hz hu i)).sub ((Frill.still (((D 0 p).pens A).card:ℝ)).times hx)
end Draft
end YM.ConnectedActivityE6.Lim
