import YM.FullVolume.E6.Yard
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
lemma springy (H₀: ∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin) (h:Finish J K H):∃ g,0<g∧Tendsto (fun i=> (K i).beta) (J:Filter ℕ) (𝓝 g) ∧ Tendsto (fun i=>(H i).beta) (J:Filter ℕ) (𝓝 g):=by
    obtain ⟨w,hW,H⟩:= h.beta
    exact ⟨w,(half_pos (zero_lt_one.trans (H₀ 0).laws.intake.height)).trans_le (ge_of_tendsto hW (Eventually.of_forall fun i=> (H₀ i).laws.intake.window.1)),hW,H⟩
lemma ticks (H₀: ∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin) (h:Finish J K H): Glints J (fun n=> (gStep (K n).beta)⁻¹) (fun n=> (gStep (H n).beta)⁻¹):= by
    obtain ⟨g,hg,hp,hr⟩:= springy H₀ h; unfold gStep; simp_rw [inv_inv]; exact ⟨_,hp.sqrt,hr.sqrt⟩
lemma mvec {ι κ:Type} [Fintype ι] {D Z:ℕ→ E→ Matrix κ ι ℝ}{F Gf:ℕ→ E→ι→ℝ}(h: Buds φ j p D Z)(he:∀ i,Frill φ j p (fun n y=> F n y i) (fun n y=>Gf n y i))(q):Frill φ j p (fun n y=> (D n y *ᵥ F n y) q) (fun n y=> (Z n y *ᵥ Gf n y) q):= Frill.buds Finset.univ (fun i _=> (h _ i).times (he i))
variable [FiniteDimensional ℝ E]
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(hQ: ∀ n,Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(he:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j v)(ht:∀ᶠ i in (J: Filter ℕ), Z.Viable (U i p))
include hz hQ he ht h
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
lemma teg (i:Tubular f G):Frill J j p (fun n y=> leanB (D n y) i) (fun n y=> leanB (D' n y) i):=by
    refine mvec ((plot h (scaleG he) Z).opp) (fun k=> ?_) i
    by_cases hh:(D 0 p).selected k.1.1 (spot S k.1.2)
    · let Q(n:ℕ)(y:E):= scale • strain (D n y) k.1.1 k.1.2 0; let P(n:ℕ)(y:E):= scale • strain (D' n y) k.1.1 k.1.2 0
      have ht: Frill J j p Q P:= (Frill.still _).fee (ponds hQ hz h he ht k.1 hh (Frill.still _))
      have h Z' V : stand (Vine.bar (Z.paints (Λ:=Λ) Z' V) 0) k=(scale • strain (Z.paints (Λ:=Λ) Z' V) k.1.1 k.1.2 0 : G.Color) k.2:=by unfold stand Vine.bar; rw [if_pos (show (Z.paints Z' V).selected _ _ from hh)]
      simp_rw [h]; exact pointed ht k.2
    have h Z' V : stand (Vine.bar (Z.paints (Λ:=Λ) Z' V) 0) k=0:=by unfold stand Vine.bar; rw [if_neg (show ¬ (Z.paints Z' V).selected _ _ from hh)]; rfl
    simp_rw [h]; exact Frill.still _
include H₀
lemma lightwell (i:Tubular f G):Frill J j p (fun n y=> well (D n y) i) (fun n y=> well (D' n y) i):= (mvec ((standbys H₀ hz h (scaleG he) ht).opp) (teg hQ hz h he ht) i).neg
lemma levied : Frill J j p (fun n y=> voltage (D n y)) (fun n y=> voltage (D' n y)):= Frill.stocks fun i=> aimed fun k=>lightwell H₀ hQ hz h he ht (i,k)
lemma harry (i:Tubular f G): Frill J j p (fun n y=> shimmer (D n y) (K n).beta i) (fun n y=> shimmer (D' n y) (H n).beta i):=
    ((Frill.bare (ticks H₀ h)).neg).fee ((mvec (plume h (scaleG he) Z) (lightwell H₀ hQ hz h he ht) i).add (teg hQ hz h he ht i))
end Draft
end YM.ConnectedActivityE6.Lim
