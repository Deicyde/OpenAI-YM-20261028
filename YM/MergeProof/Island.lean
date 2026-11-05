import YM.MergeProof.Seaside
import YM.PhysicalNext.SERVICE.Mixer

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Service
open ThroughLaunch Function Filter WilsonStartup Set Pressure Work.F05 AnalyticBridge.VerifiedReset
open RG Wilson Precision Lattice RG.Shoot RG.Supply Matrix Further.StrongStartup Next.Scheduling
open Next.Foundations
open Push.PriceCompiler UVNext.CouplingReset Time Org Progress.DirectedRecipe
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} (hG : G.Simple)
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D} {η g z : ℕ → ℝ}
    {E : ℕ → ℕ → Next.Scheduling.Exchange} {F J : PostList} {p : ResetPrices}
    {I f r b : RatioList} {L : ℕ→ℕ→ℝ→ℝ} {S : Scouts (F:=F)}
    {O T : MapPrices} {C : ℕ → ℝ}

variable {s : Sheet G} {t : Tariffs} {B : Extra.Multi.Scope} {v v' : ℕ→ℕ}
    {ℓ l : ℕ→ℝ} {w : Bid.Worth} {Z : Rolls (ThroughLaunch.raise s v')} {Θ : Protection Z} {W : Delays Θ}
    {P : PostCost Z} {Δ : Bar W} {Y : Wait Δ} {a : Levels G} {U : Horizon a} {k : Kin U (chart G)}

include hG
lemma depT (ha : Paid Y a) (hL : Torrent O T ℓ P a U k)
     (hx : Further.StrongStartup.Prices (ThroughLaunch.raise s v') t (Next.Foundations.localSection G) W.betaEntry)
     (hW : Stock.Priced W)
     (hP : Opened W P S) (hw : ∀ j i, StepStages j i → P.g j ≤ (F j i).rate/4 ∧
        credit G (s.profile i) ≤ p.cost j i/4)
     (hi : Inherited W I J L) (hc : ∀ j x,W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate Z p j i x)
     (hr : PricedReset a η p) (hf : Pressure.Testing.Ringing (bearing s T) f W)
     (h : Next.SectorChange.Cosmos (chart G) (bearing s T) W f r b) (E : ℕ→ℕ→Next.Scheduling.Exchange) :
      let D := Progress.DirectedRecipe.prepared k E F (permissions a) ha hL.finalMap (chart_ok _) hL.paths
      let A : Alloy (ThroughLaunch.currency s T v') Z := ⟨P,Θ,W,Δ,Y,hW,D⟩
      Mixing A E p I J L S η f r b := by
  intro D A
  obtain ⟨X,Y,u₀,hR,hS,hE,hK,hV,hD,hN,hi₀,hr₀,ht,hH,-⟩ := hL.layer
  refine ⟨⟨rfl,hP,hw,hc,hr,hf,h⟩,hi, origins hL.top (fun N=> (spending hG ha hx N).1.old),fun N m n hm=>?_⟩
  change Bid.Sworn (U.H N m) n G
  rw [hH.other N m hm]; exact hD _ _ _ hm.le
end YM.PhysicalNext.Service
