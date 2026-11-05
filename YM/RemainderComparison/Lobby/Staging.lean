import YM.RemainderComparison.Lobby.Gown

/-!
# Consumer of ALL real & AUX clauses once. Leaves for Binaries.
 Works even when shrink-by-t merge applied later; not claiming identification
 of Φ. Iterable gas & Books residual with absolute sums before quotient.
 Scalar and kinetic not erased. Persistent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lobby
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open Progress.DirectedRecipe
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {ι β I J J':Type} {α:Type*} {c f:Side} [DecidableEq β] {Jm:Marker.Census β} {Y: Stars→Side}
variable (O:Manor G c ι α I) (T:Manor G c ι α J) (P:BudgetPoint) (root:ι→ Support c) (A : Set I) (Z:Set ι)
variable (W : Flues.Yard ι α G c) (p:ℕ) (a:α)(z:ι→Marker.Poly Jm)
open Mosaic Serif Manor Flues
local notation "Dʼ" => mural O T A
variable {r w k d m:ℕ} {v v' σ η γ D₁ D₂ u u' e e' L K' p' q b:ℝ} {ϕ : β→ℝ}
local notation "Pʼ" => (A⊕J)
set_option quotPrecheck false
variable (s:Finset (A⊕J))(B:Basis (mural O T A) s r)(Q:∀ i:Stars,(Y i).val=2*(w+i.val))(fa:α→∀ i:Stars,Offer G (Y i))
local notation "Xʼ" => (mansion Q fa k : Manor G c ι α (Site c))
variable {Ω:Set (A⊕J)} (X:Quarry (mural O T A) Ω J' root r)(hg:2*w≤f.val)(g:α→J'→ Config G f→ℝ)(l:J'→ℝ)
local notation "Sʼ" => walls Dʼ X
local notation "Sˮ" => ((((s : Finset (A ⊕ J)):Set (A⊕J))∪walls Dʼ X):Set (A⊕J))
local notation "Kʼ"=> vessel Dʼ X hg g l d
local notation "Vˮ" => blooming Dʼ P X hg g l d
local notation "Vʼ" => ranging Dʼ P s B Q fa k d
local notation "Lʼ" => Vesuvius.Assembles Vʼ Vˮ
variable (F : (Site c⊕J') ↪ ℕ)
local notation "Pˮ"=> Vesuvius.spring Lʼ F
variable (q' : ℕ≃ (Flues.fireplace W (Vesuvius.spring (Vesuvius.Assembles (ranging (mural O T A) P s B Q fa k d) (blooming (mural O T A) P X hg g l d)) F)).Pellet)
local notation "Wʼ" => Flues.flash W Pˮ P Z q'
variable (h₀:P.B>0) -- unused
variable (hz: Expulsion (mural O T A) s P B Q d k fa (σ+1) u)
variable (h: Nimble (mural O T A) X P (vessel (mural O T A) X hg g l d) (Manor.zephyr (mural O T A) X P hg g l d) (σ+1) u')
variable (hW: W.Pays Z p P.B (σ+1) q)(hw : W.Sounds P root)(hp:Flues.Resonant P.B p u q u' σ b η p' γ)
variable (hQ:∀ i,0 < Mosaic.Verse.load Z (X.sign i))
include hz h hp hW hw hQ
lemma campaigns : (Vesuvius.Assembles (ranging (mural O T A) P s B Q fa k d) (blooming (mural O T A) P X hg g l d)).Works P root Z (σ+1) u u' ∧ Yard.Sounds Wʼ P root∧ Yard.Pays Wʼ Z p P.B σ b:=by
   obtain he := Lobby.throne Dʼ P k Z s B Q fa X hg g l hz h hQ
   obtain ⟨hh,hK⟩:= Lobby.berth Dʼ P k Z s B Q fa X hg g l F (p:=p) hz h hQ
   exact ⟨he,Flues.flash_sound W Pˮ P root Z q' hw hh,Flues.corner W Pˮ P Z p q' hp hW hK⟩

variable [Fintype β] (V: Config G c)
variable (hA : O.Templary A root P σ v) (hT:T.Templary Set.univ root P σ v')
variable (hS: ∀ i∈s,(mural O T A).marks i=0)(hX:  (walls (mural O T A) X)⊆ (s:Set (A⊕J))ᶜ)
variable (hk: Manor.Spinal (vessel (mural O T A) X hg g l d) Set.univ root P σ K') (hZ: Chorus Jm ϕ Z z p)
local notation "scalar" => ((Complex.ofReal (∑ x:Site c,(mural O T A).sector a s B x 1)) • (1:Marker.Poly Jm))
local notation "Rʼ" => ((Xʼ).basin P Set.univ Z z a V+(Kʼ).basin P Set.univ Z z a V+(mural O T A).basin P (((s:Set (A⊕J))∪walls Dʼ X)ᶜ) Z z a V)
open GridRenewal.Rain
-- Eta.Conv and full Compose.P. invoked even if many α. storable for every.
include hS hX hA hT hk hZ
set_option maxHeartbeats 500000 in
lemma wrap : Summable ((Wʼ).gala P Z z a V) ∧
    cyclone (O.basin P A Z z a V) * (∑' i,W.gala P Z z a V i) =
     cyclone (T.basin P Set.univ Z z a V + scalar + Rʼ) * ∑' i,(Wʼ).gala P Z z a V i:=by
    have hs := hp.exponent
    have hT':= standing' P a Z z T V hT hs hZ
    have hv := Lobby.unionAt O T P A a Z z V (standing a V Z z hA hZ hs) hT'
    have hh : Templary Dʼ Set.univ root P σ (v+v'):= by
       apply Templary.skim (Lobby.sumAnch (Lobby.peel O A) (signed T) P Set.univ Set.univ (Lobby.templarySign T P Set.univ hT) (templaryPeel O P A hA (fun i _=>i.prop))) ?_ le_rfl le_rfl
       intro i _; cases i<;> simp [switch]
    have he:=Lobby.once Dʼ P k a Z z s B Q fa V X hg g l F hz h hQ (add_nonneg hs zero_le_one) hX hS hZ (standing' P a Z z Dʼ V hh hs hZ) (standing' P a Z z Kʼ V hk.templary hs hZ)
    obtain ⟨hG,hG'⟩:= Lobby.berth Dʼ P k Z s B Q fa X hg g l F (p:=p) hz h hQ
    obtain ⟨-, -, -, -,hK⟩:= Flues.gale W Pˮ P root Z q' a V z hZ hw hG hW hG' hp
    refine ⟨hK.summable,?_⟩; rw [hv,he,hK.tsum_eq,Univ P a Z z,Univ P a Z z,Univ P a Z z]; simp only [plus]; ac_rfl
end YM.RemainderComparison.Lobby
