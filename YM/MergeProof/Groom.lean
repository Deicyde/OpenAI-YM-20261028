import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MergeProof.Revenue
import YM.MergeProof.Tray
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Novas

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
variable (R:Register D p u l) (Q:ℕ→ℕ)
def Rumor (Z:Delays Θ): Prop:= ∀ j x,Z.betaEntry j≤x→∀ i,StepStages j i→ Tariff (X j i) (D.L j) (Q j) (R.μ j i) x
structure Minty (Z: Delays Θ):Prop where
    hold : Pungent R Z
    word : Rumor R Q Z
lemma scarce (V : Delays Θ):∃ W:Delays Θ,DelayLe V W ∧ ∀ Y:Delays Θ,DelayLe W Y → Minty R Q Y:=by
    obtain ⟨T,h,hT⟩:= bravo R V
    let P j i x:= Tariff (X j i) (D.L j) (Q j) (R.μ j i) x
    obtain ⟨x,-,hx,H⟩:= collect_upper T.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> show ∀ᶠ x in atTop,P j i x from thaws _ _ _ _ (R.consumes _ _ hi).2.1) -- order args
    let W: Delays Θ:= {T with betaEntry:=x}; have ht: DelayLe T W:=⟨hx,le_rfl,le_rfl,le_rfl⟩; exact ⟨W,h.trans ht,fun Y hy=>⟨hT Y (ht.trans hy),fun j x hx i hi=> H j x ((hy.beta j).trans hx) i hi⟩⟩
end YM.PhysicalNext.Repeat.Mallow
