import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.Fruit
import YM.MergeProof.Permit
import YM.MergeProof.Record
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.SectorNext.RECONNECTED_LOCALITY.Missing
import YM.SectorNext.RECONNECTED_LOCALITY.Weld

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0) {y' ex dk:ℝ}(h: Usable M Y χ A rA K dk ex y')
open MergeProof  Set GridApprox.Nil
variable (b':V→Site c)(hw:∀ i,GridApprox.Nil.Scoped (A:= {x| b' x∈ (M i).crest.image S.ratio.parent}) (z i)) (rV:V→ℝ)(hV:∀ i,0<rV i)(hx:∀ i, Poly.price rV (z i) ≤ 1) (ho:∀ i,(z i).part B.quiet=0)
open Menu
-- no duplic.
variable (N:ι→Menu.Hat B R) [Fintype V]
include hV
-- specific Projection parent .. also counts.La
variable {y:ℝ}
lemma bidding (o:V→Site f)(hp:Daisy.foam Q L)(ht:R.p.B≤2*radiusB x)(he:4 ≤ Q.relative)(hy:100 ≤ R.p.supportExponent)(h0:0 ≤ y) (hh:Menu.Offer o N rV R.p.B (R.p.supportExponent-4) y)(hV':Extra.Multi.Occupancy (S.ratio.parent ∘ o) m)(hZ:Palette.shipPrice L Q x m y):
    Palette.Plot (fun i=>(N i).M) Y (fun i=>Menu.sumFee (N i) rV):=by
   let A(i):=(N i).s.val
   have ha i v (hv:v∈A i): o v∈ (N i).M.crest:= hh.sites i (mem_image_of_mem o hv)
   apply Palette.deck (fun i=>(N i).M) Y (fun i=>Menu.sumFee (N i) rV) (fun i=>Menu.timed (N i) hV) o A hV' ?_ he hy hp ht h0 ?_ hZ
   · intro i _; obtain ⟨j,hj⟩:= (N i).shiny; exact ⟨j,hj,ha i j hj⟩
   intro v; refine Extra.Multi.Budget.mono (hh.budget (o v)) (fun _=> ?_) (fun i=> ?_) le_rfl
   · split
     next=> exact mul_nonneg (Real.exp_pos _).le (Menu.Crew rV hV)
     next=>rfl
   split
   next h=> rw [if_pos (ha _ _ h),mul_comm]; exact le_rfl
   next=> exact (hh.budget ..).1 _
end YM.Merge.Photo
