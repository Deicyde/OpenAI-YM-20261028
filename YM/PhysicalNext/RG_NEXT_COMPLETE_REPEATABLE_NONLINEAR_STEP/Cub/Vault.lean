import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.Further.ROOTED_INTERACTING_REMAINDER.Pulse
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Letters
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Orientation
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Maya
import YM.Planned.PRIMARY_INTEGRAL_295.Colas
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-! # Summing projection crack only on icon. No direct Still.Graph.Summ recurrence. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Lattice RG Wilson Finset MeasureTheory Pressure Pressure.Tube Supply
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy Daisy.Charity Mallow Lotus
open Blush  Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open Blaze Blaze.March Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ}
open Pressure Push.SectorMeasure Greenbelt Refrain Labels
variable {S:StepData c f}{T: Tube G S}{L:Side}{P:Teller G} {Q: ConnectedActivityE6.Target G P}{W x μ C : ℝ}{o':Target.Order G W}{R:RG.Rep G f}
variable (H:Cash W x μ L Q o' C T R) (r : Cloud R) (o : Site c)
variable (K R' : ℝ → Code G c)(v: ℂ)(F : YM.Labels.Frame G j)
variable {B:BudgetPoint}{A b q t d Y f₀ α k β e w t':ℝ}{n' ℓ:ℕ}(N: Captain H n' q t d Y A b t' f₀ k ℓ Chi.canonical)
variable (hR : Herd H N.conduit A f₀ ℓ) (hF:foam Q L) (hz:Bikes Q L μ x α e f₀ n' ℓ)
    (hb:B.B=radiusB x)(hu:B.threshold=Pressure.temp x)(hk: B.order=n')(ha: B.supportExponent+2 ≤ α)
    (hp:Daisy.tailCost L Q μ x f₀ e n' ℓ B.power ≤ Daisy.poster Q L x) (h:o∈ r.live.crest.image S.ratio.parent)

section funds
set_option quotPrecheck false
local notation "s!" => scope H r o
local notation "M" => Blush.screen H r K R' v F
variable (h' : r.live.turn=.logKey i)
include hR hz hp hF hb ha h' hu hk h
lemma brimmed {τ:ℝ}{R2:Rep G c}(Z:Source.Hol G){T:Source.SectionData F}(ht:R2.p=B)(hf:(Blush.screen H r K R' v F).Format o (scope H r o) R2)(hB: Local.Readable Z T B c τ):
    let V := Brim.icon H i; let I:= enter H V; let y:= (M).row o (s!) Z B.threshold
    Summable y ∧ F.coeffSize (∑' j,if j=I then 0 else y j) ≤ Local.readPrice Z F*(‖v‖*(marvel (Q:=Q) (x:=x) (L:=L) r + marvel (Q:=Q) (x:=x) (L:=L) r)):=by
   intro V I g; let L' (j) := if j=I then (0:F.Coeff) else g j
   obtain ⟨he,hP⟩:=relish H r o v N hR hF hz hb hu hk ha hp h
   let C:=Local.readPrice Z F
   have hC:=Local.readPrice_pos Z F
   let Z' i:=tasty (B:=B) H r o v N i
   let A' (j : H.fragrances):= Local.reservedMass B (locus r.live H o j) (Z' j)
   let c₀:= ‖v‖*(marvel (Q:=Q) (x:=x) (L:=L) r+marvel (Q:=Q) (x:=x) (L:=L) r)
   have hz : SumBudget (stuff (enter H) A') c₀:= transfer_budget (enter H) (fun _=>stuffed ..) (fun i hi=> blank _ _ hi) he -- check stuffed
   have hs : SumBudget (fun i=> F.coeffSize (L' i)) (C*c₀):=by
      apply budget_mono (budget_scale (zero_le_one.trans hC) hz) (fun _=> Work.G08.size_nonneg ..)
      intro j; by_cases hq:j=I
      · rw [show L' j=0 from if_pos hq]; simpa only [Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero] using (budget_scale (zero_le_one.trans hC) hz).1 j
      unfold L'; rw [if_neg hq]
      have hU:B.Regular (s! j) ((M).bulk j):=ht ▸ hf.regular j
      by_cases hj:j∈Set.range (enter H)
      swap; · have h(e:BudgetPoint): e.Regular (s! j) ((M).bulk j)∧ e.supBounds o (s! j) ((M).bulk j) 0:=by change e.Regular _ (fields _ _ _ j)∧e.supBounds _ _ (fields _ _ _ j) 0; unfold fields; rw [blank _ _ hj]; exact regular0 ..
              have ht:=Local.weighted_bound Z F o hU hB.order hB.power ((h B).2); rw [blank _ _ hj]; exact ht
      obtain ⟨i,rfl⟩:=hj; have hv : i≠ V:=fun hi=> hq (hi ▸ rfl)
      have hN:= Mercury.grinch H r.live _ h'
      obtain ⟨hX,hV⟩:= he -- syntax.SumBudget
      let T0:=tasty (B:=B) H r o v N i
      have hp:= hP i (fun K=> hv (hN.2 _ K))
      have hn: scope H r o (enter H i)=locus r.live H o i:=(enter H).injective.extend_apply ..
      apply (Local.weighted_bound Z F o hU hB.order hB.power (show B.supBounds o _ ((M).bulk (enter H i)) T0 from ?_)).trans
      · rw [stuffed]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hp.1 (Real.one_le_exp (by positivity [B.exponent_pos]))) (zero_le_one.trans hC)
      change B.supBounds o _ (stuff (enter H) (pane H r v) (enter H i)) _; rw [stuffed,hn]; exact hp
   have hh:= (Size.series F hs.2.1).of_norm
   refine ⟨?_, (Size.bound F hs.2.1).trans hs.2.2⟩; have he : g= L' + fun i=> if i=I then g I else 0:= by ext i; by_cases hi:i=I <;> simp [*,L']
   rw [he]; exact hh.add (hasSum_ite_eq _ _).summable
end funds
end YM.PhysicalNext.Repeat.Cub
