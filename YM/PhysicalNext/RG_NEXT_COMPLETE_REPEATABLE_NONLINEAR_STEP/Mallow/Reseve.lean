import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Cruise
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-! # Evolution of the marked *same* output. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Daisy Daisy.Charity Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Averaging Geo Precision Extra.Iteration
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{n : Side}
    {X:Pipes G n} {D:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
variable {W : ℝ → Code G n}
namespace final
variable (h:Season (X.pours D) P W o r B (P.supportExponent+1)) (hp:Vapor X D P w) (he:Payments.Rates P.B A B w κ)
def frigid (X:Pipes G n)(D : Tap G n) (W : ℝ→ Code G n)(P : BudgetPoint)(t:ℝ): Code G n:=solid (folio G n) P (widen X (spice D (W t)))
local notation "R" => fused (folio G n) P (widen X D)
include h hp
include he in
lemma slopes : Season (fused (folio G n) P (widen X D)) P (frigid X D W P) o r A P.supportExponent := harvest (widening h) (shown hp) he (folio G n)
lemma slant (t : ℝ)(ht : |t| * r≤ 1)(U: Config G n): (black (R) (frigid X D W P t)).gas P U= (black (X.pours D) (W t)).gas P U* Real.exp (∑' i,D.logarithm i U):= (winters h hp (folio G n) t ht U).tsum_eq
end final
lemma cruise_EX (W : PathData G) (C : Clip) (P:BudgetPoint) (V:Config G n) (X:Pipes G n)(d:Tap G n)(β v:ℝ): (finish W C P X d β v).exponent V= (trunk W C P X d β v).exponent V:= by
  change v* _-W.inChannels _ _ _ _ - ((drawer G n).pours (widen X d)).additive P V=v*_ -_ -_
  rw [(Rack.preserves ..).same_sum]; rfl

variable {p : BudgetPoint}{P' : Stage}{s C Λ : ℝ} {Y: PathData G}{q : Clip} {Z : Listing G n}{V: Collection.Source G n} {H E α: ℝ}
    (g:G.Simple) (h : Collection.Local Z p V H E) (hx:Y.Bounds q s C Λ)(hw:Geo.Width p q s)(ht:WilsonStartup.Decent q p)
include g h hx hw ht
lemma cools (hn:20<n.val) : Vapor (Collection.shelves Z Y p) (Collection.branch Z Y q p V α) p (softNeed G p q s C α H):= by
  let Δ := Averaging.delta (Z.read V)
  have hp := h.fittings g hx ht hn α Δ
  refine ⟨hp.looks,fun i U hu=> by by_contra hh; exact hp.visits _ _ hh hu,hp.steady,hp.reads,?_⟩
  obtain ⟨u,he,hu⟩:= h.cheap
  have hF:= Local.quote_family hx ht hw α Δ he hu (delta_bound g h.projects); have hK (i : ℕ):= Local.quote_soft (R:=Y) (c:=q) g α Δ he h.smooth (numbering _ i)
  exact ⟨_,⟨fun i=> (norm_nonneg _).trans (hK i 1),fun i=> Cost.equiv (numbering _) (hF.2 i)⟩, hK⟩
end YM.PhysicalNext.Repeat.Mallow
