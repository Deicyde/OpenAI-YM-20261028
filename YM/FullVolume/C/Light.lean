import YM.FullVolume.C.Clockers
/-! Staging the literal gaze. Must not depend on what trajectory point *called* the supplier (except incoming data themselves). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable (P : Match.Alliance H I 1 0) (hz:P.units=Equiv.refl _)
variable (hp:R.path=R'.path) (he:R.activities.reg=R'.activities.reg) (hk:R.activities.forced=R'.activities.forced)
lemma cover_frame {J: Cash W p a L₀ X o U T R'} (γ:ℝ) : plusone I (Match.staple (J:=I) rfl rfl rfl) χ γ=plusone I (Match.staple (J:=J) rfl rfl rfl) χ γ:=rfl
include hp he hk
lemma spinLike (d:ℕ) : Meadow.panel H d=Meadow.panel I d:=by
  ext i
  let V:= Match.staple (H:=H) (J:=I) hp he hk
  rw [Meadow.petaled,Meadow.petaled,flyer V rfl hp he hk]; exact (migrate V rfl hp he hk d (pennant H i).2).2
lemma glitter (b:BudgetPoint) (p) : Meadow.garnerAt H b p=Meadow.garnerAt I b p:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,p,B,T₁⟩:=R'
  cases hp; cases he; cases hk; rfl
include P hz
lemma headship {I':Cash W p a L₀ X o U T R'} (b:BudgetPoint) (γ:ℝ) (n:ℕ) (g:Site c): Trio.earned b P γ n g=Trio.earned b (Match.staple (H:=I') (J:=I') rfl rfl rfl) γ n g:=by
  unfold Trio.earned
  simp_rw [show plusone H P Chi.canonical γ= _ from (upward (I':=I') Chi.canonical P hz hp he hk _).trans (Eq.symm <| cover_frame (I:=I') (J:=I) γ), Meadow.signage (I:=I') hp he hk b, glitter (I:=I') hp he hk b,spinLike (I:=I') hp he hk n]
lemma summits {w : ℕ} {Y: Slide.Stars→Side} (h : ∀ i:Slide.Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa:∀ i:Slide.Stars,Trio.Offer G (Y i)) {I':Cash W p a L₀ X o U T R'} (b:BudgetPoint) (γ:ℝ) (n:ℕ) : Trio.insight b P γ n h z fa=Trio.insight b (Match.staple (H:=I') (J:=I') rfl rfl rfl) γ n h z fa := by
  ext i V
  have he':=headship (I':=I') P hz hp he hk b γ n i
  unfold Trio.insight; rw [he',Meadow.aster (H:=I) Chi.canonical b P hp (Match.same_area hp he hk) hz, glitter (I:=I') hp he hk, spinLike (I:=I') hp he hk,Meadow.aster (H:=I') Chi.canonical b (Match.staple (H:=I') (J:=I') rfl rfl rfl) rfl rfl rfl] -- function at i depends
  rw [show plusone H P Chi.canonical γ= _ from (upward (I':=I') Chi.canonical P hz hp he hk _).trans (Eq.symm <| cover_frame (I:=I') (J:=I) γ)]
end YM.PhysicalNext.Repeat.Meadow
