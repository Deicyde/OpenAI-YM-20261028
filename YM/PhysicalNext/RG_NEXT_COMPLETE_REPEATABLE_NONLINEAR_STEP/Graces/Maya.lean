import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Crowns
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Assure
/-!
 # Timeline allotments for regular.ScoreBand. Repr.Current alpha plus Extra cap for actual Bolts.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{s:Sheet G}{K:MapPrices} {v w : ℝ}{Q:Targets s K} {Z:Expenses Q}{l:ℕ→ℝ}{V: Return.Wages}
variable (C:Programs s)(M:Rolls s)(E:ℕ→ℕ→Record) (k:ℕ→ℕ→ℕ)(r:Register M Z V l)

structure PostB (j i d : ℕ) (x: ℝ):Prop where
    heat : (tuition (Q j i) (M.L j) x (s.profile i).order (s.profile i).power ≤ winG G (s.profile i) d (M.L j)) ∧
      (∃ t:ℝ,0 ≤ t∧Real.exp (Heir.Release.base ((s.profile i).supportExponent+2) (k j i))*t≤winG G (s.profile i) d (M.L j)/2∧
        PermitY (Q j i) (C j i) (E j i) (s.profile i).power (V j i) (r.o j i) Chi.canonical (r.μ j i) x t (M.L j))
    funds (P B:BudgetPoint) : P.power=(s.profile i).power→B.threshold=fiery G x (M.L j) →
      ∀ β:ℝ,betaF G x (M.L j)/2≤ β→ Rented d (C j i) (E j i) P B (M.L j) (k j i) x (gStep β)
    fromWide : ∀ (P B:BudgetPoint),P.power=(s.profile i).power→B.threshold=fiery G x (M.L j)→
      ∀ β:ℝ,betaF G x (M.L j)/2 ≤ β → Lute.Plented (C j i) (E j i) P B (M.L j) (k j i) x (gStep β)
variable {Θ:Protection M} {j i d₀:ℕ}
abbrev Cruise (T: Delays Θ) := ∀ j x,T.betaEntry j≤x →∀ i d, s.first≤ i→ goodD s j i d→ PostB C M E k r j i d x
lemma bends (h: (E j i).ε ≤ 1/4) : ∀ᶠ x in atTop, PostB C M E k r j i d₀ x:=by
  let P:= Q j i; let L:=M.L j; let n:=(s.profile i).order; let p:=(s.profile i).power; let t:= k j i; let D:=E j i; have hc:2≤n:= (by norm_num : 2≤6).trans (s.profile i).order_ge
  let a:=(s.profile i).supportExponent; let A:= Real.exp (Heir.Release.base (a+2) t)
  have ht:A>0:= Real.exp_pos _; let u:=winG G (s.profile i) d₀ L; have hu:0 < u:=Graces.stirs ..
  obtain ⟨f,hF,hV⟩:= Mercury.tuned P p (C j i) D (V j i) (r.μ j i) (r.o j i) Chi.canonical L hc h -- edit
  filter_upwards [(hF.mul_left A).below (by norm_num) _ (half_pos hu), hV,(tutored (L:=L) P (-(1:ℝ)) n p).below (by norm_num) u hu, Peak.floats d₀ (C j i) D L t p (by omega), Heir.plents (C j i) D L t p (by omega)] with x hq hY hr hp ht'
  rw [abs_mul,abs_of_pos ht] at hq
  refine ⟨⟨(le_abs_self _).trans hr, |f x|,abs_nonneg _,hq,?_⟩,fun P B he hz β hu=> (hp _ hu).2 _ _ hz he,fun P B he hz β hu=> (ht' _ hu).2 _ _ hz he⟩
  intro c f' S T hk R e H F X i hx hh hχ hu J hK hb hP Y I _ _ a q b z hz hy he' hA M hM L' hL hL' j U hj hu' hn
  exact (hY c f' S T hk R e H F X i hx hh hχ hu J hK hb hP Y I a q b z hz hy he' hA M hM L' hL hL' j U hj hu' hn).climb (mul_le_mul_of_nonneg_left (le_abs_self _) M.profit) le_rfl
lemma reacts (T: Delays Θ) (he:∀ j i,StepStages j i→s.first ≤ i→ (E j i).ε≤1/4) :∃ U: Delays Θ,DelayLe T U ∧ ∀ V:Delays Θ,DelayLe U V→ Cruise C M E k r V:=by
  let Q j i x:= ∀ d:ℕ,s.first≤ i→ goodD s j i d→ PostB C M E k r j i d x
  have h j i (hi:StepStages j i):∀ᶠ x in atTop,Q j i x:=by
     by_cases h:s.first≤ i
     swap; · unfold Q; simp [h]
     filter_upwards [(Finset.range j).eventually_all.mpr (fun d _=> bends C M E k r (d₀:=d) (he _ _ hi h))] with x hx; intro d _ hv; exact hx d (Finset.mem_range.mpr (by have H:=hv.2.2.2; omega))
  obtain ⟨x,-,hx,hF⟩:= collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i=>h j i))
  exact ⟨{T with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩, fun U hu j x hx i d hp he=>hF j x ((hu.beta j).trans hx) _ he.1 d hp he⟩
end YM.PhysicalNext.Repeat.Graces
