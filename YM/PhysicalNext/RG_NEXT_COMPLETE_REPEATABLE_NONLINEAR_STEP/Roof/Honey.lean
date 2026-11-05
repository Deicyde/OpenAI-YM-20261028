import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Porch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Headwind
/-!
 # Cabinet of purchases, continuation sold WHEN further histories ask bigger clocks.
 program ℓ optional. First-level θ. Keep all Auxiliary Posts available with Π.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} {C : Targets X.p X.K} {Z :Expenses C} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {p:Return.Wages} {v:ℕ→ℝ} (R : Register D Z p v) {P : Protection D} {u : Delays P} {i j m n N:ℕ}
abbrev invitation (D:Rolls X.p) (b:Targets X.p X.K) (j i:ℕ) (t:ℝ):ℝ:= Trio.paySide G (D.L j) (b j i|>.halo) t
structure WorksIn (A : PostCost D) (W : Delays P) (S : Time.Scouts (F:=F)):Prop where
  chip : (Pollened D R W)
  year : Yearling.Acre R W
  terms : Autumn D Z S W
  plaza : Pane.Planks D R A (invitation D C) W (fun _ i=> (X.p.profile i).order)
lemma honey (A : PostCost D) (V: Delays P) (S : Time.Scouts (F:=F)) (hp:∀ j i,StepStages j i→ (Z j i).wanting= -(7/16:ℝ)) (he : Yearling.Hood X.p X.K C X.p.floorL):∃ U : Delays P,DelayLe V U ∧∀ T:Delays P,DelayLe U T→ WorksIn R A T S:= by
  obtain ⟨X',hh,hH⟩:= Boulevard.emits D R (fun j i h=> (hp _ _ h).le) V
  obtain ⟨Y,hy,hY⟩:= Yearling.brine R he (fun j=> (D.large j).need) X'
  obtain ⟨W,hW,H⟩:= Roof.ensures D Z S Y hp
  obtain ⟨V,hv,hP⟩:= Pane.school D R A (invitation D C) (fun _ i=> (X.p.profile i).order) (fun j i hi=> le_trans (by decide : 2≤6) (X.p.profile i).order_ge) (fun j i h=>Trio.circles ..) W
  exact ⟨V,hh.trans (hy.trans (hW.trans hv)),fun V h=>⟨hH _ (hy.trans (hW.trans (hv.trans h))),hY _ (hW.trans (hv.trans h)),H _ (hv.trans h), hP _ h⟩⟩
-- numeric post on real orientation
variable (A : Alloy X D)
lemma volumic (h : Autumn D Z S A.delay) :
    let k:=(C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo
    let B:=radiusB (A.B.a.clock.hatBeta m); let e:=Trio.base k B
    2*e < (A.B.a.S.side m n).val ∧ 4*(Meadow.studio k B)+16≤ (A.B.a.S.side m n).val:= by
  intro k B e
  let H:= (A.delay.growth (A.B.a.clock.J (m+1))); let s:= (A.B.a.clock.coverSize (m+1)); let a:=A.B.a.clock.J (m+1)
  have hp : 1≤B:= (A.B.a.budget m).B_pos
  obtain ⟨h',hh⟩:= h.sizes _ _ (step_paid A.B.a m)
  have hj := Trio.roof k B hp; have hv : 0< Trio.maxFixed k:= by unfold Trio.maxFixed Trio.base Trio.tent; omega
  have hH := A.B.valid.volume m n
  have ht:2*e < (A.B.a.S.side m n).val:=by
    change 2*Trio.base k B<_
    apply lt_of_lt_of_le _ hH; change _ < A.delay.shells a*(1+B+s)^H; apply lt_of_le_of_lt hj; refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_right _ h'); apply Nat.mul_lt_mul_of_pos_left _ hv
    exact lt_of_lt_of_le (b:=1+B+s) (by omega) (le_self_pow₀ (by omega) (by change 1≤ H at hh; omega))
  exact ⟨ht,(by unfold e Trio.base Trio.tent at ht; omega)⟩
end YM.PhysicalNext.Repeat.Roof
