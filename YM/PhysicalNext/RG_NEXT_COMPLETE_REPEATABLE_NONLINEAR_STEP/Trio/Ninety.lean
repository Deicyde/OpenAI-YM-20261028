import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Alto
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Reps
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
/-!
 # Epoch payments BEFORE levels. stocks rotated. post width programme.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (G : Gauge) (L:Side) (t:ℝ) (b:ℕ) (σ:RG.Stage) (x:ℝ)
local notation "B" => radiusB x
local notation "h" => (gold G L x)
local notation "c" => fence b (radiusB x)
local notation "s" => Height.away σ
local notation "z" => (base b B)
-- dues old Local.loose E-turn already included

def heat := ((ballCost (Meadow.studio b B)):ℝ)*(s*((betaF G x L)^t+ betaF G x L ^ (-(7/16):ℝ)))
def stout (P:RG.Stage):= P.supportExponent+3
def lossFee:= heat G L t b σ x+heat G L t b σ x+ ∑ i:Stars, |Slide.ray i| * ((Fintype.card (Site (c i)):ℝ)*(heat G L t b σ x+heat G L t b σ x))
def crestFeat (i:Stars):= (ticket σ.order h+2*((Fintype.card (Site (c i)):ℝ)*(s*(h+h)+h)))
def planks := ∑ i:Stars, |Slide.ray i| * ((2:ℝ)^σ.order*((1+(z:ℝ))^(σ.power*σ.order))*crestFeat G L b σ x i)
def coverTicket (b:ℕ) : ℝ := (((2*maxFixed b+1)^4:ℕ):ℝ)

lemma loses (p : BudgetPoint) (ht:p.order=σ.order) (hp:p.power=σ.power): tilt p z=(2:ℝ)^σ.order*((1+(z:ℝ))^(σ.power*σ.order))∧
    Trio.oroW p z (crestFeat G L b σ x)=planks G L b σ x:= by simp only [tilt, ht,hp,oroW,planks]; trivial -- edit orientation

-- rate bundles
lemma sparks {t : ℝ} {f:Stars→ℝ→ℝ} (hp:∀ i, Rate G L t (f i)): Rate G L t fun x=>∑ i:Stars,f i x := by
  simp_rw [Stars,Fin.sum_univ_succ,Finset.univ_eq_empty (α:=Fin 0),sum_empty, add_zero]
  repeat' first | exact hp _| apply Rate.add
lemma feeStars (i:Stars): Rate G L 0 (fun x=> (Fintype.card (Site (Trio.fence b (radiusB x) i)):ℝ)) := by
  have he:= (rows G L b).2.1
  let F x := (tent b (radiusB x):ℝ)
  let g x:=2*(F x+i.val)
  have hg:Bolt G L g:= (Bolt.still 2).times (he.joins (Bolt.still _))
  refine Rate.congr (Bolt.uses (hg.nod 4)) ?_; filter_upwards with x; rw [site_card]; symm; change (g x)^4= ((↑((2*(tent b (radiusB x)+i.val))^4:ℕ)):ℝ); unfold g F; norm_cast -- edit
lemma balls {f:ℝ→ℕ} (H : Bolt G L fun x=>(f x:ℝ)): Rate G L 0 (fun x=>(ballCost (f x):ℝ)) := by unfold ballCost; push_cast; exact (Bolt.nod ((H.joins H).joins (Bolt.still 1)) _).uses
lemma heats (ht:t=-(7/16:ℝ)): Rate G L t (heat G L t b σ):= by
  subst t; exact (balls G L ((rows G L b).1)).mul (((Rate.power).add Rate.power).mul_left _) |>.weaken (by rw [zero_add])
lemma twigs (ht:t=-(7/16:ℝ)): Rate G L t (lossFee G L t b σ):= by
  have hx:= Trio.heats G L t b σ ht; let hh:= hx.add hx; refine Rate.add hh (sparks G L fun i=> ?_); simpa only [zero_add] using! (((feeStars G L b i).mul hh).mul_left |Slide.ray i|)
lemma frost (i:Stars): Rate G L (-(23/20)) (fun x=> crestFeat G L b σ x i):= by
  have ht : Rate G L (-(23/20)) (gold G L):= Rate.power; apply Rate.add ((ht.mul_left _).mul_right _); simpa only [zero_add] using! (((feeStars G L b i).mul (((ht.add ht).mul_left _).add ht)).mul_left 2)
lemma skyward : Rate G L (-(23/20)) (fun x=> planks G L b σ x):= by
  have hb := (rows G L b).2.2.1
  apply sparks G L (f:=fun i x=> |Slide.ray i| * (_) ); intro i
  simpa only [zero_add] using! ((((Bolt.still ((2:ℝ)^σ.order)).times (((Bolt.still 1).joins hb).nod (σ.power*σ.order))).uses.mul (Trio.frost G L b σ i)).mul_left |Slide.ray i|)
-- whole transformation compare/h endpoints. q costs at any θ
lemma cheap (ht:t=-(7/16:ℝ)): ∀ᶠ x in atTop,Marlin.tithe (2*base b (radiusB x)) (lossFee G L t b σ x) ⟨σ.power,σ.order, σ.supportExponent,1,1,σ.power_ge,σ.order_ge,σ.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicket b) ≤ betaF G x L ^(-(1/8):ℝ):= by
  have ht' := ((balls G L ((rows G L b).2.2.2)).mul (twigs G L t b σ ht)).mul_right (Real.exp ((σ.supportExponent+1+1)*coverTicket b)) (-(1/8):ℝ) (by rw [ht]; norm_num)
  filter_upwards [ht'] with x hv; exact (le_abs_self _).trans hv
end YM.PhysicalNext.Repeat.Trio
