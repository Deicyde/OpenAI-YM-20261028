import YM.FullVolume.Sym.Purse
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
/-! In LAST Padding at real labels before bootstrap. Ovens.B lookup uses no history. -/
open Progress.DirectedRecipe Time Ovens Rack
variable {G:Gauge} {c:Side} {P:Pipes G c}(X:sun→Tap G c) (p: BudgetPoint){q b B:ℝ}
local notation "Z"=>drawer G c
lemma padded (h: Acquittal P.reg p (fun i=> (X i).regular) q b): Acquittal (drawer G c).reg p (fun i=>(widen P (X i)).regular) q b:=by
  constructor; intro w η hw; let K:= upE P; let f(i:sun):=(widen P (X i)).regular; change ∃ k, Quotes.anchored p _ k _ ∧ _
  obtain ⟨k,hk,hZ⟩:= h.stars _ _ hw
  refine ⟨stuff K k, fun i=> ?_,fun i=>?_⟩
  · refine transfer_budget (upE P) ?_ ?_ (hk i); · intro j; rw [reg_up,stuffed]
    intro j hj; rw [blank K k hj]; simp [BudgetPoint.mass]
  by_cases hi:i∈Set.range K; · obtain ⟨i,rfl⟩:= hi; have hh t: f t (K i)= (X t).regular i:= stuffed ..; rw [show (Z).reg (K i)=_ from reg_up _ _,stuffed]; change p.Regular _ (mix w f (K i)) ∧ p.supBounds _ _ (mix w f (K i)) _; simp_rw [mix_eval f (K i), hh]; rw [← mix_eval (fun i=>(X i).regular)]; exact hZ i
  change p.Regular _ (mix w f i) ∧ p.supBounds _ _ (mix w f i) _; have he t:f t i=0:= blank _ _ hi; simp_rw [mix_eval f i,he,mix_z,blank K k hi]; exact ⟨VerifiedReset.reg_const _,sup_le (VerifiedReset.sup_const 0) (le_of_eq abs_zero)⟩
lemma flown {M V:ℕ→Support c} (F:sun→ ℕ→ Config G c→ℝ)(A:ℕ↪ℕ)(hp:∀ i,M (A i)= V i) (h:league V p.B F b q B) : league M p.B (fun i=> stuff A (F i)) b q B:=by
  obtain ⟨f,hf,hX⟩:=h; refine ⟨stuff A f,fun i=>?_,fun i U=>?_⟩
  · refine transfer_budget A ?_ ?_ (hf i); · intro j; rw [hp,stuffed]
    intro j hj; rw [blank _ _ hj]; simp
  by_cases he: i∈ Set.range A; · obtain ⟨i,rfl⟩:=he; simp_rw [stuffed]; exact hX i U
  simp_rw [blank _ _ he]; exact (Scout.still (hX 0 U|>.ray) (0:ℝ)).enlarged ((norm_zero).le)
lemma employers {e w κ s:ℝ} (hp:1≤q) (hh:league (fun i=>(P.kernel i).support) p.B (fun i=>(X i).forced) (p.supportExponent+1) q e)(hl: league P.softer p.B (fun i=>(X i).logarithm) (p.supportExponent+1) q w)(hr:Payments.Rates p.B s e w κ): league (fun i=>(Ovens.Pipes.addr (folio G c) p i).support) p.B (fun i=>Pipes.solid (folio G c) p (widen P (X i))) p.supportExponent q s:= by
  refine venture _ (fun i=>widen P (X i)) hp (P:=p) ?_ ?_ hr
  · exact flown p _ (upK P) (fun i=> by change ((drawer G c).kernel _).support= _; rw [hard_up]; rfl) hh
  exact flown p _ _ (soft_up P) hl
end YM.PhysicalNext.Repeat.Jams
