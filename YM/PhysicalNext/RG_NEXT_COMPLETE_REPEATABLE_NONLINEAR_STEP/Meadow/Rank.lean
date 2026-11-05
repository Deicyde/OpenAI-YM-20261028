import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Urb
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Litho
/-!
 # Long Path tail via native leg tariff (σ branch doubled ratios).
  collect at NEXT exponent, even if smaller. BEFORE pushing to reflection.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {M k: ℕ} {σ C δ β θ γ : ℝ}
variable (p : BudgetPoint) (R:PathData G) (l:Clip)

def arc (i:Songbook c): ℕ:= i.elim (fun i=> i.2.length R) (Sum.elim (fun i=>(R.cubic i.2).length) (Sum.elim (fun i=>(R.quartic i.2).length) (fun i=>(R.loop i.2).length)))
lemma arc_receipt (θ:Seat c) (i:Rags): arc R (legs θ i)= Meadow.melody R i:= by cases i with|inl i=>rfl|inr i=> rcases i with i|i|i <;> rfl
-- weight exp(σ/4)
lemma arch_tail {X:Type} (A:X→ RegularAddress c) (p : BudgetPoint) {f:X→ℝ} (m : X→ ℕ)
   (hp : Quotes.early p A (fun i=> f i*Real.exp (σ*m i)) C) (hσ:0 ≤ σ) (he:∀ i,0 ≤ f i): Quotes.early p A (fun i=> if k≤ m i then f i else 0) (Real.exp (-σ*k)*C):= by
  intro x; refine budget_mono (budget_scale (Real.exp_nonneg _) (hp x)) (fun i=> ?_) fun i=>?_
  · split; next h=> dsimp only; split_ifs <;> first| exact mul_nonneg (he _) (Real.exp_nonneg _)| simp
    exact le_rfl
  split
  next h=>
    dsimp only; split
    next hv =>
      have hq : 1 ≤ Real.exp (-σ*k)*Real.exp (σ*m i):= by
        rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith only [mul_le_mul_of_nonneg_left (show (k:ℝ)≤ m i from (by exact_mod_cast hv)) hσ]
      calc
        _ ≤ (f i*Real.exp (preExponent p * coverNumber p.B (A i).support))*(Real.exp (-σ*k)*Real.exp (σ*m i)):= by apply le_mul_of_one_le_right (mul_nonneg (he i) (Real.exp_nonneg _)) hq
        _ = _ := by ring
    next hv => rw [zero_mul]; have hE:= he i; positivity
  rw [mul_zero]
lemma torque (A:ℕ→Atom G k) (h : SumBudget (fun i=> (A i).budget σ) C) (hs : 0<σ) (he: preExponent p/p.B ≤ σ/4) (β : ℝ) : Quotes.early p (pitch (n:=c) A) (fun i=> sine p A β i.2*Real.exp (σ/4*(A i.2).length))
    (anchoredFee (headline p) (octave k)*tenor G k p σ C β):= by
  apply enhanced; refine Quotes.channel_mass (p:=headline p) (fun i=> (A i).length) (fun i=> (A i).footprint (0:Site c)) (fun i=> sine p A β i * Real.exp (σ/4*(A i).length)) (σ:=σ/2) (fun i=> mul_nonneg (sine_pos p A _ _) (Real.exp_nonneg _)) ?_ (octave k) (by rw [div_div]; norm_num; exact he) fun i=> ?_
  swap
  · have hf:= Wages.traversed (A i) (0:Site c) p.B p.B_pos; change p.B* _ ≤ p.B*octave k+_; refine hf.trans ?_; unfold octave; nlinarith
  have hp := act_lp p A β hs h
  convert hp using 2 with i; rw [mul_assoc, ← Real.exp_add]; ring_nf
lemma lent (β γ : ℝ) (hx:R.Bounds l σ C δ) (hp : WilsonStartup.Decent l p) (he: preExponent p/p.B ≤ σ/4): ∃ f : Songbook c→ℝ, Quotes.early p (strings R p) (fun i=> f i*Real.exp (σ/4*arc R i)) (Song.octaveNeed G p l σ C δ β γ) ∧
    ∀ i,p.Regular (strings R p i|>.support) (sounding R l β γ i) ∧p.supBounds (strings R p i|>.site) (strings R p i|>.support) (sounding R l β γ i) (f i):= by
  let f:= Sum.elim (fun i:Tally c=> mezzo R l p (-γ) i.2) (Sum.elim (fun i:Stave (n:=c)=> sine p R.cubic (-β) i.2) (Sum.elim (fun i:Stave (n:=c)=> sine p R.quartic (-β) i.2) (fun i:Stave (n:=c)=> sine p R.loop (-1) i.2)))
  have hv : Quotes.early p (fun i:Tally c=>strings R p (.inl i)) (fun i=> mezzo R l p (-γ) i.2 * Real.exp (σ/4*i.2.length R))
      (anchoredFee (headline p) lowCount * host G l p σ C (-γ)):= by
    apply enhanced; refine Quotes.channel_mass (p:=headline p) (Low.length R) (fun i=> i.home R p (0:Site c)) (fun i:Low=> mezzo R l p (-γ) i * Real.exp (σ/4*i.length R)) (fun i=>mul_nonneg (mezzo_pos ..) (Real.exp_nonneg _)) (σ:=σ/2) ?_ lowCount (by rw [div_div]; norm_num; exact he) fun i=> low_geometry p R i _
    convert (Cost.scale (Cost.scale (low_budget G p R hx) (turnFee p*p.threshold^2) (mul_nonneg (turnFee_pos _).le (sq_nonneg _))) |VerifiedReset.factor*(-γ)| (abs_nonneg _)) using 2 with i
    rw [mul_assoc (Song.mezzo ..), ← Real.exp_add]; unfold mezzo; ring_nf
    rfl
  refine ⟨f,fun i=> Cost.sum (hv i) (Cost.sum (torque p _ hx.three hx.width he _ i) (Cost.sum (torque p _ hx.four hx.width he _ i) (torque p _ hx.two hx.width he _ i))), fun i=>?_⟩
  rcases i with i|i|i|i
  · exact tally_charge R l p i _ hp
  · exact pitch_charge p _ _ _ fun i=> (hx.invariant i).2.1
  · exact pitch_charge p _ _ _ fun i=> (hx.invariant i).2.2
  exact pitch_charge p _ _ _ fun i=> (hx.invariant i).1
end YM.PhysicalNext.Repeat.Meadow
