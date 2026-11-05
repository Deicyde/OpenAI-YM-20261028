import YM.FullVolume.Sym.Trace
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
/-! Compute prepaid costs of Patti.Nonlinear gather; now working with FINAL layout. Need both sup and family marks. -/
open FullVolume.Ray Residual Averaging Progress.DirectedRecipe Time Ovens
variable {G:Gauge}{c:Side}{p:BudgetPoint}{A:Listing G c} {R:PathData G}{b:Clip} {γ Δ C B H q v σ τ:ℝ}
variable {X:sun → Collection.Source G c}(g:G.Simple)
    (h:∀ t:sun,Meadow.Budget p A.reg (X t|>.logRead) C) (hp:sanction p A.reg (fun i=>(X i).logRead) q v)(hq:1≤q)
variable {Λ:ℝ}
    (he:R.Bounds b σ τ Λ) (hx: Geo.Width p b σ) (hd: WilsonStartup.Decent b p)
def petalsC (A: Listing G c) (R:PathData G)(b:Clip)(X:sun→ Collection.Source G c)(p:BudgetPoint)(γ:ℝ)(i:sun) := Collection.branch A R b p (X i) γ
set_option quotPrecheck false
local notation "E'"=> fun i:sun=> (petalsC A R b X p γ i).regular
local notation "L"=>fun i:sun=> (petalsC A R b X p γ i).logarithm
local notation "Z"=> shelves A R p
local notation "V'"=> regularNeed G p b σ τ γ v
local notation "U'"=> softNeed G p b σ τ γ v
-- final Sanction for Reg actual, with right exponent X.B. EBound p not preExponent
structure Acquittal (a:ℕ → RegularAddress c)(p:BudgetPoint)(E:sun→ℕ→ Config G c→ℝ)(q b:ℝ) : Prop where
    stars : ∀ w η,Stripe w q η→ ∃ f,Quotes.anchored p a f (η*b) ∧∀ i,p.Regular (a i).support (mix w E i) ∧ p.supBounds (a i).site (a i).support (mix w E i) (f i)
lemma inkable {ν y s:ℝ}(P':ℕ→RegularAddress c)(f:sun→ℕ → Config G c→ℝ) (h: Acquittal P' p f s ν)(he : ν ≤ y): Acquittal P' p f s y:= by
  constructor; intro w v hv; obtain ⟨g,hg,hP⟩:= h.stars w v hv; exact ⟨g,fun i=> budget_loosen (hg i) (mul_le_mul_of_nonneg_left he (stripe_pos hv)),hP⟩
section weight
variable (w:Rung)(η α : ℝ) (hw:Stripe w q η)
include h g hp hw
local notation "X₀"=> emitA w X
local notation "Δ'"=> fun i=>Averaging.delta (A.read (X i))
local notation "Y"=> Averaging.delta (A.read (emitA w X))
local notation "F₀"=> mix w (fun _=>γ)
local notation "f"=>fill A R b p X₀ F₀ Y
lemma reflected : p.threshold^2*|Y| ≤ η*v:= Averaging.delta_bound g (reproages _ (hp w η hw))
lemma tipped : ‖mix w Δ'‖ ≤ η*(v/p.threshold^2):= by
  rw [d_angle w g h,mul_div_assoc',Real.norm_eq_abs,le_div_iff₀ (sq_pos_of_pos p.threshold_pos)]; rw [mul_comm]; exact reflected g h hp w η hw
omit g h hp
include hw hq
lemma frame_pure : ‖F₀‖ ≤ η*|γ|:= (Scout.still hq γ).beam w η hw
variable  (hγ:|γ|≤α)
-- home actual α, Γ may > actual. ensures positive
include hγ hp g he hx hd
lemma weight_norm : regularNeed G p b σ τ F₀ (η*v) ≤ η*regularNeed G p b σ τ α v:= by
  have ht : |F₀|≤η*α:= (frame_pure hq w η hw).trans (mul_le_mul_of_nonneg_left hγ (stripe_pos hw)); have hA:= budget_pos p G b he.width (budget_nonneg he.three)
  have hT:=turnFee_pos p; have hy:=p.threshold_pos; unfold regularNeed; rw [abs_of_nonneg ((abs_nonneg γ).trans hγ)]; nlinarith only [mul_le_mul_of_nonneg_right ht (mul_nonneg (mul_nonneg hT.le hA.2.1) (pow_nonneg hy.le 3))]
lemma toll_norm : softNeed G p b σ τ F₀ (η*v) ≤ η*softNeed G p b σ τ α v:= by
  have ht : |F₀|≤η*α:= (frame_pure hq w η hw).trans (mul_le_mul_of_nonneg_left hγ (stripe_pos hw)); have hA:= budget_pos p G b he.width (budget_nonneg he.three)
  have hy:=p.threshold_pos; unfold softNeed
  have he : hitNeed p G F₀ (η*v) ≤ η*hitNeed p G α v:= by unfold hitNeed; rw [abs_of_nonneg ((abs_nonneg γ).trans hγ),mul_div_assoc η]; nlinarith only [mul_le_mul_of_nonneg_right ht hy.le]
  refine le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right he hA.2.2)) (le_of_eq ?_); unfold softReset Push.AbsoluteSums.Footprint.payment Footprint.degreeIncome; ring
end weight
section press
variable (α:ℝ)(hγ:|γ|≤α)
include hp h g hq he hx hd hγ
lemma passport : Acquittal (shelves A R p).reg p E' q (regularNeed G p b σ τ α v):= by
  constructor; intro w η hw; let X0 := emitA w X; let «Y»:= Averaging.delta (A.read X0); let F₀' := mix w (fun (_:sun)=> γ)
  obtain ⟨u,hU,hk⟩:= hp w η hw
  have he' i:p.supBounds (A.reg i).site (A.reg i).support (X0.logRead i) (u i):= (hk i).2
  have h' j:= (hk j).1
  have hf:= Collection.Local.quote_regular g he hd (v:=X0) F₀' «Y» he' h'
  have hZ:= (Collection.Local.quote_family he hd hx F₀' «Y» he' hU (reflected g h hp w η hw)).1
  rw [show mix w E'= _ from d_reg w g h]
  refine ⟨fun i=>Collection.quoteE _ _ _ F₀' «Y» u (numbering _ i),fun i=> Cost.equiv (numbering _) (Cost.enlarge (hZ i) (weight_norm (hp:=hp) g hq he hx hd w η _ hw hγ)),fun i=> ⟨?_,hf (numbering _ i)⟩⟩
  let N:=numbering (EKey c)
  change p.Regular (incoming A R p (N i)).support (archive A R b X0 F₀' «Y» (N i))
  rcases N i with i|⟨z,d⟩|⟨z,d⟩
  · exact rebate_regular _ (h' _)
  · exact z.regular (Low.fresh_regular R b d _ hd _)
  exact z.regular (High.fresh_regular R d _ he p _ _)
lemma tenderP : voted (fun i=> (petalsC A R b X p γ i).logarithm) (shelves A R p).softer p.B (p.supportExponent+1) q (softNeed G p b σ τ α v):=by
  intro w η hw; let X' := emitA w X; let d:= Averaging.delta (A.read X'); let u' := mix w (fun (_:sun)=> γ)
  obtain ⟨u,hU,hk⟩:= hp w η hw
  have he' i:p.supBounds (A.reg i).site (A.reg i).support (X'.logRead i) (u i):= (hk i).2
  have hZ:= (Collection.Local.quote_family he hd hx u' d he' hU (reflected g h hp w η hw)).2
  refine ⟨fun i=> Collection.quoteL R p b u' d u (numbering _ i),fun i=> Cost.equiv (numbering _) (Cost.enlarge (hZ i) (toll_norm (hp:=hp) g hq he hx hd w η _ hw hγ)),fun i U=> ?_⟩
  rw [← mix_eval (w:=w) _ U, ← mix_eval (w:=w) _ i, show mix w L= _ from d_soft w g h]; exact Collection.Local.quote_soft g _ _ he' (fun i=>(hk i).1) (numbering _ i) U
variable (hQ:2 ≤ q)
include hQ
lemma leg_on : league (shelves A R p).softer p.B L (p.supportExponent+1) (q/2) (2*softNeed G p b σ τ α v):=by
  have hz := unions (tenderP g h hp hq he hx hd α hγ) (Z).sites (by linarith) (add_pos p.exponent_pos zero_lt_one|>.le) (r:=q/2) (by linarith) (by linarith)
  rw [show (1-q/2/q)⁻¹=2 by field_simp; ring_nf] at hz; exact hz
-- cost k fee Rate paid with output choice W. use quoteHard. To repeat registers need distinguishing Cap vs Sanction.EX.
lemma costed {s t κ w : ℝ}(hh:league (fun i=> (A.hard i).support) p.B (fun i=> (X i).hardRead) (p.supportExponent+1) (q/2) s)(hb:2*softNeed G p b σ τ α v ≤ t)(hr:Payments.Rates p.B w s t κ)(N:ℕ≃Pipes.Pellet (shelves A R p)): league (fun i=> (Ovens.Pipes.addr N p i).support) p.B (fun i=> Pipes.solid N p (petalsC A R b X p γ i)) p.supportExponent (q/2) w := by
  let P' := shelves A R p; have hL:= leg_on g h hp hq he hx hd α hγ hQ
  obtain ⟨k,hk,hZ⟩:= hL; exact Jams.venture N (petalsC A R b X p γ) (by linarith) hh ⟨k,fun i=> budget_loosen (hk i) hb,hZ⟩ hr
end press
end YM.PhysicalNext.Repeat.Jams
