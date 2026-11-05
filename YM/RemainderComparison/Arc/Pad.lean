import YM.RemainderComparison.Arc.Interior
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Reps

/-!
 # Multiple stencil/period budgets. At arbitrary robust x (not necessarily
 interior P.V). Estimates can be supplied per representation summand;
 `favor.trust` etc charge the inflated actual weight (use UG.Body).
 Exact low marker & vacuum re-expression using `shape` stencils still
 requires its translation/period/indicator proofs. These lemmas can be
 used on an actual comparison after that step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Arc
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {j w u Y : ℕ} {P:BudgetPoint} {A p R b x : ℝ}
variable {v : Positions (Uniform.Primary c G)}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
local notation "F₀" => (fun x=> Pressure.fiery G x L)

structure Deduct (G : Gauge) (P : BudgetPoint) (β : ℝ) (Y : ℕ) (r : ℝ):Prop where
  uses : ∀ (c f:Side),2* Y<c.val→∀ w:ℕ,w+1 ≤ Y →∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors Y o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), Arc.route G β s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖ ≤ r
lemma Deduct.enlarge (h : Deduct G P b Y R) (hp : R ≤ p) : Deduct G P b Y p:= -- edit
  ⟨fun c f ht w hw u o V hv=> by obtain ⟨i,y,hi,hy⟩:= h.uses c f ht w hw u o V hv; exact ⟨i,y,hi,hy.trans hp⟩⟩

lemma threshold (Y:ℝ→ℕ) (h: Reserve G L (fun x=>(Y x:ℝ))) :
    ∃ r:ℝ→ℝ, Reserve G L r ∧ ∀ᶠ x in atTop, ∀ (P:BudgetPoint) (β:ℝ),inBand (betaF G x L) β → P.threshold ≤2*Pressure.fiery G x L → Deduct G P β (Y x) (r x) := by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let p x:=16*(2*(Y x:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ); let f x:= p x*(2*Pressure.fiery G x L)
  have hp : Reserve G L p:= Reserve.mul (Reserve.mul (Reserve.const _) (((Reserve.mul (Reserve.const _) h).add (Reserve.const _)).pow 5)) (Reserve.const _)
  let r t:= A*p t*2*2*Delay.fineMonitor G L t
  have hf : Rate G L (-(1/2)) f:= by
    simpa only [zero_add] using! hp.rate.mul ((Rate.flame (G:=G) (L:=L)).mul_left 2)
  refine ⟨r,Reserve.mul (Reserve.mul (Reserve.mul (Reserve.mul (Reserve.const _) hp) (Reserve.const _)) (Reserve.const _)) Reserve.monitoring,?_⟩
  filter_upwards [hf.below (by norm_num) d hd,Delay.shift_pos G L] with x hf hx P β hβ hs
  have hr :0≤ f x:= by have hh := P.threshold_pos.trans_le hs; unfold f p; positivity
  refine ⟨fun c g hv w hp u o V he=>?_⟩
  have hj (y:Site c) (hy:separation o y≤Y x) (p : PlaqAxes): toll V (y,p) ≤ P.threshold:= by by_contra! hf; exact Finset.disjoint_left.mp he ((neighbors_mem ..).2 hy) ((flags_spec ..).mpr ⟨(y,p),WilsonStartup.anchor_visit _,hf⟩)
  obtain ⟨a,ha⟩:= Work.E08.axial_patch o V w (Y x) hp hv (2*Pressure.fiery G x L) (P.threshold_pos.trans_le hs).le (fun y hy p=> (hj y hy p).trans hs)
  · let z (i:Site g):= a (Slide.sites (Slide.cognac u) o i); let g':=Slide.shape (Slide.cognac u) o V
    let W:= gauge z g'; have he i:G.chord (W i) ≤ f x:= by
      unfold W g'; rw [show gauge z (Slide.shape (Slide.cognac u) o V)=_ from (Slide.shape_gauge (Slide.cognac u) o a V).symm]; unfold Slide.shape; split; exact ha _ (Slide.village ..)
      split; next h'=> rw [G.chord_inv]; exact ha _ (Slide.village ..)
      simpa [Gauge.chord] using hr
    obtain ⟨b,hb,hQ⟩:= H (fun _=> (0:Site c)) 0 0 W (f x) hr ((le_abs_self _).trans hf) (fun i _=>he i)
    let t:= (Uniform.tint G _).symm b
    let y:=gStep β; have hz:0 < y:= (Fare.gS _ (Access.lane_pos hx hβ)).1
    refine ⟨z,y⁻¹ • t,?_, ?_⟩
    · unfold Arc.route; rw [smul_smul,show gStep β*y⁻¹=1 from mul_inv_cancel₀ hz.ne',one_smul]; unfold Boulevard.actual; rw [show Uniform.tint G _ t=b from ContinuousLinearEquiv.apply_symm_apply ..]; exact funext fun i=> (hQ i (by simp)).symm
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hz).le,inv_mul_le_iff₀ hz]; apply le_trans ((Uniform.tint_inv_le _).trans hb)
    let q:= Delay.fineMonitor G L x; have hq:0 ≤ q:= (Delay.monitor_pos G L x).le; have ht:0≤ p x:= by unfold p; positivity
    have hh: gStep (betaF G x L) ≤ 2 * y:= by have h: gStep (betaF G x L)/2≤y:=(band_gap _ β hx hβ).1; linarith only [h]
    change A * (p x * (2*((gStep (betaF G x L))*q))) ≤ y*(A*p x* 2*2*q)
    apply le_trans (b:=A * (p x * (2*((2*y)*q)))) _ (le_of_eq (by ring)); gcongr

lemma regular {g:Config G f→E} {p:2*w≤f.val} {F:BudgetPoint} (o:Site c) (hw: w+1 ≤ Y) (hf : F.Regular univ g):
    F.Regular (neighbors Y o) (g ∘ Slide.shape (Slide.cognac p) o) := by
  let U := cognac p; let K := neighbors Y o; have hV i: sites U o i∈K:=(neighbors_mem ..).2 (le_trans (Slide.village ..) (Nat.le_of_lt hw))
  have hs y (hy: Healthy F.threshold K y): Local.Chart F.order (g ∘ shape U o) y := by
    have hh := hf.smooth (shape U o y) (by unfold Healthy; rw [Slide.allFlag U o y K hV F.threshold F.threshold_pos.le hy]; simp)
    apply Push.Local.chart_comp (k:=F.order) (x:=(0:Directions G c)) (W:=fun v=> shape U o (increment y v)) ?_ (Slide.modeling U o y); rw [Work.G07.at_zero_increment]; exact hh
  have he :Continuous (shape (K:=G.El) U o):= continuous_pi fun i=> by unfold shape; split_ifs<;> fun_prop
  refine ⟨fun x y hi=> congr_arg g (stable U o K hV x y hi), hf.borel.comp he.measurable, fun z V=> ?_, hs,fun V hu c l hl=> Next.Foundations.left_has c hl (hs V hu)⟩
  simp only [Function.comp_apply]; rw [shape_gauge,hf.symmetry]

omit [MeasurableSpace E] in
lemma vetted {g:Config G f→E} (o:Site c) {q:ℝ} (A:Track f) (W:Config G c) (a:Site f→G.El)
    (he:∀ i,separation o (sites A o i)≤ Y) (hp: Push.Local.Chart P.order g (shape A o W)) (h : Push.Local.Chart P.order (g ∘ shape A o) W)
    (hy: GaugeInvariant g) (hu: Push.Local.Chart P.order g (gauge a (shape A o W)))
    (hq: ∀ i:List (Directions G f),i.length≤ P.order→ (∀ v∈i, ‖v‖ ≤ P.threshold) → ‖leftDerivs g i (gauge a (shape A o W))‖ ≤ q)
    (l : List (Directions G c)) (hB:l.length ≤ P.order) (hf:∀ v∈l,P.dirBound o v) :
    ‖leftDerivs (g∘shape A o) l W‖ ≤ Trio.tilt P Y*q:= by
  obtain ⟨L,hL,hT⟩:= exists_dual_vector'' ℝ (leftDerivs (g∘shape A o) l W)
  let g':=L ∘ g
  let U:= shape A o W; let t:=gauge a U
  have hh (l) (hp:l.length ≤ P.order) (he:∀ i∈l,‖i‖≤P.threshold): ‖leftDerivs g' l t‖≤ q:= by
    rw [show leftDerivs g' l t= L _ from Push.Local.left_linear L l hu hp]
    exact (L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hL |>.trans (hq _ hp he))
  have ht: GaugeInvariant g':= fun a V=> congr_arg L (hy a V)
  have hV : Local.Chart P.order g' U:= L.contDiff.contDiffAt.comp 0 (f:=g ∘ increment U) hp
  have hb : ‖leftDerivs (g' ∘ shape A o) l W‖ ≤ Trio.tilt P Y*q:= Slide.stalled A o g' he l W hB hf hV (Slide.bills a ht hh)
  change ‖leftDerivs (L ∘ (g ∘ shape A o)) l W‖ ≤ _ at hb; rw [Push.Local.left_linear L l h hB, (show L _ = ‖leftDerivs (g∘shape A o) l W‖ from hT),show ‖(‖leftDerivs (g∘shape A o) l W‖:ℝ)‖=_ from Real.norm_of_nonneg (norm_nonneg _)] at hb; exact hb

/-- Support bridge to aligned output budget.
    Use separate summations after orientation averaging over V pull. -/
lemma deductive (hx:2*Y < c.val) (hp : Tracer P G b R) (ha : Deduct G P b Y R)
    {k':2*w≤f.val} (o:Site c) (g : Config G f→E) (hw : w+1 ≤ Y) (hRu : P.Regular univ g)
    (hr:1 ≤ R) (hA:0 ≤ A)
    (hZ : ∀ v:Positions (Uniform.Primary f G), ‖v‖ ≤ R → Arc.route G b v ∈ Boulevard.sunny P → Brush P.order A 1 (g ∘ Arc.route G b) v) :
    P.supBounds o (neighbors Y o) (g ∘ shape (cognac k') o) (Trio.tilt P Y* budgetizer P.order R A) := by
  refine ⟨by unfold Trio.tilt budgetizer Boulevard.ticket; positivity, fun V hu l hl hF=>?_⟩
  obtain ⟨u,X,hU,hR⟩:= ha.uses c f hx w hw k' o V hu
  let Z:= shape (cognac k') o V
  have h i := (village (c:=c) (o:=o) (C:=f) k' i) -- args edit
  have hz : flags P.threshold Z=∅:= Slide.allFlag (cognac k') o V (neighbors Y o) (fun i=> neighbors_mem ..|>.2 ((h i).trans (Nat.le_of_lt hw))) P.threshold P.threshold_pos.le hu
  have ht : flags P.threshold (Arc.route G b X)=∅:= by rw [hU, gauge_flags,hz]
  have he x (hx: flags P.threshold x=∅): Local.Chart P.order g x:= hRu.smooth x (by unfold Healthy; rw [hx]; simp)
  have hh := Tracer.uses hp g X hR ht (fun v _ hx=> he _ hx) hZ
  rw [hU] at ht hh
  exact vetted o (cognac k') V u (fun i=> (h i).trans (Nat.le_of_lt hw)) (he _ hz) ((regular (p:=k') o hw hRu).smooth V hu) hRu.symmetry (he _ ht) hh l hl hF
end YM.RemainderComparison.Arc
