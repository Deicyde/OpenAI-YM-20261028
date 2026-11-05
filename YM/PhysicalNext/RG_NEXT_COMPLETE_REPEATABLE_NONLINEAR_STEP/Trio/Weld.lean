import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Mover
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Panel
/-! # Oars accounting; sewn analytic collection first. Consume when actual V Healthy
 (boundary ANY). -/
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
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F L:Side} {j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side} {q : ℝ}
section morph
variable {q q' : Stars→ℝ} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i))
lemma sup_S {ι:Type} (F:ι→ Config G c→ℝ) (p:ι→ℝ) (A:Finset ι) (X:Support c) (u:Site c) (h:∀ i∈ A,B.Regular X (F i)) (hp:∀ i∈ A,B.supBounds u X (F i) (p i)):B.supBounds u X (∑ i∈A,F i) (∑ i∈A,p i) := by
  refine ⟨sum_nonneg (fun i hi=> (hp i hi).1),fun V hu l hl ht=>?_⟩
  rw [Push.Local.left_sum _ _ _ _ (fun i hi=> (h i hi).smooth V hu) hl]; exact (norm_sum_le ..).trans (sum_le_sum fun i hi=> (hp i hi).2 V hu l hl ht)

abbrev froth {c : Side} (f:Offer G c) : Config G c →ℝ:= fun V => ∑ i : Site c, f i V
lemma orchard (x:Site c): Trio.ornament Q fa x=∑ j:Stars, ray j • ((Boulevard.stillA (Trio.froth (fa j))) ∘ Slide.shape (Trio.pad Q j) x):= by
  funext i; simp only [ornament, beacon,rip,unit,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,froth,Boulevard.stillA,sum_sub_distrib]
-- pay oath from prior erudition ON points very small.
def tilt (B:BudgetPoint) (b:ℕ) := 2^B.order*((1+(b:ℝ))^(B.power*B.order))
def oroW (B:BudgetPoint) (z:ℕ) (q : Stars→ℝ) := ∑ i : Stars, |Slide.ray i| *(tilt B z*q i)
variable (h : ∀ i j, B.Regular univ (fa i j)) (hq : ∀ i,0≤q i) (hp:w+4 ≤ z)
include h hp hq
lemma kinds (e a : ℝ) (x:Site c)
    (he:∀ V: Config G c, Healthy B.threshold (neighbors z x) V→ ∀ i, ∃ (u:Site (Y i)→G.El) (P:Positions (Uniform.Primary (Y i) G)), actual P= gauge u (Slide.shape (pad Q i) x V)∧ ‖P‖+2*e <a)
    (hM: ∀ i (P : Positions (Uniform.Primary (Y i) G)),flags B.threshold (actual P)=∅→ ‖P‖+2*e < a → ∀ l: List (Directions G (Y i)),l.length ≤B.order→ (∀ i∈l, ‖i‖≤ B.threshold)→ ‖leftDerivs (Boulevard.stillA (Trio.froth (fa i))) l (actual P)‖ ≤ q i) :
    B.supBounds x (neighbors z x) (Trio.ornament Q fa x) (oroW B z q):= by
  rw [orchard]; let p i:= Boulevard.stillA (Trio.froth (fa i))
  have hh i:B.Regular univ (p i):= by
    have hx : B.Regular univ (froth (fa i)):= by rw [show froth (fa i)=∑ j,fa i j from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=> h i j
    exact CouplingShape.reg_sub hx (CouplingShape.reg_const _)
  have hz i (j:Site (Y i)): separation x (Slide.sites (pad Q i) x j)≤z:= (Slide.village (C:=Y i) (w:=w+i.val) (Q i).ge _ _).trans (by have hk := i.isLt; omega)
  apply sup_S (B:=B) _ _ _ _ _ (fun i _=>CouplingShape.reg_scale _ (Slide.regular (pad Q i) x (hh i) fun j=> (neighbors_mem ..).2 (hz i j)))
  intro i _; apply CouplingShape.sup_scale _
  refine ⟨mul_nonneg (by unfold tilt; positivity) (hq i),fun V hu l hl hd=>?_⟩
  obtain ⟨u,P,hP,hR⟩:= he V hu i; let W:=Slide.shape (pad Q i) x V; have hK := Trio.hint Q z V i hp x hu
  apply Slide.stalled (pad Q i) x (p i) (hz i) l V hl hd ((hh i).smooth _ (by unfold Healthy; rw [hK]; simp))
  have hf:= hM i P (by rw [hP, gauge_flags,hK]) hR; rw [hP] at hf; exact Slide.bills u (hh i).symmetry hf
end morph
section flatten
lemma pledges (G: Gauge) (L: Side) (Y:ℝ→ℕ) (h: Rate G L 0 fun x=>(Y x:ℝ)): ∀ᶠ x in atTop, ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2* Y x<c.val→∀ w:ℕ,w+1≤Y x→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors (Y x) o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < eaves G L x:= by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let f x:= 16*(2*(Y x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have hv : Rate G L (-(1/2)) f:= by
    simpa only [f,zero_mul,zero_add] using! (((((h.mul_left 2|>.add (Rate.const 1)).pow 5).mul_left _).mul_right _).mul ((Rate.flame (G:=G) (L:=L)).mul_left 2))
  filter_upwards [hv.below (by norm_num) d hd, contraction G L (a:=1) (b:=1) zero_lt_one ((hv.mul_left A).add ((Sienna.belt G L|>.mul_left 2).weaken (by norm_num))) (show -(1/2:ℝ)<vow by norm_num [vow])] with x hv hK P hx c g h w hp u o V he
  have hf :0≤ f x:= by have hh := P.threshold_pos.trans_le hx; unfold f; positivity
  have hj (y:Site c) (hy:separation o y≤Y x) (p : PlaqAxes): toll V (y,p) ≤ P.threshold:= by by_contra! hv; exact Finset.disjoint_left.mp he ((neighbors_mem ..).2 hy) ((flags_spec ..).mpr ⟨(y,p),WilsonStartup.anchor_visit _,hv⟩)
  obtain ⟨a,ha⟩:= Work.E08.axial_patch o V w (Y x) hp h (2*Pressure.fiery G x L) (P.threshold_pos.trans_le hx).le (fun y hy p=> (hj y hy p).trans hx)
  · let z (i:Site g):= a (Slide.sites (Slide.cognac u) o i); let g':=Slide.shape (Slide.cognac u) o V
    let W:= gauge z g'; have he i:G.chord (W i) ≤ f x:= by
      unfold W g'; rw [show gauge z (Slide.shape (Slide.cognac u) o V)=_ from (Slide.shape_gauge (Slide.cognac u) o a V).symm]; unfold Slide.shape; split; exact ha _ (Slide.village ..)
      split; next h'=> rw [G.chord_inv]; exact ha _ (Slide.village ..)
      simpa [Gauge.chord] using hf
    obtain ⟨b,hb,hQ⟩:= H (fun _=> (0:Site c)) 0 0 W (f x) hf ((le_abs_self _).trans hv) (fun i _=>he i)
    refine ⟨z,(Uniform.tint G _).symm b,?_,lt_of_le_of_lt (add_le_add ((Uniform.tint_inv_le _).trans hb) le_rfl) (by simpa only [one_mul] using! hK)⟩
    unfold Boulevard.actual; rw [ContinuousLinearEquiv.apply_symm_apply]; exact funext fun i=> (hQ i (by simp)).symm
end flatten
end YM.PhysicalNext.Repeat.Trio
