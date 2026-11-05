import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Postcards
/-!
 # Numeric solvency. Add a dependent occurrence coin at AUTHENTIC height, measure separate.
 Doesn't perturb R. Leaves explicit ASK schedule even on support larger.C
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill  Eider   Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}

section
variable (Q : YM.ConnectedActivityE6.Target G P)
-- wants projected cover inequality reserve

def foam (L : Side) := Q.relative*(10*Footprint.preCost (Q.halo+5)/L.val) ≤ Q.ε
def ribbon (L : Side) (x : ℝ):ℝ := Q.goal L x * Real.exp (Q.relative*Footprint.preCost (Q.halo+5))
def sailUp (L : Side)(x:ℝ):ℝ:= (betaF G x L)^(Q.rate/2)
def swing (L : Side)(μ β x C:ℝ) : Mixed.Costs:= {Q.costs L μ β x C with
    optionalHit := Q.goal L x+ribbon Q L x
    q:= sailUp Q L x
    rootHit:=(Q.costs L μ β x C).rootHit+ribbon Q L x }
lemma early : ∃ n:ℕ, ∀ L:Side,n≤L.val→ foam Q L:=by
  obtain ⟨n,hn⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const Q.usable|>.eventually_ge_atTop (Q.relative *(10*Footprint.preCost (Q.halo+5))))
  refine ⟨n,fun L hl=>?_⟩; unfold foam; rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2
  rw [mul_comm Q.ε]; exact hn L.val hl
lemma sailsW (L:Side) (h : 0<μ) : ∀ᶠ x in atTop, ∀ (β C:ℝ), (Q.costs L μ β x C).Buy L Q.halo (radiusB x) → (swing Q L μ β x C).Buy L Q.halo (radiusB x):=by
  let v x:=(swing Q L μ 0 x 0).rootHit; have hv : Rate G L Q.rate v:= (Q.rate_root (β:=0) (C:=0) L h).add (Rate.power.mul_right _)
  have he:=Q.stop; let g(x:ℝ):= Trees.degreePrice (radiusB x) (v x) Q.δ
  have hp:Rate G L Q.rate g:=by
    unfold g Trees.degreePrice Trees.stretch; have hx:=width_rate G L 1 0; simp only [one_mul,add_zero] at hx
    simp_rw [div_eq_mul_inv]; simpa only [zero_add] using! (((hx.mul hv).mul_right _).mul_left _)
  filter_upwards [Delay.shift_pos G L,hp (Q.rate/2) (by linarith), Rate.power.below (G:=G) (L:=L) (show Q.rate/2<0 by linarith) _ (by norm_num : (0:ℝ)<1/2)] with x hx hG hF β C hQ
  have hh:0<ribbon Q L x:=by unfold ribbon ConnectedActivityE6.Target.goal; positivity
  exact { hQ with
    γ:=hQ.γ.trans_le (le_add_of_nonneg_right hh.le)
    combined:=le_trans (le_of_eq (add_assoc ..|>.symm)) (add_le_add_left hQ.combined _)
    trees:=(le_abs_self (g x)).trans hG
    grows:=((le_abs_self (sailUp Q L x)).trans hF).trans_lt (by norm_num)} -- defeq
end
-- same H data.
section mask
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
local notation "cR" => coverNumber R.p.B M.crest
local notation "B" => radiusB x
-- main vs partner. Beauty support reserve captured

def jewel (M:Leaf R)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(x:ℝ) := Q.goal L x*Real.exp (-(R.p.supportExponent-Q.ε)*(coverNumber R.p.B M.crest))
def jewelDebt (M:Leaf R)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(x:ℝ):ℝ:= R.p.mass M.crest M.weight * Real.exp (-Q.ε*(coverNumber R.p.B M.crest)) / Q.goal L x

def sparkling (c f:Side): Wing→ ConnectedActivityE6.Alphabet c f
    | .logKey i=> .inr (.inl (.inl (.inl i)))
    | .gasKey i=> .inl i
lemma sparkPath (i : Wing) (S: StepData c f): Sum.inr (sparkling c f i)= i.badge S:=by cases i <;> rfl
lemma sparkHead : H.birth (sparkling c f M.turn) = enlargement S.ratio Q.halo B (RG.inspected M.crest):=(by simpa only [← sparkPath M.turn S] using! M.turn.badge_area R T Q.halo B)
lemma sparkExp : ConnectedActivityE6.lengths T R (sparkling c f M.turn) = coverNumber R.p.B M.crest:=by unfold Leaf.crest; generalize M.turn=y; cases y <;> rfl

include H
lemma arable : 0<Q.goal L x:=by
  apply Real.rpow_pos_of_pos; have he:= H.laws.intake.height; rw [H.laws.data.funds.length_eq] at he; linarith
lemma dew : 0<jewel M Q L x ∧ 0 ≤ jewelDebt M Q L x ∧ M.weight=jewelDebt M Q L x*jewel M Q L x:=by
  have h:=arable H; refine ⟨mul_pos h (Real.exp_pos _),div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le M.profit) (Real.exp_pos _).le) h.le,?_⟩
  unfold jewelDebt jewel BudgetPoint.mass; field_simp; rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel,Real.exp_zero,mul_one]
variable (hf:foam Q L)(hs:R.p.B≤2*(radiusB x))
-- update `accounts` independent of inflated Stamp proof. T.B.H
omit H in
def colly {n : Side} (w : ConnectedActivityE6.Alphabet n f → ℝ) (M : Leaf R)
    (Q : YM.ConnectedActivityE6.Target G P)(L:Side)(x:ℝ): ConnectedActivityE6.Alphabet n f → ℝ:=fun i=> if i=sparkling n f M.turn then jewel M Q L x else w i -- c unused
include hf hs
lemma sustains : Ac.Hit H.birth B (Reserves.tariff (colly (n:=c) (fun _=>0) M Q L x) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (ribbon Q L x):=by
  intro y
  let i:=sparkling c f M.turn
  let v j:= if y∈H.birth j then Reserves.tariff (colly (n:=c) (fun _=>0) M Q L x) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε j * Real.exp (Q.relative*coverNumber B (H.birth j)) else 0
  change SumBudget v _; have hM:= (dew M H).1
  have h j (hj:j≠i):v j=0:=by simp [v,Reserves.tariff,colly,hj,show sparkling c f M.turn=i from rfl]
  refine ⟨fun j=>?_,summable_of_ne_finset_zero (s:={i}) (f:=v) (fun j hj=>h j (by simpa using hj)),?_⟩
  · unfold v; split; next=>
      refine mul_nonneg ?_ (Real.exp_pos _).le; unfold Reserves.tariff
      exact mul_nonneg (by unfold colly; split; exact hM.le; exact le_rfl) (Real.exp_pos _).le
    next=> rfl
  rw [tsum_eq_single i h]; unfold v; split
  next hj=>
    let u:= Q.relative; have hb:0<B:= lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1
    have he' := footprint S.ratio (Q.halo+5) B R.p.B M.crest hb hs
    have he : u*coverNumber B (H.birth i) ≤ u*Footprint.preCost (Q.halo+5)+ Q.ε*cR:=by
      let s:= S.patch.L; have hv : coverNumber B (H.birth i)≤ coverNumber _ _:= cover_mono (sparkHead M H|>.symm ▸ (Footprint.inspected_price S.ratio Q.halo _ M.crest hb)) B
      have hh : 0 ≤ u:=by unfold u ConnectedActivityE6.Target.relative; linarith [Q.usable,Q.bound,Q.pos]
      refine (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hv).trans he') hh).trans ?_
      have hx : u*Footprint.conversion S.ratio (Q.halo+5)≤ Q.ε :=by unfold Footprint.conversion; rw [show S.ratio.count=L from H.laws.data.funds.length_eq]; exact hf
      rw [mul_add u,← mul_assoc u _ _] -- focus
      gcongr
    unfold Reserves.tariff colly; rw [if_pos rfl, add_zero, show ConnectedActivityE6.lengths T R i= (cR:ℝ) from sparkExp (T:=T) M]
    unfold jewel ribbon; simp_rw [mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (arable H).le
    apply Real.exp_monotone; have ht : 4*Q.ε < R.p.supportExponent:= H.laws.intake.exponent ▸ Q.grants.1
    unfold u at he
    nlinarith only [he,mul_le_mul_of_nonneg_right ht.le (show 0≤(cR:ℝ) by positivity)]
  next=> exact mul_nonneg (arable H).le (Real.exp_pos _).le

lemma coco (F:ConnectedActivityE6.Alphabet c f→ℝ)(G: Pressure.Stores S→ℝ)
    (e : ℝ) (hp:Accounts S Q.halo B (Q.costs L μ R.beta x e) H.birth F (ConnectedActivityE6.lengths T R) G): Accounts S Q.halo B (swing Q L μ R.beta x e) H.birth (colly F M Q L x) (ConnectedActivityE6.lengths T R) G:=by
  have hh i: 0≤ colly F M Q L x i:=by unfold colly; split; exact (dew M H).1.le; exact hp.holds i
  refine ⟨hp.packetBound,hh,hp.extra,?_⟩
  intro y; refine budget_mono (budget_plus (hp.pays y) (sustains M H hf hs y)) ?_ ?_
  · intro i; split_ifs; exact mul_nonneg (mul_nonneg (hh _) (Real.exp_pos _).le) (Real.exp_pos _).le; rfl
  intro i
  have he : (swing Q L μ R.beta x e).head= Q.relative:=rfl
  have ht : (Q.costs L μ R.beta x e).head= Q.relative:=rfl; rw [he,ht]; split_ifs
  · unfold Reserves.tariff colly; split
    next hz=> exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (hp.holds i) (Real.exp_pos _).le) (Real.exp_pos _).le)
    next hx=> simp [swing] -- if hx same
  simp
end mask
end YM.PhysicalNext.Repeat.Daisy
