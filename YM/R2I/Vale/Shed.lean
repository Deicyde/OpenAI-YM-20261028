import YM.R2I.Vale.Oaths
import YM.RG12.Burst.Cotton
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Stove
/- Stage scheduling of alias panorama before products. Need *vol* aperture & post width
 pre momentum projection, not from mere Egg.s curvature. These transfer requests include
 only PURE for derivative estimates; pair with Starter Movement. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof.Vale
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
variable {G : Gauge} (L:Side) {P:Teller G} (Q : ConnectedActivityE6.Target G P) {μ η : ℝ}
variable (U:RG.Stage) (j:ℕ)
def tiny (G:Gauge) (L: Side)(j:ℕ)(t:ℝ):= betaF G t L ^ (-(j:ℝ))
def shiny (G:Gauge)(L:Side)(j:ℕ)(t:ℝ):= betaF G t L ^ (-3/4*(j:ℝ))
def donate (μ t:ℝ) :=
    let d:= grow G L t; let δ:=tiny G L j t
    (((d^(3+4*j))⁻¹+ Real.exp (-(Q.mark L μ t)))* (d^3*heap G U (1/16)) ≤ δ) ∧
    Real.exp (-(U.width/4)* radiusB t)*(betaF G t L ^ (-(7/16):ℝ)) ≤ δ ∧
    δ ≤ gold G L t ∧ (away U*(δ+δ)+δ) ≤ gold G L t ∧ (away U*(δ+δ)+δ) ≤ shiny G L j t ∧ δE t ≤ 1
lemma toll (hμ : 0<μ) (hj:2≤j) : ∀ᶠ t in atTop, Vale.donate L Q U j μ t:= by
  let k:= 3+4*j; let u:ℝ:=3/8; let q x:= grow G L x; let B x:= betaF G x L; let e x:= Real.exp (-(Q.mark L μ x)); let w x:= Real.exp (-(U.width/4)*radiusB x); let δ t:=tiny G L j t
  have hK:Rate G L (-u*k) (fun x=> (q x^k)⁻¹) := by
    apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx
    unfold q grow; rw [neg_mul,Real.rpow_neg hx.le,Real.rpow_mul hx.le]; rw [Real.rpow_natCast]; -- adjust
  have he : Rate G L (-u*k) e:= by
    have h:= Mallow.infuso L 1 _ 1 (by positivity : 0 < μ/4) zero_lt_one (-u*k) (G:=G) -- syntax
    simpa only [Mallow.syrup,e,one_mul] using! h -- may rewrite reversed
  have hG: Rate G L (-(j:ℝ)) δ:= Rate.power
  have hv:(2:ℝ)≤ j:=by exact_mod_cast hj
  have hp : Rate G L (-(j:ℝ)) w:= by
    refine (Rate.cutoff (G:=G) (L:=L) (a:=- (j:ℝ)) (show 0<U.width/4 from div_pos U.width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_)
    rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=U.width_pos; linarith)
  let a x:= away U*(δ x+δ x)+δ x; have ha:Rate G L (-(j:ℝ)) a:= ((hG.add hG).mul_left _).add hG
  filter_upwards [( (hK.add he).mul (((Rate.power (G:=G) (L:=L) (a:=u)).pow 3).mul_right (heap G U (1/16)))) (-(j:ℝ)) (by unfold k u; push_cast; linarith only [hv]), (hp.mul (Rate.power (a:=-(7/16)))) _ (by linarith : -(j:ℝ)+(-(7/16)) < -(j:ℝ)),ha (-(23/20)) (by linarith only [hv]), ha _ (by linarith only [hv] : -(j:ℝ) < -3/4*j), (Work.E09.betaF_growth G L).eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with x hk hp ha hT hv' ht
  refine ⟨(le_abs_self _).trans hk,(le_abs_self _).trans hp,Real.rpow_le_rpow_of_exponent_le hv' (show _ ≤ _ from by linarith only [hv]),(le_abs_self _).trans ha,(le_abs_self _).trans hT,Real.rpow_le_one (by unfold Clock.gap; positivity) (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr ht)) (by norm_num)⟩

section pane
variable {X:Metals G} (D:Rolls X.p) {C : Targets X.p X.K} {Z : Expenses C}
    {u:Return.Wages} {v:ℕ→ℝ} (R : Register D Z u v) (J:PostCost D)
    {F:ℕ→ℕ→Postage} (S : Time.Scouts (F:=F)) {P:Protection D} (W : Delays P)
abbrev Tess (j:ℕ):=3+4*j
def invitation (D : Rolls X.p) (C : Targets X.p X.K) (j i:ℕ) (t:ℝ):ℝ:= Trio.paySideW (Tess j) G (D.L j) (C j i|>.halo) t
structure ReserveW : Prop where
  stay : Pane.Planks D R J (invitation D C) W (fun _ i=> (X.p.profile i).order)
  widths : AutumnW D Z S W
  purse j i : StepStages j i → 2≤j → ∀ t,W.betaEntry j≤t → Vale.donate (D.L j) (C j i) (X.p.profile i) j (R.μ j i) t
lemma edition (hp:∀ j i,StepStages j i→ (Z j i).wanting= -(7/16:ℝ)): ∃ V:Delays P,DelayLe W V ∧ ∀ U : Delays P,DelayLe V U → Vale.ReserveW D R J S U:= by
  obtain ⟨k,hM,hB⟩:= Pane.school D R J (invitation D C) (fun _ i=> (X.p.profile i).order) (fun j i hi=> le_trans (by decide : 2≤6) (X.p.profile i).order_ge) (fun j i h=>Trio.circlesW ..) W
  obtain ⟨V,hq,hv⟩:= Roof.ensuresW D Z S k hp
  obtain ⟨x,-,hs,hx⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j atTop (fun i x=> 2≤j → Vale.donate (D.L j) (C j i) (X.p.profile i) j (R.μ j i) x) (fun i he=> by
      by_cases hh:2≤j
      · filter_upwards [toll (D.L j) (C j i) (X.p.profile i) j ((R.consumes j i he).2.1) hh] with x hx
        exact fun _=> hx
      exact Eventually.of_forall fun x hp=> (hh hp).elim))
  let K:Delays P:= {V with betaEntry:=x}; have hK : DelayLe V K:= ⟨hs,le_rfl,le_rfl,le_rfl⟩
  exact ⟨K,hM.trans (hq.trans hK),fun U h=> ⟨hB _ (hq.trans (hK.trans h)),hv _ (hK.trans h),fun j i hi hs t ht=>hx j t ((h.beta _).trans ht) i hi hs⟩⟩
variable (A:Alloy X D){m n:ℕ}
lemma volumic (h : AutumnW D Z S A.delay) :
    let k:=(C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo
    let B:=radiusB (A.B.a.clock.hatBeta m); let e:=Trio.baseW (Tess (A.B.a.clock.J (m+1))) k B
    200*e < (A.B.a.S.side m n).val:= by
  intro k B e; let a:=A.B.a.clock.J (m+1); let H:= A.delay.growth a; let K:=A.B.a.clock.coverSize (m+1)
  have hp : 1≤B:= (A.B.a.budget m).B_pos; let k':= 100*Trio.maxFixedW (Tess a) k
  obtain ⟨h',hh⟩:= h.sizes _ _ (step_paid A.B.a m)
  have hj := Trio.roofW (Tess a) k B hp; have hv : 0< k':= by unfold k' Trio.maxFixedW Trio.baseW Trio.tentW; omega
  have hH := A.B.valid.volume m n
  apply lt_of_lt_of_le _ hH; change _ < A.delay.shells a*(1+B+K)^H; refine lt_of_le_of_lt (b:=k'*B) ?_ (lt_of_lt_of_le ?_ (Nat.mul_le_mul_right _ h')); swap
  · apply Nat.mul_lt_mul_of_pos_left _ hv
    exact lt_of_lt_of_le (b:=1+B+K) (by omega) (le_self_pow₀ (by omega) (by change 1≤ H at hh; omega))
  calc _ = 100*(2*Trio.baseW (Tess a) k B) := by unfold e; ring
       _ ≤ 100*(Trio.maxFixedW (Tess a) k*B) := Nat.mul_le_mul_left _ hj
       _ = _ := (mul_assoc ..).symm
end pane
end YM.PhysicalNext.Repeat.Roof.Vale
