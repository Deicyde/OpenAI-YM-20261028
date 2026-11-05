import YM.RemainderComparison.Cadenza.Tempo
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadenza
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Funk Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {p:Patch} {L : Side} {K:KernelChoices} {j n r : ℕ}
variable {q o w : ℝ→ℝ}{W μ:ℝ} {A:ConnectedActivityE6.Target.Order G W}
open Ethereal Geo
namespace Tuba
open Ethereal Geo Time
variable (Q:ConnectedActivityE6.Target G P) (p:Patch)(r:Rays)(s:Songbook G p.L)(t:Scrollwork G p.L)(X:RG.Stage)(D:Quarry)
variable {e δ:ℝ} (hp:D.Financed G p.L e)(hd:0<D.d)(hZ:0<D.Z)
local notation "Πx"=> royale p r s t X D


def transit (δ x:ℝ):= (turnFee (Time.probe X))* ((1+|δ|)* incomingE G p.L x + Πx x*(Access.apron G p.L x)^3+Πx x*(Access.apron G p.L x)^5)
-- controlling Stage-post output.As.Support.Power.
include hp hd hZ
lemma receives (δ:ℝ): Rate G p.L (-11/10) (transit p r s t X D δ):=by
   have ht:= (grand p r s t X D hp hd hZ).rate ; let a:= Access.apron G p.L; have he:= Access.rates_apron (G:=G) (L:=p.L)
   apply Rate.mul_left; apply Rate.add
   · apply Rate.add
     · convert! (incomingE_rate G p.L).mul_left (1+|δ|) using 1; ring
     exact (ht.mul (he.pow 3)).weaken (by norm_num)
   exact (ht.mul (he.pow 5)).weaken (by norm_num)
omit hp hd hZ
variable {M:BudgetPoint}{x β:ℝ}
lemma royalties : 0≤ Πx x:=by unfold royale; positivity
def headwind (G:Gauge)(M:BudgetPoint)(c:Clip)(σ C:ℝ):= hitPower M G 1 0*lowHard M c σ C
-- Uptake need signal ONLY for when comparison to history claims full next
-- Lawful cap. Stronger incoming E smallness after authenticated separation:
-- U ⊆ {‖e‖≤ g^2.5}, others not included as e. Asymptotically eligible e
-- size on our allocated η<1/2. Use when doing the RG04.Q progression.
-- This cap is AFTER slope/scalar effects appended to residual.
-- Distinguish incomingE (whole-law E cap) from this demand on inherited errors.
def sail (M:BudgetPoint)(x β δ:ℝ):= let g:=gStep β; turnFee M*((1+|δ|)*g ^ ((5/2:ℝ))+ royale p r s t X D x * g^(r.p+1)+ royale p r s t X D x*g^5)
-- next's remaining δ inside locality; costs transport via Γ enough separately
abbrev hair (x:ℝ):ℝ:= (Real.sqrt x)⁻¹ ^ ((11:ℝ)/5)
def seam (x β δ:ℝ)(M:BudgetPoint) :=
      2≤r.p → ∀ H≤ sail p r s t X D M x β δ, regularNeed G M X.clip X.width X.paths 0 H ≤ Tuba.hair x/4
structure Beyond (μ x β:ℝ)(M:BudgetPoint)(δ:ℝ) : Prop where
    slight : WilsonStartup.Decent X.clip M ∨ ¬ X.clip.direct≤ 1
    halo : Geo.Width M X.clip X.width
    -- Strong K carried on markup output terms with enough profile space for tolerance.Paid all.<Circ k>. Standard calendar comparison ready
    brightness : Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ)) ≤ Lyric.unitK x^4
    forever (v H ζ:ℝ) : 2≤r.p → 0≤H→ 0≤ v→ v≤gStep β^5 → H≤ turnFee M*((1+|δ|)* incomingE G p.L x+ royale p r s t X D x * gStep β^(r.p+1)+ royale p r s t X D x*v) → ζ ≤ |Tempo.proposal p r s t X D x| →
       ∃ W y z:ℝ, Flues.Resonant M.B r.k (Expenditure.signed p r t D.Rb s.unsigned x + (s.unsigned x + Ethereal.ocean G M X.clip X.width X.paths 0 H)+ Tuba.headwind G M X.clip X.width X.paths) (Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ))*gStep β^r.s) (Expenditure.autumn p r s t X D x β v+ζ) M.supportExponent (Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ))*gStep β^r.finalG) W y z
    restores : seam p r s t X D x β δ M
-- helpers.C_0 for.L.E. before Tube.C.
lemma rhine (hm:Temper M X x G p.L) : turnFee (Time.probe X) = turnFee M:=by unfold turnFee Time.probe; rw [hm.power,hm.order]
variable {σ:ℝ} {q B:ℕ}{w w' b b' η η' c W' y z:ℝ}
lemma resonates' (h:Flues.Resonant B q w b η σ c W' y z)(hx:w' ≤ w)(he:b'≤b)(hf:η'≤η): Flues.Resonant B q w' b' η' σ c W' y z :={ h with
    small:=hx.trans h.small
    joint:= (add_le_add (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr h.gain.le)) (add_le_add (mul_le_mul_of_nonneg_left hx zero_le_two) (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr (zero_le_one.trans h.shrink))))).trans h.joint }
variable {Q p r s t X D}
lemma Beyond.alters {μ β x:ℝ}{M:BudgetPoint}(h : Beyond Q p r s t X D μ x β M δ) (v H ζ:ℝ) : 2≤r.p → 0≤H→ 0≤ v→ v≤gStep β^5 → H≤ turnFee M*((1+|δ|)* incomingE G p.L x+ royale p r s t X D x * gStep β^(r.p+1)+ royale p r s t X D x*v) → ζ ≤ |Tempo.proposal p r s t X D x| →
       ∃ W y z:ℝ, Flues.Resonant M.B r.k (Expenditure.signed p r t D.Rb s.unsigned x + (s.unsigned x + Ethereal.ocean G M X.clip X.width X.paths 0 H)) (Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ))*gStep β^r.s) (Expenditure.autumn p r s t X D x β v+ζ) M.supportExponent (Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ))*gStep β^r.finalG) W y z:=by
    intro h₀ hV hU hx hT he; obtain ⟨W,y,z,hu⟩:= h.forever v H ζ h₀ hV hU hx hT he; have hh : 0≤ headwind G M X.clip X.width X.paths:= mul_nonneg (hitPower_pos ..) (budget_pos M G X.clip X.width_pos X.paths_pos.le).2.2
    refine ⟨W,y,z,resonates' hu ?_ le_rfl le_rfl⟩; linarith only [hh]
variable (Q p r s t X D)
lemma Beyond.cruise {μ β x:ℝ}{M:BudgetPoint}(h : Beyond Q p r s t X D μ x β M δ) (v H:ℝ) : 2≤r.p → 0≤H→ 0≤ v→ v≤gStep β^5 → H≤ turnFee M*((1+|δ|)* incomingE G p.L x+ royale p r s t X D x * gStep β^(r.p+1)+ royale p r s t X D x*v) →
       ∃ W y z:ℝ, Flues.Resonant M.B r.k (Expenditure.signed p r t D.Rb s.unsigned x + (s.unsigned x + Ethereal.ocean G M X.clip X.width X.paths 0 H)) (Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ))*gStep β^r.s) (Expenditure.autumn p r s t X D x β v) M.supportExponent (Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ))*gStep β^r.finalG) W y z:=by
    intro h₀ hV hU hx hT; obtain ⟨W,y,z,H⟩:=h.alters v H 0 h₀ hV hU hx hT (abs_nonneg _); exact ⟨W,y,z,(by rwa [add_zero] at H)⟩
open Expenditure
include hp hd hZ
lemma eligible (δ:ℝ) : ∀ᶠ x in atTop,∀ Z:BudgetPoint, Temper Z X x G p.L→ ∀ β,inBand (betaF G x p.L) β→ seam p r s t X D x β δ Z:=by
    let A:=Access.apron G p.L; let Gv:= fun x=> betaF G x p.L
    let κ:= Time.base G X
    let Xv x :ℝ:= turnFee (Time.probe X)*((1+|δ|)*(A x) ^ ((5/2:ℝ))+ royale p r s t X D x * (A x)^3+royale p r s t X D x * (A x)^5)
    have hv : Rate G p.L (-5/4) (fun x=> κ*Xv x):=by
       have hh:= (grand p r s t X D hp hd hZ).rate
       have hg : Rate G p.L (-(1/2)) A:= Access.rates_apron
       have hF : Rate G p.L (- (5/4)) (fun x=> A x ^ ((5/2:ℝ))):=by
          intro j hj; have he: -(1/2:ℝ)< j/(5/2:ℝ):=(lt_div_iff₀ (by norm_num)).2 (by linarith only [hj])
          filter_upwards [hg _ he, Delay.shift_pos G p.L] with x hx ht
          have hh : 0 < A x:= mul_pos (by norm_num) (Fare.gS _ ht).1
          rw [abs_of_pos (Real.rpow_pos_of_pos hh (5/2:ℝ))]; exact (Real.rpow_le_rpow hh.le ((le_abs_self _).trans hx) (by norm_num : (0:ℝ) ≤ 5/2)).trans_eq (show (Gv x ^ (j/(5/2:ℝ))) ^ ((5/2:ℝ)) = _ from (by rw [← Real.rpow_mul ht.le, show j / (5/2:ℝ) * (5/2) = j from div_mul_cancel₀ j (by norm_num)]))
       apply Rate.mul_left; apply Rate.mul_left
       exact ((hF.mul_left (1+|δ|)|>.weaken (by norm_num)).add ((hh.mul (hg.pow 3)).weaken (by norm_num))).add ((hh.mul (hg.pow 5)).weaken (by norm_num))
    have hFto x (hx:0<Gv x): hair (Gv x) = Gv x ^ ((-(11/10):ℝ)):=by
        unfold hair; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
    filter_upwards [eventually_gt_atTop (0:ℝ), Delay.shift_pos G p.L, ((hv.mul (Rate.power (G:=G) (L:=p.L) (a:=11/10))).mul_left 4).below (by norm_num) 1 zero_lt_one, Access.wide (Rate.const (G:=G) (L:=p.L) 1)] with x hx ht hk he Z hZ' β hβ h H hH
    rw [Time.table G X ⟨hZ'.power,hZ'.order,hZ'.salary⟩]; simp only [abs_zero,zero_mul,mul_zero,add_zero]
    have hh:= he.2 β hβ; let g:=gStep β; have hz:g ≤1:= hh.2.le.trans (he.1.2.1.le.trans he.1.2.2.1.le)
    have ha : H≤ Xv x:=by
        apply hH.trans; change sail _ _ _ _ _ _ _ _ _ _ ≤ _
        unfold sail Xv; rw [rhine p X hZ']; dsimp only; have ha:0≤ Πx x:= royalties p r s t X D
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh.1.le hh.2.le (by norm_num : (0:ℝ) ≤ 5/2)) (by positivity : (0:ℝ) ≤ 1+|δ|)) (mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_of_le_one hh.1.le hz (show 3≤r.p+1 by omega)) (pow_le_pow_left₀ hh.1.le hh.2.le 3)) ha)) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.1.le hh.2.le 5) ha)) (turnFee_pos _).le
    have hg : Gv x ^ (-(11/10):ℝ) ≤ Tuba.hair x := by rw [← hFto _ ht]; let L:=p.L; have he:x≤Gv x:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L); apply Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt he)) (by norm_num)
    refine le_trans (mul_le_mul_of_nonneg_left ha (Time.base_nonneg G X).1) ((le_trans ?_ (div_le_div_of_nonneg_right hg (by norm_num))))
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<4),Real.rpow_neg ht.le,← one_div,le_div_iff₀ (Real.rpow_pos_of_pos ht _)]
    refine le_trans ?_ ((le_abs_self _).trans hk); apply le_of_eq; change κ * Xv x * 4 * Gv x ^ ((11/10:ℝ))= 4 *(κ * Xv x*Gv x ^ ((11/10:ℝ))); ring
lemma financed (q:ℝ)(h:r.Heart X q)(hμ:0<μ)(hr:e<0)(δ:ℝ) : ∀ᶠ x in atTop,∀ Z:BudgetPoint, Temper Z X x G p.L→ ∀ β,inBand (betaF G x p.L) β→ Beyond Q p r s t X D μ x β Z δ:= by
    let a:= transit p r s t X D δ
    let k:= signed p r t D.Rb s.unsigned
    let u':ℝ→ℝ:= fun x=>swell G X * (1+(radiusB x : ℝ))^(4:ℕ)* (2*fiery G x p.L)
    let f' x:= 2*(2*fiery G x p.L)*(lowHard (Time.probe X) X.clip X.width X.paths * (1+(radiusB x:ℝ))^(4:ℕ))
    let b' x:= k x+(s.unsigned x + u' x)+f' x; let c:=max e s.rate
    have hv: Rate G p.L c k:= salary' p r t D.Rb s.unsigned c (hp.low.weaken (le_max_left ..)) (s.stage.weaken (le_max_right ..))
    have hu : Rate G p.L (-(1/2)) u' := by
       have hf:=(((Rate.const (G:=G) (L:=p.L) 1).add Rate.radius_price).pow 4).mul_left (Tuba.swell G X)
       simpa only [zero_mul,zero_add] using! hf.mul (Rate.flame.mul_left 2)
    let a' x:= Real.exp ((-Q.mark p.L μ x)*(1/2:ℝ)); have hΛ := Lyric.strongK Q p.L hμ
    have hA : ∀ᶠ x in atTop,0 < a' x ∧ a' x ≤1:=hΛ.mono (fun i hi=>⟨Real.exp_pos _,hi.trans (pow_le_one₀ (Flues.cheap i).1.le (Flues.cheap i).2)⟩)
    let z:= max c (-(1/2:ℝ))
    have hh : Rate G p.L z b':= by
       have hh : Rate G p.L (-(1/2)) f':=by simpa [f'] using! (((Rate.flame.mul_left 2).mul_left 2).mul ((((Rate.const (G:=G) (L:=p.L) 1).add Rate.radius_price).pow 4).mul_left (lowHard (Time.probe X) X.clip X.width X.paths)))
       exact ((hv.weaken (le_max_left ..)).add ((s.stage.weaken ((le_max_right ..).trans (le_max_left ..))).add (hu.weaken (le_max_right ..)))).add (hh.weaken (le_max_right ..))
    have hl:= (Expenditure.inclined p r s t X D hp hZ hd)
    filter_upwards [Tuba.shelling G X p.L, Flues.buying a' hA b' _ hh (max_lt (max_lt hr s.night) (by norm_num)) (hl.absolute.add (Tempo.mentions p r s t X D hp hd hZ).absolute).rate X.price_pos.le r.k r.finalG,Tuba.rhythm G p.L,Access.exchange _ 2 (by norm_num) (receives p r s t X D hp hd hZ δ),Delay.shift_pos G p.L,hΛ, eligible p r s t X D hp hd hZ δ, Access.wide (Rate.const (G:=G) (L:=p.L) 1)] with x hx hm hv hP hF h₀ h_t hk Z hZ' β hβ
    have hh := hx _ hZ'; have he := hk.2 β hβ; let g:=gStep β
    have hy : g ≤ 1:= he.2.le.trans (hk.1.2.1.le.trans hk.1.2.2.1.le)
    have hb : inBand (betaF G x p.L) (betaF G x p.L):= ⟨by linarith,by linarith⟩
    have ho : 0≤ royale p r s t X D x:= royalties p r s t X D -- shadow
    refine ⟨(by by_cases he:X.clip.direct≤1; exact Or.inl (hh.1 he); exact Or.inr he),hh.2,h₀,?_,h_t _ hZ' _ hβ⟩ -- use classical err
    intro v QH ζ hm' hQ hi hv' ht hz
    obtain ⟨W,y,d,hX⟩:= hm β hβ
    have hp₀: QH ≤ Z.threshold^2 := le_trans (b:=a x) ?_ (le_trans ((le_abs_self _).trans (hP _ hb)) (pow_le_pow_left₀ hv.1.le (hZ'.pressure.symm ▸ hv.2) 2))
    · refine ⟨W,y,d,?_⟩; rw [hZ'.pose,hZ'.salary]; refine resonates' hX (le_trans ?_ (le_abs_self _)) ?_ ((add_le_add ((Expenditure.prize p r s t X D hZ' (β:=β) hy hi (hv'.trans (pow_le_one₀ he.1.le hy))).2.trans (le_abs_self _)) hz).trans (le_abs_self _))
      · apply add_le_add
        swap
        · unfold f' headwind hitPower; rw [abs_zero, add_zero,abs_one,one_mul,zero_mul,zero_mul,zero_mul,add_zero]; exact mul_le_mul (mul_le_mul_of_nonneg_left hZ'.pact zero_le_two) (hZ'.pose ▸ Time.lowSoft_exp X ⟨hZ'.power,hZ'.order,hZ'.salary⟩) (budget_pos Z G X.clip X.width_pos X.paths_pos.le).2.2 (mul_nonneg zero_le_two (hZ'.pact.trans' Z.threshold_pos.le))
        apply add_le_add_right (add_le_add_right _ _) _; have hu:= Tuba.coast G X ⟨hZ'.power,hZ'.order,hZ'.salary⟩ hQ hp₀
        apply hu.trans; unfold u'; rw [hZ'.pose]; exact mul_le_mul_of_nonneg_left hZ'.pact (mul_nonneg (Tuba.shore G X) (pow_nonneg (by positivity) _))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he.1.le hy h.atHull) (Real.exp_pos _).le
    refine ht.trans ?_
    unfold a transit; rw [rhine p X hZ']; exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_of_le_one he.1.le hy (show 3≤r.p+1 by omega)) (pow_le_pow_left₀ he.1.le he.2.le 3)) ho) _) (mul_le_mul_of_nonneg_left (hv'.trans (pow_le_pow_left₀ he.1.le he.2.le 5)) ho)) (turnFee_pos _).le
end Tuba
end YM.RemainderComparison.Cadenza
