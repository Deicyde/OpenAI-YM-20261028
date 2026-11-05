import YM.UVExtension.Payroll.Marches
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Payroll
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Blaze March Shell Channel SliceRows Control Window
open PhysicalNext PhysicalNext.Repeat Marlin Height Animals Slide Song Trio Wick Lamppost
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Progress.DirectedRecipe
open YM.UVExtension.Concert
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
-- post geometry prices. purchases from prebrace extended.
variable {G : Gauge} {L : Side} {P:Teller G} (Q : Target G P) (C : RG.Stage) {q : ℕ} (L:Side) (W μ a : ℝ) (o:Target.Order G W) {ε:ℝ}
def colorspeed : ℝ:= -(3/8)
def fillSpeed : ℝ:=1/32
def hearts (G:Gauge)(L:Side)(x:ℝ):=betaF G x L^fillSpeed
-- recoil receipt
structure Flew (x:ℝ)(ε:ℝ) : Prop where
  opens : Q.rate≤colorspeed
  engines : (∀ N : ℕ, N=4 → -- Finance currently arity exactly 4, pad users
    ∀ {c f} (S:StepData c f) (T:Tube G S) (R:Rep G f) (H:Cash W x μ L Q o a T R), Stamp T → ∀ (ι:Type) [Fintype ι], Fintype.card ι=N →∀ (V:ι→ Juice G f) {w:ℝ} (K:Festa Q L H V w (Payroll.hearts G L x)) (p:BudgetPoint) (γ Λ : ℝ), Time.Same C p → p.threshold=Pressure.temp x → p.B=radiusB x → T.down.Bounds T.low C.width C.paths Λ → WilsonStartup.Decent T.low p→ preExponent p/p.B ≤ C.width/2 →
    Song.octaveNeed G p T.low C.width C.paths Λ (betaF G x L) γ ≤ betaF G x L ^ (-(7/16):ℝ) → ∀ J:(d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V),
      (∀ d,smoothP p (Beam.marquee H p).reg (plusone H (fleet d J H) Chi.canonical γ).logRead)∧
      Nonempty (ticketR (aperture K) p (Beam.marquee H p).reg (preExponent p) (fun d=> (plusone H (fleet d J H) Chi.canonical γ).logRead) (fun _=>Payroll.drum G L C x)) ∧
        Nonempty (Atlas (bell (Beam.marquee H p).hard p.B (p.supportExponent+1+1)) (aperture K) (fun d i U=> (plusone H (fleet d J H) Chi.canonical γ).hardRead i U) (fun _ => Cash.armK (stalk Q opens (by norm_num [colorspeed])) L μ x 0 0)))
  alive : 0 ≤ drum G L C x
  seek : Payroll.seek G L C Q.halo x≤ pay G L x
  run : freshW G L C Q.halo x≤ pay G L x
  changeK : ∃ κ, Payments.Rates (radiusB x) (prize G L x (ε/8)) (Cash.armK (stalk Q opens (by norm_num [colorspeed])) L μ x 0 0) (pay G L x) κ
  returns : ∀ b,0≤ b → b≤ pay G L x→∃ κ, Payments.Rates (radiusB x) (prize G L x ε) (prize G L x (ε/8)) b κ
  travel : ConnectedActivityE6.incomingK G L x ≤ Real.exp (-((Vac.Numbers.P x)^((1:ℝ)/5)))

set_option maxHeartbeats 400000 in
lemma collecting : ∃ n : ℕ,∀ (L:Side), n ≤ L.val→∀ (W μ a ε:ℝ) (o:Target.Order G W),0<W → 0<μ → 0≤ a → 0<ε → ∀ C:RG.Stage,C.supportExponent+3 < Q.exp→ Q.rate ≤ -(7/16:ℝ) → ∀ᶠ x in atTop,Flew Q C L W μ a o x ε := by
  obtain ⟨n,hN⟩:= basisE Q; use n; intro L hL W μ a ε o hW hm ha he C hh hy
  have hp: Q.rate+fillSpeed<colorspeed:=by unfold colorspeed fillSpeed; linarith
  have hx:0<fillSpeed:=by norm_num [fillSpeed]
  have hz:colorspeed<0:=by norm_num [colorspeed]
  have hr: Q.rate≤colorspeed:= by linarith
  let K:= Q.halo; let P':=stalk Q hr hz
  let t : ℝ:=C.supportExponent+3
  let y:=(Q.exp-t)/3; have hY:0<y:= by unfold y t; linarith
  have hk:= harvest G L C K
  obtain ⟨A,hA,hF⟩:= Festa.lodges hx hp hz a ha 4 hY W hm (L:=L)
  let u:=ε/8; have hU : 0 < u := div_pos he (by norm_num)
  have h: ∀ᶠ x in atTop, (∀ N:ℕ, N=4 → ∀ {c f} (S:StepData c f)(T:Tube G S)(R:Rep G f)(H:Cash W x μ L Q o a T R), Stamp T→∀ (ι:Type)[Fintype ι], Fintype.card ι=N →∀ (V:ι→Juice G f) {w}(K':Festa Q L H V w (Payroll.hearts G L x)) (p:BudgetPoint)(γ Λ:ℝ), Time.Same C p → p.threshold=temp x → p.B=radiusB x → T.down.Bounds T.low C.width C.paths Λ → WilsonStartup.Decent T.low p→ preExponent p/p.B ≤ C.width/2 → Song.octaveNeed G p T.low C.width C.paths Λ (betaF G x L) γ ≤ betaF G x L ^ (-(7/16):ℝ) → ∀ J:(d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V),
    (∀ d,smoothP p (Beam.marquee H p).reg (plusone H (fleet d J H) Chi.canonical γ).logRead)∧ Nonempty (ticketR (aperture K') p (Beam.marquee H p).reg (preExponent p) (fun d=> (plusone H (fleet d J H) Chi.canonical γ).logRead) (fun _=>Payroll.drum G L C x)) ∧
        Nonempty (Atlas (bell (Beam.marquee H p).hard p.B (p.supportExponent+1+1)) (aperture K') (fun d i U=> (plusone H (fleet d J H) Chi.canonical γ).hardRead i U) (fun _ => Cash.armK P' L μ x 0 0))) := by
    by_cases h: ∃ D:Patch,D.Branches P.bind G ∧D.L=L ∧ D.J=P.j
    swap; · exact Eventually.of_forall fun x N heq c f S T R H hS=> (h ⟨S.patch,H.laws.data.funds.funds.kernel,H.laws.data.funds.length_eq,H.laws.data.funds.funds.atStep⟩).elim
    obtain ⟨D,hD,hd,h⟩:= h; obtain ⟨θ,hθ,ht⟩:= hN L hL D Chi.canonical W μ o hD hW hm 4 C.order C.power colorspeed fillSpeed t (by unfold t; linarith [C.price_pos]) hh hx hp hz
    filter_upwards [ht,hθ (-(1/3:ℝ)) (by norm_num [colorspeed]),hF,P'.certify L hm 0 y y hY hY,(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hy hx hZ hA hg N hEq c f S T R H hS ι inst hQ V w K' p γ Λ hp hv hr' hT hC ht hu J
    subst N
    have hP:preExponent p = t:=by unfold preExponent t; rw [hp.2.2]
    obtain ⟨hr,⟨h₁⟩⟩:= hy c f S (H.laws.data.funds.patch hd h) T _ _ H hS ι V hQ w K' p J hP.le hp.2.1.le hp.1.le hv hr'
    obtain ⟨hΨ,⟨h₂⟩⟩:= opusE p γ hT hC ht hg K' J Chi.canonical hr h₁
    refine ⟨hΨ,broaden _ _ h₂ (fun x' _=> ?_),?_⟩
    · have he := Payroll.panels G L C K x p hp|>.1; unfold Payroll.drum; rw [← he]; exact mul_le_mul_of_nonneg_left (add_le_add ((le_abs_self _).trans hx) (mul_le_mul_of_nonneg_left hu (by norm_num))) (mul_nonneg (by norm_num) (turnFee_pos _).le)
    let Y:= hZ c f S T o R H ι V hQ w K'; have ht:p.supportExponent+1+1+y+y ≤ Q.exp-y := by unfold t at hP; unfold preExponent at hP; unfold y t; linarith
    have hi:0≤ Q.exp-y:=by linarith [p.exponent_pos]
    have hb:= bellsOut K' Y hi J Chi.canonical (by linarith [p.exponent_pos] : 0≤ p.supportExponent+1+1) hY hY ht hA.2.2.2.1 hA.2.2.2.2 hA.2.2.1
    rw [hr']; exact hb
  filter_upwards [h, hk.1 _ (by norm_num : -(1/3:ℝ)< -(1/8:ℝ)), hk.2 _ (by norm_num : -(1/3:ℝ)< -(1/8:ℝ)), Delay.shift_pos G L, cashiers (G:=G) L he,cashiers (G:=G) L hU,soaredK P' L hm hU,stipend (G:=G) L] with x hx ht hU' hv hy' hz h hK
  refine ⟨hr,hx,?_,(le_abs_self _).trans ht,(le_abs_self _).trans hU',hz _ _ h.1 (Real.rpow_nonneg hv.le _) h.2 le_rfl,fun b hB h' => hy' _ _ (mul_nonneg hU.le (Real.exp_nonneg _)) hB ?_ h',hK⟩
  · unfold Payroll.drum Height.away Push.Local.turnCost; positivity
  unfold prize; linarith -- ratio
end YM.UVExtension.Payroll
