import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Diap
import YM.Planned.STATIONARY_JET_PORT.Enclosures

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Progress.StationaryScenes.Green AnalyticBridge.MarginalMultiplier3b1d.FiniteMatrix
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    {u v D s m l p σ σ' C C' Λ Λ' q W : ℝ} {n : ℕ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "V" => (fun x:Xs=>represent (tint G _ x))
variable (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)) (ρ : Bid.Dir G c→AxisChart G F) (X: Coat T F) (β : ℝ)
    (B B' : BudgetPoint) {P : Teller G}
variable (he : A.Service F T.high T.up ρ) (ha : Larger (G:=G) S) (h : T.up.Bounds T.high σ C Λ) {d : ℝ}
    (hm : ClassicalMatch F T.high T.low T.up T.down ρ) (hq : T.down.Bounds T.low σ' C' Λ') (J : BareRates.pre G σ' C' (n+3))
local notation "R₀" => Pane.virgin T B β
local notation "M" => A.tables T.high S.patch
local notation "f₁" => Lapis.table F k T.up T.high
local notation "r" => Lapis.orbit F ρ
section tintSteps
variable {F T}
def stocksK (G : Gauge) (n : ℕ) (σ C : ℝ) (J : BareRates.pre G σ C (n+3)) (q : Clip) (v : ChartPrices) :=
    let M' := townCost G
    reception G M' 5 (classicalRate v n) (classicalBill v n)+reception G M' 5 (dial σ (n+3)) (BareRates.bill J q)
include he ha h hm hq
lemma red (hn : 5 ≤ n+3) (x:Xs) (V₀ : ℝ) (ht : (Fintype.card (Site c):ℝ) ≤ V₀) (hx : Uniform.shade G*‖x‖ < min (M).horizon 1) :
    let C₀:=stocksK G n σ' C' J T.low M
    |f₁ (x,r x) - mainTerm T.low T.down (V x)| ≤ V₀*C₀*‖x‖^5 := by
  intro C₀
  obtain ⟨h₁,hp,hH⟩ := onMeeting he h ha rfl rfl k hq J hn hm
  change 0<C₀ at hp; have hv:= hH 0 (by decide) _ (mem_ball_zero_iff.mpr ((Uniform.tint_le (G:=G) x).trans_lt hx)) Fin.elim0
  simp only [iteratedFDeriv_zero_apply,Nat.sub_zero,ContinuousLinearEquiv.symm_apply_apply,Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht hp.le) (by positivity))
end tintSteps

variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
include F T
omit T in
lemma market (O : ChartRatio G) : solar F O β=prefactor S G β* measure_g O β ^Fintype.card F.Free := by
  unfold solar measure_g; rw [mul_pow O.scale,← pow_mul]; rw [show Fintype.card K=Fintype.card G.ColorIndex * Fintype.card F.Free from (Fintype.card_prod ..).trans (mul_comm ..)]; ring -- mul_pow match order
lemma overdraft (X : Coat T F) (O : ChartRatio G) (h:B'.threshold=Pressure.temp X.x) (hb : flags B'.threshold X.V=∅): Matter.overhead X R₀ O =
    solar F O β * Real.exp (-β * secondTerm T.low T.down X.V- Real.log X.blank.plate.det/2):= by
  unfold Matter.overhead levy deducted; rw [Raw.stone_full _ _ _ B' h]; rw [market F]; simp_rw [Pane.crystal _ _ B' _ (Pane.tranquility _ hb _ 0)]; change (prefactor S G β * Real.exp (0*_)* Real.exp _) * (measure_g O β^_ * Real.exp _) = _
  rw [zero_mul,Real.exp_zero,mul_one,show -β * _- _/(2:ℝ)= -β * secondTerm T.low T.down X.V+ -Real.log X.blank.plate.det/2 by ring,Real.exp_add]; change prefactor S G β*Real.exp (-β*secondTerm T.low T.down X.V)*(_*Real.exp _)=_; ring

lemma chairs (H : Cash W X.x l L Q o p T R₀) (hm : X.manifest) (hw : X.width=o.K) : Real.log X.blank.plate.det ≤ (Fintype.card (Tubular f G):ℝ)*o.ample := by
  let A:=X.blank.plate; have he:Window.Allow A _ _ o.eta o.gap o.ample := (H.laws.data.localP F X rfl hw hm).empty.scale
  have hh:= Control.definite he.symmetry he.ground he.down
  apply AnalyticBridge.MarginalMultiplier3b1d.FiniteMatrix.log_le _ he.fuel.le hh.det_pos
  intro j; apply le_trans _ (le_add_of_nonneg_left zero_le_one); apply le_trans _ (he.price j); apply sum_le_sum
  intro i _; have ht : A i j=A j i:= by simpa using congr_fun (congr_fun he.symmetry j) i
  rw [ht]; exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (mul_nonneg he.eta.le (Nat.cast_nonneg _)))

-- rate razor: compare base indices ONLY at Healthy coarse
variable {x : Positions (Uniform.Primary c G)}
include hm hq he ha h
lemma bench (J : BareRates.pre G σ' C' (n+3)) (hn : 5 ≤ n+3) (hb : 0<β) (H : Cash W X.x l L Q o p T R₀) (hm' : X.manifest) (hw : X.width=o.K) (K₀ : ℝ)
    (hV : X.V=V x) (hy : B'.threshold=Pressure.temp X.x) (hv : flags B'.threshold (V x)=∅)
    (hΘ : Uniform.shade G*‖x‖ < min (M).horizon 1) (hc : (Fintype.card (Site c):ℝ)≤K₀) (hk : (Fintype.card (Tubular f G):ℝ)≤K₀) (hf : (Fintype.card (Joint F G):ℝ) ≤ K₀)
    (hg : Golf (Lapis.table F k T.up T.high) (mist F Q.table T.up) r (gram F T.up T.high ρ k) n D u v q) (ht : ‖x‖<u) (hr : u ≤ (M).horizon) :
    let C₀:=stocksK G n σ' C' J T.low M
    let e:=β*(K₀*C₀*‖x‖^5 + K₀*(C'*B'.threshold^3+C'*B'.threshold^4))+ (q+tapir (M) K₀ +K₀*o.ample/2)
    solar F Q.table β * Real.exp (-coverLog F T Q.table k ρ β x-e) ≤ Matter.overhead X R₀ Q.table := by
  intro C₀ e; rw [overdraft F T β B B' X Q.table hy (hV.symm ▸ hv)]
  have h₁:= red k A ρ he ha h hm hq J hn x K₀ hc hΘ; have hV₀ := abs_le.mp h₁|>.1; have hy:=classbill T.down B' (V x) hq hv
  have hx:=mul_le_mul_of_nonneg_right hc (show 0 ≤ C'*B'.threshold^3+C'*B'.threshold^4 by have h:=B'.threshold_pos; have hh:0≤C':= (tsum_nonneg hq.three.1).trans hq.three.2.2; positivity)
  have hz:=abs_le.mp (hy.trans hx)|>.1
  -- Need cover ≥ βbase -e+ logdet. minus β * (classic - base) controlled lower
  apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (sun F Q.table β hb Q.table_exists).le
  have ht:= (abs_le.mp (colo F T k A ρ Q.table he ha h K₀ hf hg hr x ht β)).1
  have hh:= (chairs F T X β B H hm' hw).trans (mul_le_mul_of_nonneg_right hk (H.laws.data.localP F X rfl hw hm').empty.scale.fuel.le)
  rw [hV]; unfold e; linarith only [ht,hh,mul_le_mul_of_nonneg_left hz hb.le,mul_le_mul_of_nonneg_left hV₀ hb.le] -- hV changes det?
end YM.PhysicalNext.Repeat.Fare
