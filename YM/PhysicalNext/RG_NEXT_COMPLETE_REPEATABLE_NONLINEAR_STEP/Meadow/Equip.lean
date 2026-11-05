import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Litho
/-! # Quantitative fees at antenna, ask before clocks for extras
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
variable {G : Gauge} {c f L₀ : Side} {M k: ℕ} {σ C δ β r s : ℝ}
def cousin (p q:BudgetPoint):= p.power=q.power∧ p.order=q.order∧ p.supportExponent=q.supportExponent
lemma postage (p q:BudgetPoint) (hp : cousin p q) : turnFee p=turnFee q ∧ Geo.lowFee G p σ=Geo.lowFee G q σ ∧
    (∀ k,anchoredFee (headline p) k=anchoredFee (headline q) k) ∧ ∀ k,highFee G k p σ=highFee G k q σ:= by
  constructor; · unfold turnFee; rw [hp.1,hp.2.1]
  constructor; · unfold Geo.lowFee Geo.rowDegree lowCost rowCost pairBill faceCost; rw [hp.1,hp.2.1]
  refine ⟨fun k=>?_,fun k=>?_⟩
  · unfold anchoredFee headline; simp only [preExponent,hp.2.2]
  unfold highFee; rw [hp.1,hp.2.1]
lemma rain (G:Gauge) (l:Clip) (hs:0 < σ) (hc : 0 ≤ C) (q:BudgetPoint) (p:BudgetPoint) (hp:cousin p q) {A B T Λ Y:ℝ}
    (hA : |β| ≤ A) (hr:|r| ≤ B) (hh:p.threshold ≤ T) (hk:0 ≤ Λ) (hY:Λ ≤ Y):
    let s i:=anchoredFee (headline q) i
    let fee i a b:=s (Song.octave i)* (|VerifiedReset.factor| *a*(turnFee q * (highFee G i q σ*T^i*b)))
    Song.octaveNeed G p l σ C Λ β r ≤ s Geo.lowCount*(|VerifiedReset.factor| *B*(turnFee q*T^2*(lowFee G q σ * lowerSize l C))) + (fee 3 A C + (fee 4 A C+ fee 2 1 Y)):= by
  intro s f
  obtain ⟨ht,hQ,h,hF⟩:= Meadow.postage (G:=G) (σ:=σ) p q hp
  have hp' i: 0≤ s i:= mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _); have he : 0 ≤ B:= (abs_nonneg _).trans hr; have hZ:0 ≤ lowerSize l C:= by unfold lowerSize; have := l.quadratic_pos; positivity
  have hv := p.threshold_pos; have hh':= turnFee_pos q; have hV:= lowFee_nonneg G q hs
  unfold octaveNeed; simp_rw [h]; apply add_le_add
  · refine mul_le_mul_of_nonneg_left ?_ (hp' _); unfold host; rw [ht,hQ,abs_mul,abs_neg]; gcongr
  have hh (k) (v V p' P' : ℝ) (hf:|v|≤ V) (hv:0≤ p') (hk:p'≤P'): s (octave k)* tenor G k p σ p' v ≤ f k V P':= by
    apply mul_le_mul_of_nonneg_left _ (hp' _); unfold tenor; rw [ht,hF,abs_mul]; have hA:= highFee_pos G q k hs
    apply mul_le_mul (mul_le_mul_of_nonneg_left hf (abs_nonneg _)) _ _ _ <;> first | positivity | exact mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans hf) | gcongr
    all_goals have hT:0 ≤ T:=p.threshold_pos.le.trans hh; positivity
  have h' : |-β|≤ A:= (abs_neg _).trans_le hA
  exact add_le_add (hh 3 _ _ _ _ h' hc le_rfl) (add_le_add (hh 4 _ _ _ _ h' hc le_rfl) (hh 2 _ _ _ _ (by norm_num) hk hY))
lemma spur (G : Gauge) (L : Side) (B:Stage) (k : ℝ) (_he: 0 < k) : ∃ q: ℝ→ℝ, Rate G L (-(1/2)) q ∧ ∀ᶠ t in atTop,
    ∀ P : BudgetPoint,P.power=B.power→P.order=B.order→ P.supportExponent=B.supportExponent→ P.threshold ≤ 2*Pressure.fiery G t L→∀ β b Λ, |β|≤2*Pressure.betaF G t L→|b|≤ k→0 ≤ Λ→ Λ≤ ConnectedActivityE6.loopBill G L t→
      Song.octaveNeed G P B.clip B.width B.paths Λ β b ≤ q t := by
  by_cases hs: ∃ p:BudgetPoint,p.power=B.power ∧ p.order=B.order∧p.supportExponent=B.supportExponent
  swap
  · exact ⟨_,Rate.power (G:=G) (L:=L),Eventually.of_forall fun t P hp hq hE => (hs ⟨P,hp,hq,hE⟩).elim⟩
  obtain ⟨p,hp,hq,hE⟩:=hs
  let c:=B.paths; have hc:0≤c:=B.paths_pos.le -- inspect
  let T t:=2*Pressure.fiery G t L
  let K t:=2*Pressure.betaF G t L
  let s i:= anchoredFee (headline p) i -- edit
  let f i t a b:= s (octave i)*(|VerifiedReset.factor| *a*(turnFee p*(highFee G i p B.width*T t^i*b)))
  let q t:= s Geo.lowCount*(|VerifiedReset.factor| *k*(turnFee p*T t^2*(lowFee G p B.width * lowerSize B.clip c)))+(f 3 t (K t) c+(f 4 t (K t) c+ f 2 t 1 (ConnectedActivityE6.loopBill G L t)))
  have ht:Rate G L (-(1/2)) T:=Rate.flame.mul_left _
  have hv:Rate G L 1 K:= Rate.hat.mul_left _
  have hK : ∀ (b:ℕ) (A : ℝ→ℝ) (B:ℝ) (U : ℝ→ℝ) (a:ℝ), Rate G L B A→Rate G L a U→ B+(-(1/2:ℝ)*b+a) ≤ -(1/2:ℝ)→ Rate G L (-(1/2)) (fun t=>f b t (A t) (U t)):= by
    intro i A B X a he hK hs; exact (Rate.mul (he.mul_left |VerifiedReset.factor|) (((((ht.pow i).mul_left _).mul hK)).mul_left _)|>.mul_left _).weaken hs
  refine ⟨q,Rate.add ?_ ((hK _ _ _ (fun _=>c) _ hv (Rate.const c) (by norm_num)).add ((hK _ _ _ _ _ hv (Rate.const c) (by norm_num)).add (hK 2 _ _ _ _ (Rate.const 1) (ConnectedActivityE6.loopBill_rate G L) (by norm_num)))),?_⟩
  · exact ((((((ht.pow 2).mul_left _).mul_right _).mul_left _).mul_left _)).weaken (by push_cast; norm_num)
  exact Eventually.of_forall fun t P h H hv ht b B' Λ hx hβ hΛ hK=> Meadow.rain G _ B.width_pos hc p P ⟨h.trans hp.symm,H.trans hq.symm,hv.trans hE.symm⟩ hx hβ ht hΛ hK
end YM.PhysicalNext.Repeat.Meadow
