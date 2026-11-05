import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Grotto
/-! # Coat dictionaries non-smooth along mask boundaries. Keep ALL real fields/flags fixed in exposure.
 Translation through inverse covariance(Air) must absorb normalizer variation separately from this bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open AnalyticBridge VerifiedReset Quotes Extra.Iteration
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ} {x d μ C : ℝ} {F : Forest S.ratio}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R : RG.Rep G f} (H : Cash W x μ L Q o C T R)

lemma pertinent : Summable H.fair := by
  let r := (Sum.inl : ℕ → Alphabet c f); let s i:= Reserves.tariff H.opt (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε (r i); let p:=radiusB x
  have ht : Ac.Hit (forcedFoot S.ratio Q.halo p R) p s Q.relative (Q.goal L x) := fun i=> budget_pull r Sum.inl_injective (H.fares.hit i)
  have hh:= Q.usable; have hp : 0 ≤ Q.relative:= by unfold Target.relative; have := Q.bound; have := Q.pos; positivity
  have he i : H.v i ≤ s i:= by
    have h:= H.armed.extra (r i); unfold s Reserves.tariff; exact le_mul_of_one_le_right (H.earns (r i)) (Real.one_le_exp (by positivity))
  have hy i : 0 ≤ s i:= (H.earns (r i)).trans (he i)
  have hq (i:ℕ) : (forcedFoot S.ratio Q.halo p R i).Nonempty := by
    let P:= R.activities.forced i; obtain ⟨j,h⟩:= P.inventory_ne; exact ⟨S.ratio.parent j,halo_subset _ _ (mem_image_of_mem _ (show j∈ RG.inspected P.support from mem_union_left _ (P.inventory_sup h)))⟩
  have hx := (AbsoluteSums.Product.everyone_ne (w:=s) _ _ hy (fun i _=>hq i) ht).2.1
  have hA : Summable H.v:= hx.of_nonneg_of_le (fun i=> H.earns (r i)) (fun i=> (he i).trans (le_mul_of_one_le_right (hy _) (Real.one_le_exp (by positivity))))
  exact (HasSum.sum (f:=H.fair) (hasSum_fintype (fun i:Stores S=>H.fair (.inl i))) (HasSum.sum (f:=H.fair ∘ Sum.inr) hA.hasSum (HasSum.sum (f:= (H.fair ∘ Sum.inr) ∘ Sum.inr) (log_ext H).hasSum (hasSum_fintype (fun _i:WarningAt c f=>topStorm S.patch))))).summable

include H
theorem hingeFare : ∃ K:ℝ,0 ≤ K ∧ ∀ (I : RG.Rep G f) (a b : ℕ→ℝ) (t : ℝ), Equalized Q.table R I a b t→ t ≤ 1 → ∃ f' : LogIndex c f→ ℝ, SumBudget f' (t*K) ∧ ∀ (F:Forest S.ratio) (X:Coat T F), X.width=o.K → X.x=x → X.manifest → ∀ z:Air f G, ∀ i : LogIndex c f,
    |X.raiseAir I o.a Q.table (low R I • z) i-X.raiseAir R o.a Q.table z i|≤ f' i := by
  let w:= H.w; let k := ∑' i, w i; have hn i : 0≤ w i:= H.fair_price (Sum.inr (Sum.inr (Sum.inl i))); have hk:SumBudget w k:=⟨hn,log_ext H,le_rfl⟩; have hK:0 ≤ k:= tsum_nonneg hn
  let v:= k+k+1; refine ⟨Real.exp v * (k+1),by positivity,?_⟩; intro I a b t hp hx
  let P:= films c f a; have hV : SumBudget P t:= filmed hp.ae; let f' i:= t*w i+ P i
  have ht:= hp.fund_pos; have he : SumBudget f' (t*k+t):= budget_plus (budget_scale ht hk) hV
  refine ⟨fun i=> Real.exp v*f' i,budget_loosen (budget_scale (Real.exp_nonneg _) he) (le_of_eq (by ring)),?_⟩; intro F X hX hy h z i
  let L:= low R I; let A:= X.farLog I o.a Q.table (L • z) i; let B:=X.farLog R o.a Q.table z i
  have hhB : |B| ≤ w i:= (H.quotes F X hy hX h|>.2.1 i z).1
  have hB := ((le_abs_self _).trans hhB).trans (budget_single hk i)
  have hc : |A-B| ≤ f' i:= by
    by_cases hv:oldVac c f i
    · unfold A B; rw [flitter o.a hp.toFacing _ X z i hv]; split_ifs
      · change |L^2*B-B| ≤ _; rw [← sub_one_mul,abs_mul]; exact (mul_le_mul hp.heat hhB (abs_nonneg _) ht).trans (le_add_of_nonneg_right (hV.1 _))
      rw [one_mul,sub_self, abs_zero]; exact he.1 _
    unfold oldVac at hv; push Not at hv; obtain ⟨j,hj⟩:=hv
    unfold A B; rw [hj]
    let u:= X.liftA R.beta z; let T':=X.input u; let V := X.plaza (Raw.space T 0 X.B R (.inl j))
    change |-I.activities.regularOccurrence I.p j (X.input (X.liftA I.beta (L • z)))*X.enforce _ _ (X.plaza (Raw.space T 0 X.B I (.inl j)))- -R.activities.regularOccurrence R.p j T' * X.enforce _ _ V|≤ _
    unfold L; rw [lifting hp.toFacing,← location hp.toFacing, ← sub_mul,abs_mul,neg_sub_neg,abs_of_nonneg (X.conserve ..).1]; apply (mul_le_of_le_one_right (abs_nonneg _) (X.conserve ..).2).trans
    exact (hp.high j (X.input (X.liftA R.beta z))).trans (le_add_of_nonneg_left (mul_nonneg ht (hn _)))
  have h : A≤v:= by
    unfold v; linarith only [hB, (abs_le.mp (hc.trans (budget_single he i))).2, mul_le_of_le_one_left hK hx, hx]
  change |Real.exp A-1-(Real.exp B-1)|≤ _; rw [sub_sub_sub_cancel_right]; apply (ponds A B v h (by unfold v; linarith only [hK,hB])).trans; exact mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
variable (h: Covers T x H)
include h
lemma cornice : ∃ K : ℝ, 0 ≤ K ∧ ∀ (I : RG.Rep G f) (a b : ℕ→ℝ) (t:ℝ), Equalized Q.table R I a b t→ t ≤ 1 → t ≤ R.beta/2 → ∃ w : Head S→ℝ, SumBudget w (K*t) ∧∀ (F:Forest S.ratio) (X:Coat T F), X.width=o.K → X.x=x → X.manifest → ∀ l:Finset ℕ, ∀ i:Head S, ∀ z,
    |X.vertex I Q.table W o.a l Q.halo (low R I • z) i-X.vertex R Q.table W o.a l Q.halo z i| ≤ w i := by
  obtain ⟨A,hA,hY⟩:=h; obtain ⟨B,hB,H'⟩:= hingeFare H; let n:ℝ:= Fintype.card (Stores S); have hn:0≤n:=Nat.cast_nonneg _
  refine ⟨n*A+(1+(B+0)),by positivity,?_⟩; intro I a b t hp he ht; let L:= low R I
  obtain ⟨f',hf,H⟩:= H' I a b t hp he
  let Y : Head S→ℝ:= Sum.elim (fun _=> A*t) (Sum.elim b (Sum.elim f' (fun _=>0)))
  have hg : SumBudget (fun _:Stores S=> A*t) (n*(A*t)):= Cost.finite _ (mul_nonneg hA hp.fund_pos)
  have hy : SumBudget Y (n*(A*t)+(t+(t*B+0))) := Cost.sum hg (Cost.sum hp.aw (Cost.sum hf (by simp [SumBudget,Y])))
  refine ⟨Y,budget_loosen hy (le_of_eq (by ring)),?_⟩; intro F X hx hv hm l i z
  unfold vertex; simp only [lifting hp.toFacing]; rcases i with i|i|i|i<;> simp only [Sum.elim,Y]
  · split
    · exact hY F X hx hv hm I a b t hp he ht _ i l
    rw [sub_self,abs_zero]; exact mul_nonneg hA hp.fund_pos
  · unfold bag; rw [← pointed hp.toFacing, ← sub_mul,abs_mul,abs_of_nonneg (X.conserve ..).1]
    apply (mul_le_of_le_one_right (abs_nonneg _) (X.conserve ..).2).trans; rw [abs_sub_comm]; exact hp.soft ..
  · exact H F X hx hv hm ..
  nth_rw 1 [← lifting hp.toFacing X z]; rw [← alarmLace o.a W hp.toFacing, sub_self, abs_zero]
end YM.PhysicalNext.Repeat.Alabaster
