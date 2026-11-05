import YM.WilsonBulk.Agenda.Awakening
import YM.Push.SECTOR_MEASURE.Gauges

/-! # Geometry numerical requirements -- Uniform allocation over all eligible T and neighbor smoothing

Delays use hatted coupling, not real trajectory shoot; placed by delay heaps after Lit choice. Combine with
other numerical thresholds by max (germ orientation patch unaffected). Part of deliver Land consumer.
Publication theorem with actual schedules additionally delayed invoked later; not proved in this file. α width
may be strengthened with future shields (power E,... etc). Use § Z relation k Ύ so refinement independent of
calendar if kernel penalty changed before. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {F : MapPrices} {i j k n m ℓ N N' E : ℕ} {x a b p σ θ μ w C t δ : ℝ} {L : Side} {P : Patch}
variable {K : KernelChoices} (J : ChartRatio G) (S : Lit G K F) (a : ℝ)

def wise (x : ℝ) := 2+Real.log (Real.log x)
abbrev zAge (A : Levels G) (i : ℕ) := wise (A.clock.hatBeta i)
abbrev Lambda (A : Levels G) (i : ℕ) := 2+Real.log (A.clock.hatBeta i)
lemma tend_ages : Tendsto wise atTop atTop := tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
lemma log_one (he : Real.exp 1 ≤ x) : 1 ≤ Real.log x := (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) he)).2 he
lemma ages_one (he : Real.exp 1 ≤ x) : 1 ≤ wise x := (by norm_num : (1:ℝ)≤2).trans (le_add_of_nonneg_right (Real.log_nonneg (log_one he)))
lemma Lambda_ready (he : Real.exp 1 ≤ x) : wise x ≤ 2+Real.log x := add_le_add_right ((Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (log_one he))).trans (sub_le_self _ zero_le_one)) _
structure Dawn (J : ChartRatio G) (a : ℝ) (S : Lit G K F) (L : ℕ→ Side) (v : ℕ→ℝ) : Prop where
  strong (j : ℕ): Real.exp 1 ≤ v j
  peak i j P (R : Model P K) : Agenda.after i j → P.J=j → P.L=L j → ∀ (e:ℕ), e≤j→ ∀ (b : ℝ),v j ≤ b → postTranche S R J i e a ≤ wise b
lemma allPost (L : ℕ→Side) : ∃ v : ℕ→ℝ,Dawn J a S L v := by
  have hh (P : Patch) (j : ℕ) : ∀ᶠ c:ℝ in atTop, ∀ R:Model P K,∀ i:Fin (j+1),∀ e:Fin (j+1), postTranche S R J i e a ≤ wise c := by
    haveI : Finite (Model P K):= Push.SectorMeasure.finite_forests
    exact eventually_all.mpr (fun R=> eventually_all.mpr fun i=> eventually_all.mpr fun e=> tend_ages.eventually_ge_atTop (postTranche S R J i e a))
  choose V hv hv' using fun j=> (show ∃ x : ℝ,Real.exp 1 ≤ x ∧ ∀ i,Agenda.after i j → ∀ (P:Patch) (R:Model P K), P.J=j → P.L=L j → ∀ e:Fin (j+1), ∀ b≥x, postTranche S R J i e a ≤ wise b from by
    by_cases h : ∃ (P : Patch), P.J=j ∧ P.L=L j; swap
    · refine ⟨_,le_rfl,fun i hi P R hk hp _=>(h ⟨P,hk,hp⟩).elim⟩
    obtain ⟨P,h,hL⟩:= h; obtain ⟨c,hc⟩:= eventually_atTop.mp (hh P j); refine ⟨max c (Real.exp 1), le_max_right .., fun i hi p R hp hP e x hx=>?_⟩; obtain rfl : P=p:= by cases P; cases p; congr <;> aesop
    exact hc x (le_trans (le_max_left ..) hx) R ⟨i,Nat.lt_succ_of_le hi.1⟩ e)
  exact ⟨V,hv,fun i j p R hi hp hP e ht=>hv' j i hi p R hp hP ⟨e,Nat.lt_succ_of_le ht⟩⟩
lemma Dawn.more {L : ℕ→Side} {v v' : ℕ→ℝ} (h : Dawn J a S L v) (he : v ≤ v') : Dawn J a S L v' :=
  ⟨fun i=>(h.strong i).trans (he i), fun i j p R hp hh hx e H b hb=>h.peak i j p R hp hh hx e H b ((he j).trans hb)⟩

lemma hat_mobile (A : Levels G) (hs : G.Simple) (hp : i≤j) : A.clock.hatBeta i ≤ A.clock.hatBeta j:= add_le_add_right (mul_le_mul_of_nonneg_left ((scale_strict A.S).monotone hp) (Gauge.slopeConstant_pos hs).le) _
lemma log_growth (h : x ≤ b) (hp : 1 ≤ x) : Real.log b ≤ Real.log x+(b-x) := by
  have hx := zero_lt_one.trans_le hp; rw [← sub_le_iff_le_add']; rw [← Real.log_div (ne_of_gt (hx.trans_le h)) hx.ne']; apply le_trans (Real.log_le_sub_one_of_pos (div_pos (hx.trans_le h) hx)) ?_
  have hb : b/x-1=(b-x)/x:= by field_simp
  exact hb ▸ div_le_self (sub_nonneg.mpr h) hp
lemma wise_growth {x b : ℝ} (h : x ≤ b) (hp : Real.exp 1 ≤ x) : wise x ≤ wise b ∧ wise b ≤ wise x+(b-x) := by
  have hx := (Real.exp_pos _).trans_le hp; have hc:= log_one hp; have hf := Real.log_le_log hx h; have he : 1≤x:= le_trans (Real.one_le_exp zero_le_one) hp
  refine ⟨add_le_add_right (Real.log_le_log (lt_of_lt_of_le zero_lt_one hc) hf) _,?_⟩
  unfold wise; linarith only [log_growth hf hc, log_growth h he] -- log_growth x≤...
variable (A : Levels G) (hs : G.Simple) (hp : ∀ i, Real.exp 1 ≤ A.clock.hatBeta i)
include hs hp
lemma age_charge (i k : ℕ) (hc : zAge A k ≤ x) : zAge A i ≤ budgetFit (1+G.slopeConstant) 1 (age A.S k x i) := by
  let c:= G.slopeConstant; have ht : 0≤c:= (Gauge.slopeConstant_pos hs).le; obtain h₀:0≤ x:= zero_le_one.trans ((ages_one (hp k)).trans hc)
  rcases le_or_gt i k with H|H
  · have hv:= (wise_growth (hat_mobile A hs H) (hp i)).1; unfold budgetFit; rw [pow_one]; exact hv.trans (hc.trans ((age_ge A.S k x i).trans (le_mul_of_one_le_left (h₀.trans (age_ge ..)) (le_add_of_nonneg_right ht))))
  have hv := (wise_growth (hat_mobile A hs H.le) (hp k)).2
  have ht : A.clock.hatBeta i - A.clock.hatBeta k=c*(A.S.scale i-A.S.scale k):= by unfold Calendar.hatBeta c; ring -- A.S def
  rw [ht] at hv; unfold budgetFit age; have hW : 0≤ A.S.scale i-A.S.scale k:= sub_nonneg.mpr ((scale_strict _).monotone H.le); rw [abs_of_nonneg hW,pow_one]; linarith only [hc,hW,mul_nonneg (show 0≤c from (Gauge.slopeConstant_pos hs).le) h₀,hv]
end YM.WilsonBulk.Parapet.Agenda
