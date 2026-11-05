import YM.AnalyticBridge.VERIFIED_RESET_STEP.Investor
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.RemainderComparison.Lacuna.Vowel

/-!
# Sharper reset adapter. No charging E influence on projection
 from a high-temperature or conformal shell cut here: uses E budgets
 exactly. Keep the Width, from price-passage on same path. Adaptation
 of VerifiedReset.Quotes/Investor (step one for angular stage usually
 obtains +2 E before reset, not +3). Finite but **unbounded** volume costs
 used only to establish qualitative Local equations / motion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Ethereal
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{p : BudgetPoint}

def mid (p:BudgetPoint):= p.supportExponent+2

def foam (G:Gauge)(p:BudgetPoint)(H:ℝ):= Footprint.payment 1 (4*p.B+2) 0 (1/2) (resetLoss G p) H (p.supportExponent+1) 81
abbrev summit (p:BudgetPoint)(X:ℕ→RegularAddress n)(k:ℕ→ℝ)(H:ℝ):=
    Footprint.Anchored (fun i=> (X i).site) k (fun i=>coverNumber p.B (X i).support) (mid p) H

lemma loft (X:ℕ→RegularAddress n) {k:ℕ→ℝ}{H:ℝ}(h:∀ i,0 ≤ k i) (hh: summit p X k H): anchored p X k H:=by
  intro o; refine Cost.mono (hh o) (fun i => ?_) fun i => ?_
  · unfold BudgetPoint.mass; have h := h i; split <;> positivity
  split
  next he => rw [BudgetPoint.mass,mul_comm (k _)]; gcongr
             · exact h i
             unfold mid; linarith
  exact le_rfl

lemma glory (G:Gauge)(X:ℕ→ RegularAddress n) {k:ℕ→ℝ}{H:ℝ}(hB:2≤p.B)(h:∀ i,0 ≤ k i)(hh: summit p X k H): anchored p (enlarges ∘ X) (fun i=> resetLoss G p*k i) (resetFee G p*H) ∧ Ac.Hit (expand ∘ X) p.B (fun i=> resetLoss G p*k i) (p.supportExponent+1) (foam G p H):=by
  have hz := loss_pos G p
  have he := p.exponent_pos
  have ht := loft X h hh
  refine ⟨fun o => ?_,?_⟩
  · refine Cost.mono (Cost.scale (ht o) (resetFee G p) (by unfold resetFee; positivity)) ?_ ?_
    · intro i; split
      · unfold BudgetPoint.mass; have := h i; positivity
      exact le_rfl
    intro i; dsimp [enlarges,BudgetPoint.mass,resetFee]; split
    next _ =>
      have hi := enlarge p (X i) hB; rw [mul_mul_mul_comm, ← Real.exp_add]; gcongr
      · exact mul_nonneg hz.le (h i)
      exact le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hi : (coverNumber p.B (expand (X i)) : ℝ) ≤ coverNumber p.B (X i).support + 81) he.le) (by linarith)
    rw [mul_zero]
  exact Footprint.assigned id 1 (fun Y : Support n => by simp) _ _ h _ _ hh _ 0 _ (fun i x hx => enlarged_dist p _ x hx)
    (fun i => by rw [one_mul,add_comm]; exact_mod_cast enlarge p (X i) hB) hz.le ⟨by linarith,by norm_num,by unfold mid; linarith⟩
    _ (fun i => mul_nonneg hz.le (h i)) (by simp)
lemma slip (p: BudgetPoint)(X: ℕ→ RegularAddress n)(c:ℕ→ℝ){H:ℝ}(h:∀ i,0 ≤ c i)(hh:summit p X c H): ∃ u:ℝ, Quotes.early p X c u:=by
    let d : ℝ:=Real.exp (preExponent p* coverNumber p.B (Finset.univ:Support n)); have he:0 ≤ d:= (Real.exp_pos _).le
    refine ⟨d * H,fun o=> Cost.mono (Cost.scale (hh o) d he) ?_ ?_⟩
    · intro i; split; exact mul_nonneg (h _) (Real.exp_pos _).le; exact le_rfl
    intro i; split_ifs -- D.thest
    next hP=>
      calc _ ≤ c i*d:= by
                  unfold d; gcongr
                  · exact h i
                  · unfold preExponent; linarith [p.exponent_pos]
                  exact Lattice.Corona.cover_mono (Finset.subset_univ _) _
           _ ≤ _:= by
                  rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ he
                  have hp:0≤ mid p:=by unfold mid; linarith [p.exponent_pos]
                  exact le_mul_of_one_le_right (h _) (Real.one_le_exp (mul_nonneg hp (Nat.cast_nonneg _)))
    next=> exact (mul_zero d).symm.le

section Local
variable {R:PathData G}{c:Clip}{σ C Λ A w α Δ :ℝ} {X:Listing G n} {v:Collection.Source G n}
variable (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hw : Width p c σ) (α Δ:ℝ) {u:ℕ→ℝ}
    (h₁:∀ i,p.supBounds (X.reg i).site (X.reg i).support (v.logRead i) (u i))

def ocean (G:Gauge)(p:BudgetPoint)(c:Clip)(σ C α H:ℝ):= foam G p H + hitNeed p G α H * lowHard p c σ C
include h₁ hx hc hw
lemma cruise (hu:summit p X.reg u A)(hΔ:p.threshold^2* |Δ| ≤ A) :
    anchored p (incoming X R p) (quoteE R p c α Δ u) (regularNeed G p c σ C α A) ∧ Ac.Hit (soft X R p) p.B (quoteL R p c α Δ u) (p.supportExponent+1) (ocean G p c σ C α A):=by
  have hC := Cost.nonneg hx.three
  have ⟨he,hk⟩ := glory G X.reg hc.radius (fun i => (h₁ i).1) hu
  obtain ⟨ha,hb,hl⟩ := Quotes.rows (n:=n) G R c p hx hw
  obtain ⟨hL,hH,hD⟩ := budget_pos p G c hx.width hC
  have ht := turnFee_pos p
  have hp := p.threshold_pos
  refine ⟨fun o => Cost.enlarge (Cost.sum (he o) (Cost.sum
    (anchored_scale (r:=turnFee p*(|Δ| * p.threshold^2)) (by positivity) ha o)
    (anchored_scale (r:=turnFee p*(|α+Δ| * p.threshold^3)) (by positivity) hb o))) ?_, fun x => ?_⟩
  · unfold regularNeed; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΔ hL) ht.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (fresh_allow hΔ (α:=α)) hH) ht.le]
  refine Cost.enlarge (Cost.sum (hk x) ((hit_scale (hitPower_pos p G α Δ) hl) x)) ?_
  unfold ocean; exact add_le_add_right (mul_le_mul_of_nonneg_right (hit_allow hΔ) hD) _
end Local
end YM.RemainderComparison.Ethereal
