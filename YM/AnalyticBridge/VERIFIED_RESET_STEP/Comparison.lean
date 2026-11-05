import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation

/-!
# Price drift in the projection through the real label census

No Lipschitz-along-Q or continuity in field across flags assumed. All
pre-mask left jets charged (not derivatives of a Taylor polynomial). These
producer-side hypotheses must hold on the *same* data as the numerator
identity. Further subsequences only for the continuity test in fixed volume.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Quotes Residual WilsonStartup Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ : ℝ}
    {X : Listing G n}
namespace Source
instance : Sub (Source G n) := ⟨fun v w => ⟨v.logRead - w.logRead, v.hardRead - w.hardRead⟩⟩
end Source

variable {a b : Source G n} {d v w : ℝ}
lemma projection_drift (g : G.Simple) (h : Projects (X.read a) p v) (h' : Projects (X.read b) p w)
    (hd : deviation p (X.read a) (X.read b) d) : p.threshold^2 * |delta (X.read a) - delta (X.read b)| ≤ d := by
  obtain ⟨k,k',hk,-,hkE,-⟩ := hd
  have hf i := reg_sub (h.regular i) (h'.regular i)
  have H : Projects (X.read (a-b)) p d := ⟨hf, k, fun i => (sup_varies (h.regular i) (h'.regular i)).1 (hk i),
    fun o => Cost.mono hkE (fun i => by split; exact hkE.1 i; exact le_rfl) fun i => by split; exact le_rfl; exact hkE.1 i⟩
  convert delta_bound g H using 3
  unfold Averaging.delta Averaging.total; rw [← (h.seriesAt g ..).tsum_sub (h'.seriesAt g ..)]
  apply tsum_congr; intro i
  unfold censusAt; dsimp only [Listing.read]; split
  · exact (projection_sub _ (h.regular i) (h'.regular i) ..).symm
  ring

lemma archive_sub (h : ∀ i, p.Regular (X.reg i).support (a.logRead i)) (h' : ∀ i, p.Regular (X.reg i).support (b.logRead i))
    (R : PathData G) (α Δ Δ' : ℝ) (i : EKey n) : archive X R c a α Δ i - archive X R c b α Δ' i = archive X R c (a-b) 0 (Δ-Δ') i := by
  rcases i with i|⟨z,d⟩|⟨z,d⟩
  · exact (label_sub _ _ p.threshold _ p (h i) (h' i)).1.symm
  · funext V
    change d.fresh R c 0 (factor*Δ) _ - d.fresh R c 0 (factor*Δ') _ = d.fresh R c 0 (factor*(Δ-Δ')) _
    rw [mul_sub]; exact congr_fun (Low.fresh_sub R c d 0 _ _) (z.view _)
  funext V
  change d.fresh R 0 (factor*α) (factor*Δ) _ - d.fresh R 0 (factor*α) (factor*Δ') _ = d.fresh R 0 _ _ _
  rw [mul_zero,mul_sub]; exact (congr_fun (High.fresh_sub R d 0 _ _ _ _) (z.view V)).trans (by rw [sub_self])
lemma throws_sub (h : ∀ i, p.Regular (X.reg i).support (a.logRead i)) (h' : ∀ i, p.Regular (X.reg i).support (b.logRead i))
    (R : PathData G) (α Δ Δ' : ℝ) (i : LKey n) (U) : loses X R c p a α Δ i U - loses X R c p b α Δ' i U = loses X R c p (a-b) 0 (Δ-Δ') i U := by
  rcases i with i|⟨z,d⟩
  · exact congr_fun (label_sub _ _ p.threshold _ p (h i) (h' i)).2.symm U
  exact (Low.loan_sub R c d 0 p (factor*α) (factor*Δ) (factor*α) (factor*Δ') (z.view U)).trans (by simp only [sub_self,loses, Sum.elim_inr,Function.comp_apply,mul_zero,← mul_sub])

lemma E_dominate (i : EKey n) {d α Δ t A e : ℝ} (he : e ≤ d) (hα : |α+Δ| ≤ t*A) (hΔ : |Δ| ≤ t * |v|) (hA : A=|w+v|) :
    quoteE R p c α Δ (fun _ => e) i ≤ (Sum.elim (fun _ => resetLoss G p * d) fun j => t* quoteE R p c w v 0 (.inr j)) i := by
  have ht := turnFee_pos p; have hp := p.threshold_pos
  rcases i with i|⟨z,b⟩|⟨z,b⟩
  · exact mul_le_mul_of_nonneg_left he (loss_pos ..).le
  · exact le_trans (b:= turnFee p * (t* |v| *p.threshold^2) * (|b.mark R c| * lowCost G p (b.length R))) (by
      change turnFee p * (|Δ| * p.threshold^2) * (|b.mark R c| * lowCost G p (b.length R)) ≤ _
      have := low_nonneg G p (b.length R); gcongr) (by dsimp [quoteE]; apply le_of_eq; ring)
  exact le_trans (b:=turnFee p * (t*A*p.threshold^3) * b.price R p) (by
    change turnFee p * (|α+Δ| * p.threshold^3) * _ ≤ _; have := b.price_nn R p; gcongr) (by dsimp [quoteE]; rw [hA]; apply le_of_eq; ring)
lemma L_dominate (i : LKey n) {d α Δ t A e : ℝ} (he : e ≤ d) (hα : |α+Δ| ≤ t*A) (hΔ : |Δ| ≤ t * |v|) (hA : A=|w+v|) :
    quoteL R p c α Δ (fun _ => e) i ≤ (Sum.elim (fun _ => resetLoss G p*d) fun j => t * quoteL R p c w v 0 (.inr j)) i := by
  rcases i with i|⟨z,b⟩
  · exact mul_le_mul_of_nonneg_left he (loss_pos ..).le
  have hp := p.threshold_pos; have hb := pair_nonneg G p
  dsimp [quoteL]; rw [← mul_assoc t]; apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [hA] at hα; unfold hitPower
  linarith only [mul_le_mul_of_nonneg_right hα hp.le, mul_le_mul_of_nonneg_right hΔ (show 0 ≤ pairBill G p * p.threshold^2 by positivity)]

structure Compared (X : Listing G n) (p : BudgetPoint) (a : ℝ → Source G n) (T : Set ℝ) : Prop where
  values : ∀ x∈T, AtEach p (X.read (a x)) (fun y => X.read (a y)) (𝓝[T] x)
  series : ∀ x∈T, Submajorized p (X.read (a x)) (fun y => X.read (a y)) (𝓝[T] x)
namespace Compared
variable {a : ℝ → Source G n} {T : Set ℝ} {H w : ℝ → ℝ}
    (g : G.Simple) (L : ∀ x∈T, Local X p (a x) (H x) (w x)) (h : Compared X p a T)
    (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hw : Width p c σ)
include h
lemma deviation_at {x : ℝ} (he : x∈T) {ε : ℝ} (hε : 0<ε) : ∀ᶠ y in 𝓝[T] x,deviation p (X.read (a x)) (X.read (a y)) ε :=
  deviation_submajorized (F:=fun y => X.read (a y)) (Eventually.of_forall fun _ => rfl) (h.values x he) (h.series x he) hε
include g L in
lemma drifting {x : ℝ} (he : x∈T) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ y in 𝓝[T] x, |delta (X.read (a x))-delta (X.read (a y))| ≤ ε := by
  filter_upwards [self_mem_nhdsWithin,h.deviation_at he (mul_pos (sq_pos_of_pos p.threshold_pos) hε)] with y hy hq
  exact le_of_mul_le_mul_left (projection_drift g (L _ he).projects (L _ hy).projects hq) (sq_pos_of_pos p.threshold_pos)
include g L
include hx hc in
set_option linter.unusedVariables false in
lemma quote_at (α : ℝ) (hn : 20 < n.val) (x : ℝ) (he : x∈T) (ε) (hε : 0<ε) : let Δ y := delta (X.read (a y)); let t y := branch X R c p (a y) α
    ∀ᶠ y in 𝓝[T] x,
    (∀ i, variesRegular p ((shelves X R p).reg i) ((t x).regular i) ((t y).regular i) (ε * quoteE R p c 0 1 (fun _ => 1) (numbering (EKey n) i))) ∧
    (∀ i U, ‖(t x).logarithm i U - (t y).logarithm i U‖ ≤ ε * quoteL R p c 0 1 (fun _ => 1) (numbering (LKey n) i)) := by
  intro Δ t; filter_upwards [h.deviation_at he hε, self_mem_nhdsWithin, h.drifting g L he hε] with y hd hy hq
  obtain ⟨u,_,hu,-,hU,-⟩ := hd
  have hr i := reg_sub ((L x he).smooth i) ((L y hy).smooth i)
  have ht i : p.supBounds (X.reg i).site (X.reg i).support ((a x).logRead i - (a y).logRead i) ε := sup_le
    ((sup_varies ((L x he).smooth i) ((L y hy).smooth i)).1 (hu i)) ((p.loMass _ _ (hu i).1).trans (budget_single hU i))
  have hD : |0+(Δ x - Δ y)| ≤ ε*1 := by simpa only [zero_add,mul_one]
  have hD' : |Δ x-Δ y| ≤ ε* |(1:ℝ)| := by simpa only [abs_one,mul_one]
  constructor
  · intro i
    apply (sup_varies (((L x he).regFamily g hx hc hn α (Δ x)).smooth i) (((L y hy).regFamily g hx hc hn α (Δ y)).smooth i)).2
    change p.supBounds _ _ (archive X R c (a x) _ _ _ - archive X R c (a y) _ _ _) _
    rw [archive_sub ((L _ he).smooth) ((L _ hy).smooth)]
    have H := Local.quote_regular (v:=a x-a y) g hx hc 0 (Δ x-Δ y) (u:=fun _ => ε) ht hr (numbering (EKey n) i)
    exact sup_le H ((E_dominate (R:=R) (p:=p) (c:=c) (numbering (EKey n) i) (w:=0) (le_refl ε) hD hD' (by norm_num)).trans_eq
      (by rcases numbering (EKey n) i with i|d|d <;> dsimp only [quoteE,Sum.elim_inl,Sum.elim_inr] <;> ring))
  intro i U; change ‖loses X R c p (a x) _ _ _ U - loses X R c p (a y) _ _ _ U‖ ≤ _
  rw [throws_sub ((L _ he).smooth) ((L _ hy).smooth)]
  exact (Local.quote_soft (R:=R) (c:=c) (v:=a x-a y) g 0 (Δ x - Δ y) ht hr _ U).trans
    ((L_dominate _ (w:=0) (v:=1) (R:=R) (c:=c) (p:=p) (le_refl ε) hD hD' (by norm_num)).trans_eq (by rcases numbering (LKey n) i with i|d <;> dsimp only [quoteL,Sum.elim_inl,Sum.elim_inr] <;> ring))
end Compared
end YM.AnalyticBridge.VerifiedReset.Collection
