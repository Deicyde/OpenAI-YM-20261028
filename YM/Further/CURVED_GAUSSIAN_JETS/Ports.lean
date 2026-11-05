import YM.Further.CURVED_GAUSSIAN_JETS.Transit

/-!
# Uniform issuance of integral prices, and the address-exact readings
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice Wilson RG Precision Push.Uniform SectorNext.Vacuum Set MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I J : Type*} [Fintype I] [DecidableEq I] {f n c : Side} {a : I → Site n} {b : J → Site f} {s : Jets.Weights a} {t : Jets.Weights b} {P : Prices} {K δ M : ℝ} {q k N : ℕ}

structure Port (P : Prices) (s : Jets.Weights a) (k : ℕ) (M K : ℝ) (N : ℕ) : Prop extends Fuel P s k M K where
  dose : dose_cost P s k M ≤ K
  approxLog : P.deep N < 1
  approxInv : P.error N < 1
  adjLog : qd P s k M N ≤ 1/2
  adjInv : qr P s k M N ≤ 1/2

lemma enroll (P : Prices) (k : ℕ) (s : Jets.Weights a) (hm : 0 ≤ M) : ∃ K : ℝ, 1≤K ∧ ∀ᶠ N in atTop, Port P s k M K N := by
  obtain ⟨h1,h2,h3,h4⟩ := cost_pos P s k hm
  have h := s.pay_pos k
  let X := dose_cost P s k M
  have hx : 0 ≤ X := by have hd := discount_pos P s k hm k; unfold X dose_cost; positivity
  let K := 1+s.pay k*(M+column_cost P s k M+defect_cost P s k M + line_cost P s k M)+X
  have hK : 1≤K := le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right hx)
  refine ⟨K,hK,(q_delay (1/2) (by norm_num)).mono fun N ⟨he,hv,hd,hr⟩=> {
      valid := hm
      one := hK
      base := by unfold K; nlinarith
      column := by unfold K; nlinarith
      defect := by unfold K; nlinarith
      line := by unfold K; nlinarith
      dose := le_add_of_nonneg_left (by positivity)
      approxLog := he
      approxInv := hv
      adjLog := hd.le
      adjInv := hr.le }⟩

lemma Port.use (h : Port P s k M K N) (hv : s.budget=t.budget) : Port P t k M K N := by
  have hp : s.pay k=t.pay k := by unfold Weights.pay; rw [hv]
  have he (j : ℕ) : discount P s k M j = discount P t k M j := by induction j with | zero => rfl | succ j ih=> simp only [discount,wheelCost,hp,ih]
  obtain ⟨⟨hm,hK,hB,hC,hD,hL⟩, hx,hd,hq,ha,hb⟩ := h
  simp only [qr,qd,dose_cost,line_cost,sharp_cost,defect_cost,column_cost,he,hp] at *
  exact ⟨⟨hm,hK,hB,hC,hD,hL⟩, hx,hd,hq,ha,hb⟩
lemma Port.cut (h : Port P s k M K N) (e : J→I) : Port P (s.restrict e) k M K N := h.use rfl

variable {G : Gauge} (W : Windows I)
structure Record (P : Prices) (s : Jets.Weights a) (k N : ℕ) (K : ℝ) (V : Config G c) (A : Jets.Field G c I) (Q : Directions G c→Prop) : Prop where
  full : Fits a P (A V)
  positive : (covariance W A V).PosDef
  precision : Real.log (A V).det = ∑ i,price A P i V
  reference : Real.log (covariance W A V).det = -Real.log (A V).det + ∑ i,Round.onLine (coeff W A V) i
  amounts (i : I) (l : Word G c) : l.length ≤ k → (∀ i∈l,Q i) → ‖leftDerivs (fun v=> W.tollLine (A v) P.mass i) l V‖ ≤ K*s.τ i^l.length
  assemble (l : Word G c) : l.length ≤ k → (∀ i∈l,Q i) → ∀ i j : I,
    leftDerivs (price A P i) l V = leftDerivs (fun v=> W.tollLine (A v) P.mass i) l V - ∑' d,∑ p : Run I (d+2),ends i i p (leftDerivs (mailed W A p) l V) ∧
    leftDerivs (fun v=>Round.onLine (coeff W A v) i) l V = ∑' d,∑ p : Run I (d+1),ends i i p (leftDerivs (pushLog W A p) l V) ∧
    leftDerivs (fun v=> ((covariance W A v)⁻¹-A v) i j) l V = ∑' d,∑ p : Run I (d+2),ends i j p (leftDerivs (pushQuad W A p) l V)
  ship (l : Word G c) : l.length≤k → (∀ i∈l,Q i) → ∀ d (p : Run I (d+2)), leftDerivs (mailed W A p) l V = ∫ u : ℝ in Ioi 0, leftDerivs (sailing W A p u) l V ∧
    IntegrableOn (fun u=> leftDerivs (sailing W A p u) l V) (Ioi 0) ∧ (∫ u : ℝ in Ioi 0, ‖leftDerivs (sailing W A p u) l V‖) ≤ asking s P K N d p l.length ∧
    ‖leftDerivs (mailed W A p) l V‖ ≤ asking s P K N d p l.length ∧ ‖leftDerivs (pushQuad W A p) l V‖ ≤ asking s P K N d p l.length
  certify (l : Word G c) : l.length≤k → (∀ i∈l,Q i) → ∀ d (p : Run I (d+1)), ‖leftDerivs (pushLog W A p) l V‖ ≤ asking s P K N d p l.length
variable {W} {Q : Directions G c→Prop} {A : Jets.Field G c I} {V : Config G c}

theorem Port.read (h : Port P s k M K N) (hv : ∀ᶠ v in 𝓝 V, Street P s k Q A v M) (hb : W.Includes a N) : Record W P s k N K V A Q := by
  have hA := hv.self_of_nhds.base
  obtain ⟨h1,h2⟩ := (true_det W hb h.adjInv hv h.approxInv).self_of_nhds
  have he : Real.log (A V).det = ∑ i,price A P i V := by
    cases isEmpty_or_nonempty I with | inl h => simp | inr h => obtain ⟨i⟩ := h; have hh := Panel.bill_quad hA.symm hA.numeric i; exact Panel.log_form _ hA.symm hA.numeric P.gap_pos (hh.1.trans hh.2)
  refine ⟨hA,h1,he,?_,?_,?_,?_,?_⟩
  · rw [Finset.sum_add_distrib,Finset.sum_neg_distrib] at h2; rwa [he]
  · intro i l hl hd
    have he := (paid_dose (hv.mono (fun v h=> h.slab W i)) hl hd (W.center i)).2.1
    exact he.trans (mul_le_mul_of_nonneg_right (h.cut (W.inside i)).dose (pow_nonneg (s.nonneg i) _))
  · intro l hl hd i j
    obtain ⟨h₁,h₂,h₃⟩ := window_log_error W hb h.adjLog hv (by norm_num : (1/2:ℝ)<1) h.approxLog hl hd i
    have hr := correction_error W hb h.adjInv hv (by norm_num : (1/2:ℝ)<1) hl hd i
    have hq := precision_terms W hb h.adjInv hv (by norm_num : (1/2:ℝ)<1) h.approxInv hl hd i j
    simp_rw [←tail_exact h.toFuel hb hv hl hd, ←log_values h.toFuel hb hv hl hd, ←quad_values h.toFuel hb hv hl hd]
    rw [h₁] at h₂
    refine ⟨?_,hr.1,hq.1⟩; change leftDerivs _ _ _ = leftDerivs (price (slab W A i) P (W.center i)) _ _ -_; linarith only [h₂]
  · intro l hl hd d p
    obtain ⟨h₁,h₂,h₃⟩ := mailed_price h.toFuel hb hv hl hd p
    refine ⟨h₁,h₂,?_,h₃,quad_prices h.toFuel hb hv hl hd p⟩
    have he := sailing_terms hv.self_of_nhds h.toFuel hb p
    exact (integral_mono_ae h₂.norm (Line.bell_int.1.mul_const _) ((ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))).mono (he.major l hl hd))).trans_eq (by rw [integral_mul_const,Line.bell_int.2,one_mul])
  exact fun l hl hd d p=>push_prices h.toFuel hb hv hl hd p
end YM.Further.CurvedGaussianJets.Tracks
