import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Recite
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Tickets

/-! # Pullback payment for a predicted E direction through held-Z log tables

All orders, including reanchoring for winding support when taking actual
sensitivities separately per argument (even then, D & Γ remain on the
whole read-set). No index-commutation of derivative tensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Metric Lattice Wilson Pressure RG Tree Next Next.Fluctuations Next.SectorChange
   Exterior Bloch Bid AnalyticBridge.SectorAffine.Offset Push.Uniform Planned.AtomRegular
open WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {o p : Site c} {r l n j : ℕ}
    {C u t Q ε H : ℝ}
section propagation
variable {E F J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup J] [NormedSpace ℝ J]
    {f : E → F} {L : E →L[ℝ] F} {g : J → E}
lemma sterile (L : E →L[ℝ] F) (x : E) (hn : 2 ≤ j) : iteratedFDeriv ℝ j L x=0 := by
  rcases j with _|j
  · omega
  rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]; simp_rw [L.fderiv, iteratedFDeriv_const_of_ne (n:=j) (by omega),Pi.zero_apply]; exact (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.map_zero

abbrev clinicFee (n : ℕ) (C : ℝ) := (1+patterns n)*(2*C)
lemma clinicFee_le (n : ℕ) (hC : 0 ≤ C) : 2*C ≤ clinicFee n C := le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_right (patterns_nonneg n))

lemma Portrait.propagate (hf : Portrait f L n ε t Q) (hn : 2 ≤ n) (hg : ‖g 0‖ ≤ u) (hQ : 0 ≤ Q) (hε : ε ≤ u) (hu : u ≤ 1) (ht : u ≤ t) (hd : ContDiffAt ℝ (n:ℕ∞ω) g 0)
    (hH : 0≤H) (he : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ v : Fin j → J, (∀ i, ‖v i‖ ≤ 1) → ‖iteratedFDeriv ℝ j g 0 v‖ ≤ u^j*H^j)
    (hj : j ≤ n) (v : Fin j → J) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (f ∘ g) 0 v-L (iteratedFDeriv ℝ j g 0 v)‖ ≤ clinicFee n Q * u^2 * H^j := by
  let f' := f-(⇑L)
  have h0 := hg.trans ht; have h₀ := (norm_nonneg _).trans hg
  have hx := (hf.uniform (g 0) h0).smooth
  have hx' : ContDiffAt ℝ n f' (g 0) := hx.sub L.contDiff.contDiffAt
  have h := show (j:ℕ∞ω) ≤ n from Nat.cast_le.mpr hj
  have hfg : iteratedFDeriv ℝ j (f' ∘ g) 0 v = iteratedFDeriv ℝ j (f ∘ g) 0 v-L (iteratedFDeriv ℝ j g 0 v) := by
    rw [show f' ∘ g=f ∘ g - (L ∘ g) from rfl,iteratedFDeriv_sub_apply ((hx.comp 0 hd).of_le h) ((L.contDiff.contDiffAt.comp 0 hd).of_le h),L.iteratedFDeriv_comp_left hd h]
    rfl
  by_cases hi : j=0
  · subst hi; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply,pow_zero,mul_one,comp_apply]; refine (hf.zeroth_charge hn hg ht).trans ?_
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε hQ) h₀
    nlinarith only [mul_le_mul_of_nonneg_right (clinicFee_le n hQ) (sq_nonneg u),hh]
  rw [← hfg, iteratedFDeriv_comp hx' hd h, FormalMultilinearSeries.taylorComp, sum_apply]
  let M := 2*Q*u^2*H^j
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => M) (fun p _ => ?_)).trans ?_)
  · let w (i : Fin p.length) := iteratedFDeriv ℝ (p.partSize i) g 0 (v ∘ p.emb i)
    have hw (i) := he _ (p.partSize_pos i) ((p.partSize_le i).trans hj) _ (show ∀ k, ‖(v ∘ p.emb i) k‖ ≤ 1 from fun _ => hv _)
    let m := p.length; have hm : 0 < m := p.length_pos (Nat.pos_of_ne_zero hi)
    have hf' (j) (hj : j ≤ n) := iteratedFDeriv_sub_apply (i:=j) (hx.of_le (Nat.cast_le.mpr hj)) L.contDiff.contDiffAt
    change ‖iteratedFDeriv ℝ m f' (g 0) w‖ ≤ M
    have hprod : ∏ i, ‖w i‖ ≤ u^j*H^j := by
      have he : ∑ i,p.partSize i=j := by simpa using p.sum_sigma_eq_sum (fun _ => (1:ℕ))
      apply (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hw i)).trans_eq
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,he]
    have ht : u^j ≤ u := pow_le_of_le_one h₀ hu hi
    by_cases h1 : m=1
    · have hF : ‖iteratedFDeriv ℝ m f' (g 0)‖ ≤ 2*Q*u := by
        rw [h1,norm_iteratedFDeriv_one]; unfold f'; rw [fderiv_sub (hx.differentiableAt (by exact_mod_cast (show n ≠ 0 by omega))) L.differentiableAt,L.fderiv]; apply (hf.first_charge hn h0).trans
        nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hε hg) hQ]
      refine ((iteratedFDeriv ℝ m f' (g 0)).le_opNorm _).trans ((mul_le_mul hF (hprod.trans (mul_le_mul_of_nonneg_right ht (pow_nonneg hH _))) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)).trans_eq (by unfold M; ring))
    have hF : ‖iteratedFDeriv ℝ m f' (g 0)‖ ≤ 2*Q := by
      unfold f'; rw [hf' _ (p.length_le.trans hj),sterile _ _ (by omega),sub_zero]; exact ((hf.uniform _ h0).pay _ (p.length_le.trans hj)).trans (by linarith)
    exact ((iteratedFDeriv ℝ m f' (g 0)).le_opNorm _).trans ((mul_le_mul hF (hprod.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one h₀ hu (lt_of_lt_of_le (show 1 < m by omega) p.length_le)) (pow_nonneg hH _))) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)).trans_eq (by unfold M; ring))
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; refine le_trans (b:=(1+patterns n)*M) (mul_le_mul_of_nonneg_right ((card_le_patterns hj).trans (le_add_of_nonneg_left zero_le_one)) (by unfold M; positivity)) (le_of_eq ?_)
  unfold clinicFee M; ring
end propagation

variable {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {x : ℝ} {P : BudgetPoint} {V : Config G c} {g : Site c → G.El} {k : S.Choices} {A : Slab G c l} {w : Directions G f}

abbrev enters (V : Config G c) (o : Site c) (r : ℕ) (g : Site c → G.El) (A : Slab G c l) (w : Directions G f) (z) := ((launch V o r g A z),w)
abbrev converses (V : Config G c) (o : Site c) (r : ℕ) (g : Site c → G.El) (A : Slab G c l) (w : Directions G f) (z) := (enters V o r g A w z,enters V o r g A w 0)
variable (hT : Canvas P o r V g n C)
include hT
lemma readyEnter : ContDiffAt ℝ n (enters V o r g A w) 0 := (hT.ready _).prodMk contDiffAt_const
lemma readyConverse : ContDiffAt ℝ n (converses V o r g A w) 0 := (readyEnter hT).prodMk contDiffAt_const
lemma enter_pos (hj : j ≤ n) (h₀ : 1 ≤ j) (v : Fin j → Panels l) :
    iteratedFDeriv ℝ j (enters V o r g A w) 0 v=(iteratedFDeriv ℝ j (launch V o r g A) 0 v,0) := by
  rw [iteratedFDeriv_prodMk (hT.ready _) contDiffAt_const (Nat.cast_le.mpr hj),iteratedFDeriv_const_of_ne (by omega)]
  rfl
lemma converse_pos (hj : j ≤ n) (h₀ : 1 ≤ j) (v : Fin j → Panels l) :
    iteratedFDeriv ℝ j (converses V o r g A w) 0 v=((iteratedFDeriv ℝ j (launch V o r g A) 0 v,0),0) := by
  rw [iteratedFDeriv_prodMk (readyEnter hT) contDiffAt_const (Nat.cast_le.mpr hj),iteratedFDeriv_const_of_ne (by omega)]
  change (iteratedFDeriv ℝ j (enters V o r g A w) 0 v,0)=_; rw [enter_pos hT hj h₀]

variable (hA : Act T F x k n t Q) (ht : P.threshold=temp x) (hn : 2 ≤ n) (h : ∀ i, P.dirBound p (A i)) (hC : 1 ≤ C) (hl : l ≤ n)
    (hQ : 1≤Q) (hu : loom P r C ≤ 1) (hL : loom P r C ≤ t) (hw : ‖w‖ ≤ loom P r C)
include hA ht hn h hC hl hQ hu hL hw
lemma timesEnter (sw : Bool) : let s := enters V o r g A w; let Φ := display T F x k sw
    ContDiffAt ℝ n (Φ ∘ s) 0 ∧ ∀ j ≤ n, ∀ v : Fin j → Panels l, (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ j (Φ ∘ s) 0 v-mainStroke T F sw (iteratedFDeriv ℝ j s 0 v)‖ ≤ clinicFee n Q * (loom P r C)^2 * (spine P.power o p)^j := by
  intro s Φ
  have hs : ‖s 0‖ ≤ loom P r C := max_le ((congrArg (‖·‖) (launch_zero A)).trans_le (hT.paid hC)) hw
  refine ⟨(((hA.costs sw).uniform _ (hs.trans hL)).smooth).comp 0 (readyEnter hT),fun j hj v hv => (hA.costs sw).propagate hn hs (by positivity) ?_ hu hL (readyEnter hT) (spine_pos ..).le
    (fun j hj hk v hv => ?_) hj v hv⟩
  · unfold loom; rw [←ht]; have := P.threshold_pos; exact le_trans (le_mul_of_one_le_left (by positivity) hC) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by simp)))
  unfold s; rw [enter_pos hT hk hj v]; exact max_le (hT.cost h hC hl hk hj v hv) ((norm_zero).le.trans ((norm_nonneg _).trans (hT.cost h hC hl hk hj v hv)))
lemma timesEcho : let s := converses V o r g A w; let Φ := echo T F x k
    ContDiffAt ℝ n (Φ ∘ s) 0 ∧ ∀ j > 0, j ≤ n → ∀ v : Fin j → Panels l, (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ j (Φ ∘ s) 0 v-woody T F (iteratedFDeriv ℝ j (launch V o r g A) 0 v)‖ ≤ clinicFee n Q * (loom P r C)^2 * (spine P.power o p)^j := by
  intro s Φ
  have he : ‖enters V o r g A w 0‖ ≤ loom P r C := max_le ((congrArg (‖·‖) (launch_zero A)).trans_le (hT.paid hC)) hw
  have hs : ‖s 0‖ ≤ loom P r C := max_le he he
  have h₀ : 0 ≤ loom P r C := (norm_nonneg _).trans he
  have h₁ := spine_pos P.power o p
  refine ⟨(hA.calibrated.uniform _ (hs.trans hL)).smooth.comp 0 (readyConverse hT),fun j hj hj' v hv => ?_⟩
  have ht := hA.calibrated.propagate hn hs (by positivity) ?_ hu hL (readyConverse hT) h₁.le (fun j hj hk v hv => ?_) hj' v hv
  rotate_left
  · unfold loom; rw [← ‹P.threshold=temp x›]; have := P.threshold_pos; exact le_trans (le_mul_of_one_le_left (by positivity) hC) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by simp)))
  · rw [converse_pos hT hk hj v]; exact max_le (max_le (hT.cost h hC hl hk hj v hv) (by rw [norm_zero]; positivity)) (by rw [norm_zero]; positivity)
  rw [converse_pos hT hj' hj v, realStroke, mainStroke,if_neg Bool.false_ne_true] at ht
  simpa using! ht
end YM.PhysicalNext.JointLoad.Heir
