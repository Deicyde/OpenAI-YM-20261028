import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Dredge
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Turret
/-!
# Affine row economy. Receipts on hero labels
Occupancy at true tag budget, exponent ret earnings later. Lower clip not a derivative prescription. Does not bound individual rough row uniformly in c!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Coffer
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x W a e L C : ℝ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S} {t : ℝ}
abbrev noises (v : Dyed G S) (L x:ℝ) := ∀ p:Pilot G S x,Matched p →Barge.Sound x v.source.beta L v.things p.park p.view p.tag p.key v.chi v.arc

lemma watchmen (h : Chips v P W x) (ht : noises v L x) : ∃ b : ℝ,∀ p:Pilot G S x,Matched p → b ≤ (∑ i,dues v i p):= by
  let t:= Fintype.card (Receipt G S); let H : Teller G:=P; let T:=v.things
  have hv:= h.boost.funded
  obtain ⟨b,f',hF,hT⟩:= hv.feeds
  rw [← h.boost.funded.high,h.paths,h.clips] at hF;rw [← hv.low] at hT
  obtain ⟨A,hA⟩ : ∃ A,∀ U, ‖cutR v.source (till x) U‖≤A:= by
    let g (s : Signed) (i : Cell f) := env_crown (n:=f) hF (till x) 1 v.source.p.threshold i;
    exact (env_mean (F:=fun s U=>∑ i,crown v.source.path v.source.clip (till x) 1 v.source.p.threshold (pull s 0 U) i) (fun s=> Envelope.sum _ _ fun i=> Env.along (g s i) ((continuous_pull ..).measurable))).cost
  obtain ⟨B,hB⟩ : ∃ B : ℝ,∀ V : Config G c, ‖Wax.theta T.down T.low S.patch.L.val x (temp x) V‖ ≤ B:= by
    exact (env_mean (F:=fun s V=>∑ i,crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i) (fun s=> Envelope.sum _ _ fun i=> Env.along (env_crown (n:=c) hT (till x) S.patch.L.val (temp x) i) ((continuous_pull ..).measurable))).cost
  let Y:= fun p:Config G c × Config G c=> ∑ i, monetary S p.1 p.2 i
  obtain ⟨C,hC⟩:= (Env.compact (show Continuous Y by unfold Y monetary wire; fun_prop)).cost
  refine ⟨-v.source.beta*(C+(A+B)+(t:ℝ)),fun p hp=>?_⟩
  unfold dues; simp_rw [← mul_sum]
  apply mul_le_mul_of_nonpos_left _ (Left.neg_nonpos_iff.mpr h.beta.le)
  let V:=p.view; let U:= v.top p; let k:= p.tag; let Y':=p.y.1; let A':= p.key; let F:=p.park
  let m:=meanLog p.key p.park T x V p.tag v.chi v.arc Y'; let q:=p.y.2
  let Q (z:Prices G (Active A' x F)):= Rows.guide T x V k (shots S x) A' F v.chi v.arc Y' z; let a:=v.combo p (coupling v.source.beta)
  have hm : 0≤ Q a:= by unfold Q Rows.guide;apply div_nonneg _ (by norm_num); exact Finset.sum_nonneg fun i _=>mul_self_nonneg _
  have hh : Q m ≤ t := by
    unfold Q Rows.guide dotProduct
    apply le_trans (b:=((∑ _j: Receipt G S,(1:ℝ)) /2))
    · let F₁:=direct T x V k (shots S x) A' F v.chi v.arc Y' m
      change (∑ i,F₁ i*F₁ i)/2 ≤ _ ; refine div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i hi=>?_)) zero_le_two
      have hv : |F₁ i| ≤ 1 := (ht p hp).rows Y' i; rw [← sq]
      rw [← sq_abs]; nlinarith only [abs_nonneg (F₁ i),hv]
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one]; exact half_le_self (Nat.cast_nonneg _)
  have hY : Y (S.prediction U k,V) ≤ C := (le_abs_self _).trans (hC _)
  have hZ: -Wax.theta T.down T.low S.patch.L.val x (temp x) V ≤B:= by convert le_trans (neg_le_abs _) (hB V)
  have hR : cutR v.source (till x) U ≤ A := (le_abs_self _).trans (hA U)
  unfold Dyed.combo; rw [show Aff.weight*_=_ from v.charge_eq hv h.paths h.clips p]
  change Y (S.prediction U k,V)+(cutR _ _ _-Wax.theta T.down T.low S.patch.L.val x (temp x) V) - Q a + Q m ≤ C+(A+B) + _
  linarith only [hR,hm,hh,hY,hZ]
lemma ranked (h: Chips v P W x) (hp : 100*(1+radiusB x)≤c.val) (hA : Hefts S P x L t a W) (he : v.source.p.threshold=t)
    (hw : v.arc=L*fiery G x S.patch.L) (hy : Matched p) (hv : v.Playing W p) (i:Core S x) (hi : i∈owners p.key x) : center i v p ≤ -(v.source.beta*(a*t^2))*i.val.shares:= by
  let z:=v.combo p (coupling v.source.beta)
  obtain ⟨h₁,h₂,h₃⟩:=v.participates W h.heated h.lives p hy hv
  have ht: doors v.chi v.arc (tape z) ≠0 := h₃
  rw [← heavy] at h₁ h₂; rw [hw] at ht
  have hm:= hA.earns v.things h.boost.funded hp p.key p.park i.val _ (pack hi) (by omega) p.view p.y.1 p.tag v.chi z h₁ h₂ ht; rw [← hw] at hm
  unfold center dues; simp_rw [← mul_sum]; rw [he]
  apply (mul_le_mul_of_nonpos_left hm (Left.neg_nonpos_iff.mpr h.beta.le)).trans_eq; ring

lemma margin (P : Teller G) (D : Patch) (he : D.Branches P.bind G) (C : ℝ) (_hc : 0≤C) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (v : Dyed G S), S.patch=D → ∀ (W : ℝ), Chips v P W x →
    100*(1+radiusB x)≤ c.val → Bid.Larger (G:=G) S → ∀ H K, Aff.Alongside H K v.things →
    v.source.beta ≤4*x → v.arc≤ C*fiery G x D.L → fiery G x D.L/2 ≤ v.source.p.threshold →
    ∀ i p,Matched p → v.Playing W p → |lapse v i (p:Pilot G S x)|≤ (4*Aff.weight)*x^(-(1/4):ℝ) :=by
  filter_upwards [till_rate P D he, Rates.grow G D (2*C) (by omega : 0<7) 1,eventually_gt_atTop (0:ℝ)] with x hx hb h c f S v hv W hp ht hD H K hH hh hω h₁ i p he hv'
  have hC:= Aff.weight_pos
  unfold lapse; split; next => rw [abs_zero]; positivity
  next hl =>
    obtain ⟨hQ,hU,hE⟩:= v.participates W hp.heated hp.lives p he hv'
    let z:=v.combo p (coupling v.source.beta)
    have hl : ∀ j:Active p.key x p.park,‖tape z j‖≤Rates.allowance G D x 1 7:= by
      intro j
      apply (broad_span v.chi hp.arc_pos (tape z j) (every_door _ hE j)).le.trans
      simp [Rates.pieces,Rates.allowance] at hb ⊢; linarith only [hb,hω]
    have ht:= hx S v.things hv hp.boost.funded hD p.key p.view (show Aff.cert S x p.key p.view from ⟨ht,he⟩) H K hH p.park p.tag v.chi v.arc p.y.1 v.source.p.threshold z W ((heavy ..) ▸ hQ) hl (hv.symm ▸ h₁) i
      (show grantPlace S i∉p.key.dome (100*radiusB x) from fun hj=> ‹i∉_› (mem_filter.mpr ⟨mem_univ _,Aff.placed _ (100*radiusB x) (200*radiusB x) (by omega) hj⟩))
    unfold dues; rw [abs_mul,abs_neg,abs_of_nonneg hp.beta.le,abs_mul,abs_of_nonneg hC.le]; apply (mul_le_mul hh (mul_le_mul_of_nonneg_left ht hC.le) (mul_nonneg hC.le (abs_nonneg _)) (by positivity)).trans_eq
    rw [mul_assoc, mul_left_comm x, ← mul_assoc]; congr 1; nth_rw 1 [←Real.rpow_one x]; rw [←Real.rpow_add h]; norm_num
lemma minimum (h: Chips v P W x) {u : ℝ} (ha : 0≤a) (hp : 100*(1+radiusB x)≤c.val) (hA : Hefts S P x L t a W) (he : v.source.p.threshold=t)
    (hw : v.arc=L*fiery G x S.patch.L) (ht : noises v u x) (hL : ∀ i p,Matched p → v.Playing W p → |lapse v i (p:Pilot G S x)| ≤ C) : ∃ b : ℝ, ∀ (p:Pilot G S x),Matched p → v.Playing W p → ∀ i∈owners p.key x,b ≤ center i v p:= by
  obtain ⟨y,H⟩:=watchmen h ht; let B:= (Fintype.card (Grain S):ℝ)* C
  refine ⟨y-B, fun p hx hv i hi=>?_⟩
  have hh (j : Core S x) (hp':j∈owners p.key x): center j v p≤0:= (ranked h hp hA he hw hx hv j hp').trans (mul_nonpos_of_nonpos_of_nonneg (Left.neg_nonpos_iff.mpr (mul_nonneg h.beta.le (mul_nonneg ha (sq_nonneg _)))) (by positivity))
  have hl:penury v p ≤ B:= (sum_le_sum (g:=fun _=>C) (fun j _=> (le_abs_self _).trans (hL j p hx hv))).trans_eq (by simp [B])
  have hr : -(center i v p) ≤ ∑ j∈owners p.key x,-center j v p:= Finset.single_le_sum (fun j hj=> Left.nonneg_neg_iff.mpr (hh j hj)) hi
  rw [Finset.sum_neg_distrib] at hr; linarith only [hr,hl,reindex v p,H p hx]
end YM.PhysicalNext.InteractingRank.Pump.Coffer
