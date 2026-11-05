import YM.Next.RANK.Ratios

/-!
# Explicit large L budget conditions

Dilation & all forward charges, including cumulative real mask transfers,
consume only pre-L costs *subject* to growing L IN those stages. This is
not saying that the producers above can in fact work with such a plan. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {ξ : Purse}
private lemma tall (u L b : ℝ) (hb : 0≤b) (hu : 1 ≤ u) (hL : 1<L) (h : 2 * Real.log u*(b+2) ≤ Real.log L) :
    ∀ᶠ s in atTop,u^ (Station.bump L b s) ≤ Perch.bill 1 s:= by
  have he : 0 ≤ Real.log u:=Real.log_nonneg hu; have hx : 0< Real.log L:=Real.log_pos hL
  filter_upwards [boil_rate.eventually_ge_atTop (2*Real.log u)] with s hs
  let X:=bump L b s; let f : ℝ:= boil s; have hf : 0≤f:=boil_pos _
  have hm : (X:ℝ)< (b+2)*f/Real.log L+1:= by
    have hp : Real.log ((P s)^b*(P s)^2)=(b+2)*f:= by unfold P; rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (Real.exp_pos _),Real.log_pow,Real.log_exp];push_cast;unfold f boil y; ring
    unfold X bump want; rw [hp]; exact Nat.ceil_lt_add_one (by positivity)
  have hp : (X:ℝ)*Real.log u ≤ f:= by
    have hh := mul_le_mul_of_nonneg_right hm.le he; rw [add_mul,div_mul_eq_mul_div,one_mul] at hh
    have hv : (b+2)*f* Real.log u / Real.log L ≤ f/2:= by apply (div_le_iff₀ hx).2;linarith only [mul_le_mul_of_nonneg_left h hf]
    change 2*Real.log u ≤ f at hs; linarith only [hh,hv,hs]
  rw [← show Real.exp (Real.log u)=u from Real.exp_log (by linarith), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr; rw [mul_one]; exact hp
structure Digits (p : Purse) (L : ℝ) : Prop where
  band : 0 ≤ p.band
  large : 1 < L
  α : 2* Real.log (p.race)*(p.band+2) ≤ Real.log L
  two : 2*Real.log (crest p.L (2*p.taylor))*(p.band+2) ≤ Real.log L
  one : 2 * Real.log (crest p.L p.taylor)*(p.band+2) ≤ Real.log L

def stipend (A : Stage) (ξ : Purse) :=
  A.supportExponent ≤ load ξ.era ∧ ξ.era.coast.a ≤ A.clip.linear/20 ∧ ξ.taylor+1 ≤ A.order
/-- at fixed stage, any larger L can pay (assuming ξ itself set
before L). -/
theorem pulse_ok (P : Purse) (h : 0 ≤ P.band) : ∀ᶠ L in atTop, Digits P L:= by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log P.race*(P.band+2)), Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log (crest P.L (2*P.taylor))*(P.band+2)), Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log (crest P.L P.taylor)*(P.band+2)),eventually_gt_atTop 1] with L hQ ht hv hm; exact ⟨h,hm,hQ,ht,hv⟩
private lemma rails (L : ℝ) (h : Digits ξ L) : ∀ᶠ s in atTop,(Station.bump L ξ.band s:ℝ) ≤ Perch.bill 1 s:= by
  let c:= L; let t:=ξ.band
  have hb:(0:ℝ)≤ t:=h.band
  let a:= Real.log L; have ha:0<a:=Real.log_pos h.large;let d:= (t+2)/a+1; have hd:0 ≤ d:= by unfold d; positivity
  filter_upwards [((isLittleO_pow_exp_pos_mul_atTop 1 (zero_lt_one' ℝ)).const_mul_left d|>.comp_tendsto boil_rate).def zero_lt_one,boil_rate.eventually_ge_atTop 1] with s hs ht
  let z:= bump L t s; let f:=boil s; have he:0≤f:=boil_pos s
  have hv : Real.log ((P s)^t*(P s)^2) =(t+2)*f:= by unfold P; rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (Real.exp_pos _),Real.log_pow,Real.log_exp];push_cast;unfold f boil y; ring
  have hp : (z:ℝ)< (t+2)*f/a+1:= by unfold z bump want; rw [hv]; exact Nat.ceil_lt_add_one (by positivity)
  change ‖d*(f^1)‖ ≤ 1*‖Real.exp (1*f)‖ at hs
  apply hp.le.trans; change _ ≤ Real.exp (f*1); simp only [mul_one,one_mul,pow_one] at hs ⊢
  rw [Real.norm_of_nonneg (mul_nonneg hd he),Real.norm_of_nonneg (Real.exp_pos _).le] at hs
  unfold d at hs; rw [add_mul,one_mul,div_mul_eq_mul_div] at hs; linarith only [hs,ht]

lemma racetrack (L : ℝ) (h : Digits ξ L) : ∀ᶠ s in atTop, Racer ξ s (Station.bump L ξ.band s):= by
  filter_upwards [tall _ _ _ h.band ξ.running h.large h.α, tall _ _ _ h.band (pay_crest ξ.loan _) h.large h.one,tall _ _ _ h.band (pay_crest ξ.loan _) h.large h.two,
    absorb (2*ξ.credit+2) (2*ξ.credit+3) (by linarith) 2, rails L h] with s he hT hQ hy hz
  refine ⟨he,hT,hQ,?_,hz⟩; unfold Purse.ledger Purse.principal Purse.double; apply le_trans _ hy; simp only [pow_two]; simp_rw [overlap]
  rw [show ξ.credit+1+ (ξ.credit+1)=2*ξ.credit+2 by ring]; have hp : ξ.credit+ξ.credit+1 ≤ 2*ξ.credit+2:= by linarith only
  linarith only [Glimmer.billed s hp]
end YM.Next.Rank.Tapes
