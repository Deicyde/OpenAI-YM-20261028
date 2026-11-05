import YM.UVExtension.Yard.Coat
import YM.UVExtension.Guild.Bonnet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Yard
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Finset Pressure
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration WilsonStartup Residual Averaging Geo
open Lamppost Concert ConnectedActivityE6 Guild Payroll
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge}{ξ ε : ℝ}

-- constant theta chosen before L. Counting orientation already inside credit.
def basisB : ℝ := 2*wage^(Fintype.card AxisK)
lemma basis_pos:0≤ basisB:= by unfold basisB; exact mul_nonneg (by norm_num) (pow_nonneg (show 0≤wage from zero_le_one.trans (luck_ge ..)) _)
def quoteT (ε:ℝ) (G:Gauge)(C:RG.Stage)(x:ℝ): ℝ:= basisB*Lamppost.Height ε C G x

def rake (y : ℝ):= y ^ (-(8/100):ℝ)
structure Grants (G : Gauge) (L: Side)(S: Stage)(x t K ε:ℝ) : Prop where
  lifts p (hp:Time.Same S p)(hv:p.B=radiusB x)(hP:p.threshold=temp x)(hh:p.threshold≤2*Pressure.fiery G x L):
    let u:= quoteT ε G S x
    let t':= p.threshold
    0 ≤ u∧ 2*(t'^2)⁻¹*u ≤ rake (betaF G x L)∧
    ∀ α:ℝ,|α|≤K → priceS u α S.width S.paths S.clip p G ≤ Payroll.pay G L x ∧ priceE u α S.width S.paths S.clip p G ≤ t*δE x

private lemma δe (x:ℝ)(hx:0<x):δE x=x ^ (-(11/10):ℝ) := by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
private lemma pulses (L:Side) : Rate G L (-(11/10)) δE := by
  let w x := (2:ℝ)^(11/10:ℝ)* betaF G x L ^ (-(11/10:ℝ))
  have hw: Rate G L (-(11/10)) w:= Rate.power.mul_left _
  apply hw.compare
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (G.slopeConstant * Real.log L.val),Delay.shift_pos G L] with x hx hy hp
  rw [δe _ hx, abs_of_nonneg (by positivity)]; apply le_trans _ (le_abs_self _)
  let y:= betaF G x L; have h:y/2≤x:=by unfold y betaF; linarith
  change _≤ w x
  calc
    _ ≤ (y/2)^(-(11/10:ℝ)) := Real.rpow_le_rpow_of_nonpos (half_pos hp) h (by norm_num)
    _ = w x := by rw [Real.div_rpow hp.le (by norm_num),Real.rpow_neg (x:=2) (by norm_num)]; unfold w; rw [div_inv_eq_mul]; ring
lemma spots (L:Side)(S:Stage)(A:ℝ)(_hx:0≤ A) : Rate G L (-(11/10)) (quoteT A G S):=by
  let h:= (pulses (G:=G) L).mul_left (Time.credit G S)
  exact (((h.mul_left (A+2*A)).add (h.mul_left A)).mul_left _)
lemma taper {L:Side} (h:0<ε)(S:Stage) : ∀ᶠ x : ℝ in atTop, 0≤ quoteT ε G S x∧2*((temp x)^2)⁻¹ * quoteT ε G S x ≤ rake (betaF G x L) ∧ quoteT ε G S x ≤(temp x)^2:=by
  let t x:= (temp x ^ 2)⁻¹; let u:= quoteT ε G S
  have hp: Rate G L 1 t:= by
    apply Rate.hat.compare
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hh : 1/x ≤ temp x ^ 2:= by
      unfold temp; rw [mul_pow,inv_pow, Real.sq_sqrt hx.le]; rw [one_div]
      apply le_mul_of_one_le_right (by positivity); exact one_le_pow₀ (Real.one_le_exp (sq_nonneg _))
    rw [abs_of_nonneg (a:=t x) (by unfold t; positivity)]; exact ((inv_anti₀ (div_pos one_pos hx) hh).trans_eq (one_div x ▸ inv_inv x)).trans ((le_add_of_nonneg_right (Work.E04.shift_nonneg G L)).trans (le_abs_self _))
  have hv:= (hp.mul (spots L S ε h.le)|>.mul_left 2)
  filter_upwards [hv (-(8/100:ℝ)) (by norm_num),hv.below (by norm_num) 1 zero_lt_one, eventually_gt_atTop (0:ℝ)] with x hx hp' hy
  have hh:0 ≤ u x:= by have hu:= Time.credit_pos G S; unfold u quoteT; apply mul_nonneg basis_pos; unfold Lamppost.Height; rw [δe x hy]; positivity
  have he: 2*(t x*u x)≤ 1:= (le_abs_self _).trans hp'; refine ⟨hh, ?_,?_⟩
  · rw [mul_assoc]; exact (le_abs_self _).trans hx
  have hP:0<temp x:= by unfold temp; positivity
  apply le_of_mul_le_mul_right _ (inv_pos.mpr (sq_pos_of_pos hP)); rw [mul_inv_cancel₀ (sq_pos_of_pos hP).ne',mul_comm]; change t x*u x≤1; linarith
lemma stories (h:0<ε)(L:Side)(S:Stage)(K:ℝ)(hK: 0≤K): ∀ᶠ x in atTop,∀ (p:BudgetPoint)(α:ℝ),Time.Same S p → p.B=radiusB x → p.threshold=temp x→p.threshold ≤ 2*Pressure.fiery G x L → |α| ≤ K →
    priceS (quoteT ε G S x) α S.width S.paths S.clip p G ≤ Payroll.pay G L x := by
  let v:=Pressure.temp
  let u x:=2*Pressure.fiery G x L; let Z:=Time.softCeiling G S K; let f x:= Z*(1+(radiusB x:ℝ))^4*u x; have hu : Rate G L (-(1/2)) u:= Rate.flame.mul_left 2
  have he: Rate G L (-(1/2)) f:= by simpa only [zero_mul,zero_add] using! ((((Rate.const (G:=G) (L:=L) 1).add Rate.radius_price).pow 4|>.mul_left Z).mul hu)
  have hz:0≤ Z:= by unfold Z Time.softCeiling; have hv:= Time.soft_pos G S; have hF:= pair_nonneg G (Time.probe S); have hx := (Collection.budget_pos (Time.probe S) G S.clip S.width_pos S.paths_pos.le).2.2; positivity
  filter_upwards [taper h S (G:=G) (L:=L), (he.mul_left 5) (-(1/8):ℝ) (by norm_num)] with x hx he p α hp hP ht hu hA
  let b:= quoteT ε G S x
  unfold priceS
  have hm (a A) (ha : |a| ≤K) (hc : 0 ≤ A)(hd:A ≤ p.threshold^2): softNeed G p S.clip S.width S.paths a A ≤ f x:= by
    have hm:= Time.soft_table G S hp ha hc hd; rw [hP] at hm; exact hm.trans (mul_le_mul_of_nonneg_left hu (by positivity))
  have h' := hm α 0 hA le_rfl (sq_nonneg _); have hg:= hm 0 b (by rw [abs_zero]; exact hK) hx.1 (ht ▸ hx.2.2)
  have heq:softNeed G p S.clip S.width S.paths 0 1*b=softNeed G p S.clip S.width S.paths 0 b:= by unfold softNeed hitNeed softReset Push.AbsoluteSums.Footprint.payment Footprint.degreeIncome; rw [abs_zero]; ring
  change _+4*_ *b ≤ _
  rw [mul_assoc,heq]; exact le_trans (b:=5*f x) (by linarith only [h',hg]) ((le_abs_self _).trans he)
lemma chapter (t:ℝ)(h:0<t):∃ ε:ℝ,0 < ε ∧ ε ≤1/16 ∧ ε≤t ∧ ∀ (G:Gauge)(L:Side)(S:RG.Stage)(K:ℝ),0 ≤ K→ ∀ᶠ x in atTop,Grants G L S x t K ε:= by
  let V:= max 1 basisB; let ε:= min (1/16) (t/(32*V)); have hv:0<V:= zero_lt_one.trans_le (le_max_left ..); have he:0<ε:=by unfold ε; positivity
  have hk: ε≤ t/(32*V):= min_le_right ..
  have hV : basisB * ε *16 ≤ t/2:= by
    have hx: 0 < 32*V:= by positivity
    nlinarith only [(le_div_iff₀ hx).mp hk, mul_le_mul_of_nonneg_right (le_max_right 1 basisB) he.le]
  have hh: ε ≤ t:=hk.trans ((div_le_self h.le (le_trans (by have hv: (1:ℝ)≤ V:=le_max_left ..; linarith) (le_refl _))))
  refine ⟨ε,he,min_le_left _ _,hh,fun G L S K hK=>?_⟩
  let u x:=2*Pressure.fiery G x L; let Z:= Time.top G S; have hp : Rate G L (-(3/2)) (fun x=>u x^3):=by
    convert Rate.pow (Rate.flame (G:=G) (L:=L)|>.mul_left 2) 3 using 1; norm_num
  filter_upwards [taper he S (G:=G) (L:=L),Delay.shift_pos G L, eventually_gt_atTop (0:ℝ), stories (G:=G) he L S K hK, (((hp.mul_left K).mul_left Z).mul (Rate.power (a:= (11/10:ℝ)))).below (by norm_num) _ (half_pos h)] with x hx he' hv hM hr
  constructor
  intro p hy ha hb hB
  refine ⟨hx.1,hb ▸ hx.2.1,fun α hα=> ⟨hM p _ hy ha hb hB hα,?_⟩⟩
  have hΨ:=Time.base_nonneg G S
  unfold priceE; rw [Time.table G S hy,Time.table G S hy]; simp only [mul_zero,abs_zero,zero_mul,add_zero,zero_add,mul_one]
  let U:=Time.credit G S; let b:= Time.base G S; let y:= betaF G x L
  have hE: y ^(-(11/10):ℝ) ≤ δE x:= by rw [δe x hv]; exact Real.rpow_le_rpow_of_nonpos hv (le_add_of_nonneg_right (Work.E04.shift_nonneg G L)) (by norm_num)
  have hf: Z*(|α| *p.threshold^3) ≤ t/2*δE x := calc
    _ ≤ Z*(K*u x^3) := mul_le_mul_of_nonneg_left (mul_le_mul hα (pow_le_pow_left₀ p.threshold_pos.le hB 3) (pow_nonneg p.threshold_pos.le _) hK) hΨ.2
    _ ≤ t/2*y ^(-(11/10):ℝ):= by rw [Real.rpow_neg he'.le, ← div_eq_mul_inv]; exact (le_div_iff₀ (Real.rpow_pos_of_pos he' _)).mpr ((le_abs_self _).trans hr)
    _ ≤ _:= mul_le_mul_of_nonneg_left hE (half_pos h).le
  have ht : b*U≤1:= (Time.authorized G S).2.trans (by norm_num)
  apply le_trans (add_le_add_left hf _)
  change _+4*b*quoteT ε G S x≤_
  have h': 0≤ δE x:= (Real.rpow_nonneg he'.le _).trans hE
  unfold quoteT Lamppost.Height
  suffices hh : 16*(basisB*ε)*(b*U) ≤ t/2 by change _+4*b*(basisB*((ε+2*ε)*(U*δE x)+ε*(U*δE x)))≤ _; linarith only [mul_le_mul_of_nonneg_right hh h']
  exact (mul_le_of_le_one_right (mul_nonneg (by norm_num) (mul_nonneg basis_pos he.le)) ht).trans ((mul_comm ..).trans_le hV)
end YM.UVExtension.Yard
