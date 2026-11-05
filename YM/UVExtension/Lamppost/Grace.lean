import YM.UVExtension.Payroll.Marches
import YM.UVExtension.Payroll.Night
import YM.UVExtension.Lamppost.Barley

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Filter Set Lattice RG Pressure Push Push.AbsoluteSums Precision Metric Wilson Finset Topology
open ConnectedActivityE6 Blaze Wick Payroll AnalyticBridge VerifiedReset Quotes Next.Scheduling
open scoped ContDiff BigOperators Classical
-- profile-uniform (uniform in bar-offset). working charts sized in beta of the fine level
abbrev AxisK := Option (Fin 4)
abbrev Mark := Plot AxisK
def stretchB (y : ℝ):= y^(98/100:ℝ)
def gardenB (y:ℝ):= y^(4/1000:ℝ)
def inspire (y b : ℝ) (z:Mark): Mark:= Function.update z none ((b:ℂ)+(stretchB y:ℂ)*z none)
def subgate (y b : ℝ)(x : AxisK→ℝ): AxisK→ ℝ:=Function.update x none (b+stretchB y*x none)
lemma inspireD (y b : ℝ) : Differentiable ℂ (inspire y b):= by
  intro x; refine differentiableAt_pi.mpr ?_; rintro (_|i)
  · unfold inspire; simp only [Function.update_self]; fun_prop
  unfold inspire; simp only [Function.update_of_ne (show Option.some i≠none from by simp)]; fun_prop
lemma audits (y b : ℝ)(x : AxisK→ℝ): inspire y b (hoist x)=hoist (subgate y b x):= by funext i; cases i <;> simp [inspire,subgate,hoist]
-- interior 5/8, 7/4

def InsideB (y b:ℝ):= 5/8*y≤ b ∧ b≤ 7/4*y
def chasing (y B : ℝ) : Prop := ∀ b, InsideB y b →∀ z:Mark, (∀ i, ‖z i‖≤ gardenB y) → inspire y b z∈ parade y B
abbrev capK : ℝ := 16
abbrev realcap : ℝ:=1/16
abbrev lengthB : ℕ:=410
def Height (ε : ℝ)(s : RG.Stage) (G:Gauge) (x:ℝ):= (ε+2*ε)* (Time.credit G s*δE x)+ ε*(Time.credit G s*δE x)
abbrev wage : ℝ:= luck (r:=realcap) (v:=capK) (by norm_num [realcap]) (by norm_num [realcap,capK]) lengthB AxisK
variable {G:Gauge} (L:Side) {ε:ℝ} (C:RG.Stage)
structure Chateau (G:Gauge) (L:Side)(ε:ℝ)(C:RG.Stage) (x:ℝ) : Prop where
    high : 0 < x
    cast : let y:=betaF G x L
           chasing y (y^fillSpeed) ∧ capK < gardenB y ∧ pay G L x*(capK / gardenB y)^lengthB*(1-capK/gardenB y)⁻¹≤ Height ε C G x

lemma charter (h:0 < ε):∀ᶠ x in atTop,Chateau G L ε C x:= by
  let g y:=gardenB (betaF G y L)
  let a:ℝ:=4/1000
  have ha:∀ᶠ x in atTop,g x > 2*capK:= (tendsto_rpow_atTop (show 0<(4/1000:ℝ) by norm_num)|>.comp (Work.E09.betaF_growth G L)).eventually_gt_atTop _
  have hx : ∀ᶠ x in atTop,stretchB (betaF G x L)*g x ≤ (1/16)*betaF G x L:= by
    have hg : Rate G L (98/100+4/1000-1) (fun x=> stretchB (betaF G x L)*g x*(betaF G x L^(-(1:ℝ)))):= (Rate.power.mul Rate.power).mul Rate.power
    filter_upwards [Delay.shift_pos G L,hg.below (by norm_num) (1/16) (by norm_num)] with x h hx
    apply le_of_mul_le_mul_right _ (inv_pos.mpr h)
    rw [mul_assoc ((1:ℝ)/16), mul_inv_cancel₀ h.ne',mul_one, show (betaF G x L)⁻¹=betaF G x L ^ (-(1:ℝ)) from (Real.rpow_neg_one _).symm]; exact (le_abs_self _).trans hx
  have hp : Rate G L (-1/8+ (-a)*lengthB +11/10) (fun x=> pay G L x*(capK / g x)^lengthB*2* betaF G x L ^ (11/10:ℝ)):= by
    let W x:=(betaF G x L)^(-a)
    have hv : Rate G L (-a) (fun x=>capK/g x):= by
      refine (Rate.power (a:=-a)|>.mul_left capK).congr ?_
      filter_upwards [Delay.shift_pos G L] with x hx; simp only [Real.rpow_neg hx.le, div_eq_mul_inv]; rfl
    have ht: Rate G L (-1/8) (pay G L):= by
      rw [show (-1/8:ℝ)=-(1/8:ℝ) by norm_num]; exact Rate.power
    exact (((ht.mul (hv.pow _)).mul_right 2).mul Rate.power)
  have hB:= Time.credit_pos G C
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 1,hx,ha,hp.below (by norm_num [a,lengthB]) (ε*Time.credit G C) (by positivity), eventually_gt_atTop (0:ℝ)] with x he hx hA hb hX
  let y:= betaF G x L; let t:=stretchB y; have hy:0<y:= zero_lt_one.trans he; have ht:0≤ t:= Real.rpow_nonneg hy.le _
  have hi:capK<g x:= lt_trans (by norm_num [capK]) hA
  refine ⟨hX,?_,hi,?_⟩
  · intro b h z hh; apply marching _|>.2; let a:= z none; let u:=(b:ℂ)+(t:ℂ)*a
    have hd : |t*a.re|≤ t*g x := by rw [abs_mul,abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hh none)) ht
    have hv : |t*a.im| ≤ t*g x := by rw [abs_mul,abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (hh none)) ht
    unfold inspire; rw [Function.update_self]
    refine ⟨?_,fun i=>?_⟩
    · change y / 2<u.re ∧ u.re< 2*y ∧ |u.im|< y^(99/100:ℝ)
      have hh : t*g x ≤ (1/16)*y := hx; unfold u; simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.add_im,Complex.mul_im,zero_mul,sub_zero,add_zero,zero_add]; rw [abs_le] at hd
      refine ⟨by linarith only [hd.1,h.1,hy,hh],by linarith only [hd.2,h.2,hy,hh],?_⟩
      refine hv.trans_lt ?_; change y^(_ : ℝ)*y^(_ : ℝ)< _; rw [← Real.rpow_add hy]; exact Real.rpow_lt_rpow_of_exponent_lt he (by norm_num)
    rw [Function.update_of_ne (show some i ≠ none by simp)]; exact (hh _).trans_lt (Real.rpow_lt_rpow_of_exponent_lt he (by norm_num [fillSpeed]))
  let P:=pay G L x; let w:=capK/g x; have hv:0<capK:= by norm_num [capK]
  have ht':0<g x:= hv.trans hi; have hg:w ≤ 1/2:= (div_le_iff₀ ht').mpr (by linarith)
  have hu : (1-w)⁻¹ ≤ 2:= (inv_le_iff_one_le_mul₀ (by linarith : 0< 1-w)).mpr (by linarith)
  let H:= Time.credit G C; let E:= δE x; have h : 0 ≤ E:=by unfold E δE Clock.gap; positivity
  have hh' : y ^ (-(11/10):ℝ)≤ E:= by
    have hi : incomingE G L x=y ^ (-(11/10):ℝ) := by unfold incomingE; change (Real.sqrt y)⁻¹ ^ (_ : ℝ)=_; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hy.le,← Real.rpow_mul hy.le]; norm_num
    rw [← hi]; refine Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) ?_ (by norm_num : 0≤(11/5:ℝ)); exact inv_anti₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt (le_add_of_nonneg_right (Work.E04.shift_nonneg G L)))
  have hs: P*w^lengthB*2 ≤ ε*H* y ^ (-(11/10):ℝ):= by
    rw [Real.rpow_neg hy.le,← div_eq_mul_inv]; exact (le_div_iff₀ (by positivity)).mpr ((le_abs_self _).trans hb)
  have hr:0≤ ε:=by linarith only [show 0<ε from ‹_›]
  exact ((mul_le_mul_of_nonneg_left hu (mul_nonneg (Real.rpow_nonneg hy.le _) (pow_nonneg (div_nonneg hv.le ht'.le) _))).trans hs).trans (((mul_le_mul_of_nonneg_left hh' (mul_nonneg hr hB.le))).trans (by unfold Height; change ε*H*E≤(ε+2*ε)*(H*E)+ε*(H*E); have hp:0≤ H*E:=mul_nonneg hB.le h; nlinarith))
lemma periodic (v q:ℝ):IsOpen (parade (ι:=Fin 4) v q):= by apply court_open; rintro (_|i); exact open_aisle _; exact isOpen_ball
end YM.UVExtension.Lamppost
