import YM.TraceExtension.Swift.Kna
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}
abbrev fog(x:ℝ):ℝ:= Wave 1 x
abbrev thetaP(x:ℝ):=(Real.sqrt x)⁻¹*fog x
abbrev sash(S:Stage)(x:ℝ):= thetaP x*(1+(high x:ℝ))^S.power
abbrev peace(x:ℝ):=thetaP x /x^((1:ℝ)/24)
-- price ratio
abbrev shear(x:ℝ):=4*x*thinM x+wideM x
lemma qr(K m:ℕ)(S:Stage)(hS:1 ≤ m)(A:ℝ)(ha:1≤ A): ConstMass 4 (fun x=>zeff (shear x) A (sash S x)):=by
   let f(x:ℝ):=(1+(high x:ℝ))^S.power; let V(x):=4*x*wideM x+x*wideM x
   have hf: ConstMass 0 f:=((mass zero_le_one).gather expansion).crop _; let C:=2*5*(evenR 2 A); have hz:0 ≤ C:=by unfold C evenR; positivity
   have hx:ConstMass 4 (fun x=> zeff (V x) A (sash S x)):=by
      have h:ConstMass (1/50+(2*1)+(2*0)) (fun x=>C*((wideM x*(fog x)^2)*f x^2)):= (((waveM (1/50)).prod (show ConstMass ((2:ℕ)*1:ℝ) (fun x=> fog x^2) from ConstMass.pow (waveM 1) 2)).prod (show ConstMass ((2:ℕ)*0:ℝ) (fun x=> f x^2) from hf.pow 2)).times C hz
      let F x:=zeff (V x) A (sash S x)
      refine (h.inc (by norm_num : (1/50:ℝ)+(2*1)+(2*0)≤4)).mono ?_; filter_upwards[eventually_gt_atTop (0:ℝ)] with x hx
      have hv :zeff (V x) A (sash S x)= C*((wideM x*fog x^2)*f x^2):=by unfold zeff V C sash thetaP f; field_simp; rw[Real.sq_sqrt hx.le];ring
      change 0 ≤ _∧ _ ≤ _; refine ⟨by rw[hv]; positivity[show 0 < wideM x from wake ..],hv.le⟩
   refine hx.mono ?_; filter_upwards[eventually_gt_atTop (1:ℝ)] with x hp
   have hv: 0 < thinM x:=wake ..; have hV:0 < wideM x:=wake ..; have hx:0 ≤ evenR 2 A:=by unfold evenR; positivity
   refine ⟨by change 0≤ zeff _ _ _; unfold zeff shear; positivity,?_⟩; change zeff (shear x) _ _ ≤ _; unfold zeff; dsimp only[V,shear];gcongr;exacts [(wane x (by norm_num: (1/200:ℝ) ≤1/50)), (le_mul_of_one_le_left (le_of_lt (wake ..)) hp.le)]
lemma bears (m:ℕ)(k:ℕ)(A C:ℝ)(S:Stage)(hA:1 ≤ A)(hc:0 ≤ C)(hm:1 ≤ m):∃ c,0 ≤ c ∧ ConstMass c (fun x=>composeCost (k+m+1) C (zeff (shear x) A (sash S x))):=by
    have ht:= (mass zero_le_one).inc (b:=4) (by norm_num) |>.gather (qr k m S hm A hA); have hh:= (ht.pow (k+m+1)).times ((↑((k+m+1).factorial):ℝ)*C) (by positivity)
    exact ⟨_,by positivity,hh⟩
lemma sash_ok (S:Stage)(D:ℝ)(hD:0<D):∀ᶠ x:ℝ in atTop, sash S x ≤ D:=by
    let f(x:ℝ):=(1+(high x:ℝ))^S.power; let g(x) := (fog x*f x); have hf:ConstMass 0 f:=((mass zero_le_one).gather expansion).crop _; have hg: ConstMass (1+0) g:=(waveM 1).prod hf
    have hA:= hg 2 (by norm_num)
    have hQ:= ((mass (show 0≤ D⁻¹ from by positivity)).prod hg) 2 (by norm_num)
    filter_upwards [hQ, wave_sub 2 (1/2) (by norm_num), eventually_gt_atTop (0:ℝ)] with x hx hv he
    have hh : D⁻¹*(fog x*f x)≤ Real.sqrt x:= by rw[Real.sqrt_eq_rpow];exact hx.2.trans hv
    change (Real.sqrt x)⁻¹*_*_≤ D; rw [mul_assoc]; apply (inv_mul_le_iff₀ (Real.sqrt_pos.mpr he)).2; rw [mul_comm (Real.sqrt x) D]; exact (inv_mul_le_iff₀ hD).1 hh
lemma pane (x:ℝ)(hi:1 ≤ x) (S:Stage): peace x/(sash S x)= (x^((1:ℝ)/24))⁻¹/((1+(high x:ℝ))^S.power):=by
    have hh: thetaP x ≠0:=by unfold thetaP; have ht:=wake 1 x; unfold fog; positivity
    unfold peace sash; field_simp [(wake 1 x).ne']
    all_goals exact div_self (wake 1 x).ne'
lemma pet (x:ℝ)(hp:1 ≤ x) (S:Stage):
    let t:= sash S x; let h:=peace x; 0<t ∧0<h∧ h/t ≤ x^ (-(1/24:ℝ)):=by
    intro t h; have hx:0<x:=zero_lt_one.trans_le hp; have hh:0 < thetaP x:=mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hx)) (wake ..)
    refine ⟨mul_pos hh (by positivity),div_pos hh (by positivity),?_⟩; change peace _ / sash _ _ ≤ _; rw [pane x hp, Real.rpow_neg hx.le]; exact div_le_self (by positivity) (one_le_pow₀ (by simp : 1≤1+(high x:ℝ)))
-- Taylor ratio. export as bound with explicit slack.
def swole(x:ℝ):= thetaP x ^2 * x^ (-(1/100:ℝ))
lemma pledge(m:ℕ)(F:ℝ→ℝ)(S:Stage)(T:ℝ)(A a:ℝ)(h:0≤ A)(hp:ConstMass a F)(hm:48  ≤ m): ∀ᶠ x:ℝ in atTop,
    F x *((sash S x)*(peace x/sash S x)^(m+1)) ≤ swole x *peace x:=by
    obtain ⟨q,hq⟩ : ∃ q:ℝ,a<q:=exists_gt a
    filter_upwards [hp q hq,wave_sub q (1/4) (by norm_num),eventually_gt_atTop (1:ℝ)] with x hx hv hX
    obtain ⟨ht,hs,hB⟩:=pet x hX.le S; let t:=sash S x; let p:=peace x; have he: (p/t)≤1:= hB.trans (Real.rpow_le_one_of_one_le_of_nonpos hX.le (by norm_num))
    have hh: (p/t)^m ≤ x^(-2:ℝ):=by
       refine (pow_le_pow_of_le_one (by positivity) he hm).trans (le_trans (pow_le_pow_left₀ (div_nonneg hs.le ht.le) hB _) ?_)
       rw [←Real.rpow_mul_natCast (by positivity)]; norm_num
    rw [pow_succ]; change F x*(t*((p/t)^m*(p/t)))≤ swole x*p; rw[show t*((p/t)^m*(p/t))=(p/t)^m*p from by field_simp [show t≠0 from ht.ne'],←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hs.le
    refine (mul_le_mul (hx.2.trans hv) hh (by positivity) (by positivity)).trans ?_; unfold swole thetaP; rw [← Real.rpow_add (by positivity),mul_pow];
    have ho:0<x:=zero_lt_one.trans hX
    have hx: ((Real.sqrt x)⁻¹)^2=x^ (-(1:ℝ)):=by rw[inv_pow,Real.sq_sqrt ho.le,Real.rpow_neg ho.le,Real.rpow_one]
    rw [hx]; apply le_trans (b:=x^(-(1:ℝ)) * (x^(-(1/100:ℝ)))) _ (by gcongr; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (wok 1 x (by norm_num))))
    rw [← Real.rpow_add ho]; exact Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
end YM.Trace.Swift
