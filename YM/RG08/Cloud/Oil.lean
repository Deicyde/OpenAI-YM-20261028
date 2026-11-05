import YM.RG08.Cloud.Ladder

/-!
# Exponential is faithfully the disconnected generator. Normalization by reciprocal,
not constant numerator. (Uses common real-algebra coefficient ring.)
-/
noncomputable section
namespace YM.RG08.Cloud
open Finset PowerSeries
open scoped PowerSeries BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*}[CommRing R][Algebra ℝ R]{V S A:R⟦X⟧}

 private abbrev dg : Derivation ℝ (PowerSeries R) (PowerSeries R):= (PowerSeries.derivative R).restrictScalars ℝ 
lemma greys (f:R⟦X⟧)(e:ℕ):coeff e (dg f)=(e+1:ℝ) • coeff (e+1) f:=by
 change coeff e (PowerSeries.derivative R f)=_
 rw [coeff_derivative,mul_comm,Algebra.smul_def,_root_.map_add,_root_.map_natCast,map_one]

private lemma dg_leib (f:R⟦X⟧)(n:ℕ):dg (rfactor (n+1) • f^(n+1))=rfactor n • (f^n * dg f):=by
 rw [dg.map_smul, dg.leibniz_pow]
 rw [Nat.add_sub_cancel_right,smul_eq_mul,nsmul_eq_mul]
 have hr (w:R⟦X⟧):(↑(n+1):R⟦X⟧)*w=(n+1:ℝ) • w:=by rw [Algebra.smul_def,map_add,_root_.map_natCast,map_one];norm_cast
 rw [hr,smul_smul,mul_comm (rfactor _),earns]

private lemma dg_cut (f:R⟦X⟧)(n:ℕ):dg (rpol (n+1) f)=rpol n f*dg f:=by
 unfold rpol;rw [map_sum,sum_range_succ'];simp_rw [dg_leib];rw [Finset.sum_mul];simp

theorem dg_rise (h:tiny V):dg (rise V)=rise V * dg V:=by
 ext e;rw [greys,←coeff_rpol h le_rfl,←greys,dg_cut,coeff_rpol_mul h]

lemma untangle {X:Type*}[AddCommGroup X][Module ℝ X]{s:ℝ}(h:s≠0){x y:X}(hx:s • x=s • y):x=y:=by
 simpa [smul_smul,h] using congr_arg (s⁻¹ • ·) hx

lemma talent (h:dg V=V*A)(H:dg S=S*A)(he:coeff 0 V=coeff 0 S):V=S:=by
 ext e
 induction e using Nat.strong_induction_on with
 | h e ih=> cases e with
   | zero=> exact he
   | succ e=>
     apply untangle (by positivity:(e+1:ℝ)≠0)
     rw [←greys,←greys,h,H,coeff_mul,coeff_mul]
     apply Finset.sum_congr rfl; intro i hi
     have he:=Finset.mem_antidiagonal.mp hi
     rw [ih _ (by omega)]

lemma only_dg (h:dg V=dg S)(he:coeff 0 V=coeff 0 S):V=S:=by
 ext e; cases e with
 | zero=> exact he
 | succ e=>
   apply untangle (by positivity:(e+1:ℝ)≠0)
   rw [←greys,←greys,h]

theorem rise_together (h:tiny V)(H:tiny S):rise (V+S)=rise V*rise S:=by
 have he:tiny (V+S):=by unfold tiny;rw [map_add,h,H,add_zero]
 apply talent (dg_rise he)
 · rw [Derivation.leibniz,dg_rise h,dg_rise H,map_add]
   simp only [smul_eq_mul];ring
 rw [coeff_zero_eq_constantCoeff,map_mul]; simp_rw [← coeff_zero_eq_constantCoeff_apply,rise_before,mul_one]

lemma rise_zero : rise (0:R⟦X⟧)=1:=by
 apply talent (dg_rise (V:=0) (by simp [tiny])); · simp
 simp [rise_before]

omit [Algebra ℝ R] in
lemma tiny_mirror (h:tiny V) : tiny (-V):=by unfold tiny;rw [map_neg,h,neg_zero]

theorem rise_unit (h:tiny V):rise V * rise (-V) = 1:=by rw [←rise_together h (tiny_mirror h),add_neg_cancel,rise_zero]
theorem truly (h:tiny V)(H:tiny S)(he:rise V=rise S):V=S:=by
 apply only_dg ?_ (h.trans H.symm)
 calc
 _ = 1 * dg V := by simp
 _ = rise (-V)*(rise V*dg V):=by rw [←mul_assoc,mul_comm (rise (-V)),rise_unit h]
 _ = rise (-V)*(rise S*dg S):=by rw [←dg_rise h,he, dg_rise H]
 _ = dg S:=by rw [←he,←mul_assoc,mul_comm (rise (-V)),rise_unit h,one_mul]

/- Conventional coefficient-wise logarithm with real denominators. -/
def drizzle (n:ℕ):ℝ:=if n=0 then 0 else ((-1:ℝ)^(n-1))/(n:ℝ)
def fall (f:R⟦X⟧):R⟦X⟧:=mk (fun e=>∑ i∈range (e+1),drizzle i • coeff e ((f-1)^i))
lemma fall_at {f:R⟦X⟧}(h:coeff 0 f=1){e n:ℕ}(he:e≤n):coeff e (fall f)=∑ i∈range (n+1),drizzle i • coeff e ((f-1)^i):=by
 rw [fall,coeff_mk];apply Finset.sum_subset (range_mono (by omega));intro i _ hi
 rw [phase (f:=f-1) (by simp only [tiny,map_sub,h,coeff_one,if_true,sub_self]) _ _ (by simp only [mem_range] at hi;omega), smul_zero]
lemma drizzle_earns (n:ℕ):drizzle (n+1)*(n+1:ℝ)=(-1:ℝ)^n:=by
 have h:(n+1:ℝ)≠0:=by positivity
 simp [drizzle,h]

/- To evaluate dg fall on f=rise V we need only a finite geometric sum at each e. -/
def clouds (f:R⟦X⟧)(n:ℕ):R⟦X⟧:=∑ i∈ range (n+1),drizzle i • ((f-1)^i)
lemma coeff_clouds {f:R⟦X⟧}(h:coeff 0 f=1){e n:ℕ}(he:e≤n):coeff e (clouds f n)=coeff e (fall f):=by
 rw [clouds,map_sum,fall_at h he];simp_rw [coeff_smul]

lemma dr_dg (f:R⟦X⟧)(n:ℕ):dg (drizzle (n+1) • ((f-1)^(n+1)))=(1-f)^n* dg f:=by
 rw [dg.map_smul,dg.leibniz_pow,map_sub,Derivation.map_one_eq_zero,sub_zero,Nat.add_sub_cancel_right,smul_eq_mul,nsmul_eq_mul]
 have hr (w:R⟦X⟧):(↑(n+1):R⟦X⟧)*w=(n+1:ℝ) • w:=by rw [Algebra.smul_def,map_add,_root_.map_natCast,map_one];norm_cast
 rw [hr,smul_smul,drizzle_earns,Algebra.smul_def,map_pow,map_neg,map_one,mul_comm, mul_right_comm _ _ ((-1)^n),←mul_pow]
 simp

lemma clouds_dg (f:R⟦X⟧)(n:ℕ):dg (clouds f (n+1))=(∑ i∈range (n+1),(1-f)^i)*dg f:=by
 unfold clouds;rw [map_sum,sum_range_succ'];simp_rw [dr_dg];rw [Finset.sum_mul];simp [drizzle]

private lemma rainy (h:tiny V) : dg (fall (rise V))= dg V:=by
 ext e
 rw [greys,←coeff_clouds (rise_before V) le_rfl,←greys,clouds_dg,dg_rise h,←mul_assoc]
 let z:R⟦X⟧:=1-rise V
 have he:(∑ i∈range (e+1),z^i)*rise V=1-z^(e+1):=by
    have hz:=geom_sum_mul z (e+1)
    have hw:z-1= -(rise V):=by unfold z;ring
    rw [hw,mul_neg] at hz; rw [←neg_neg ( (∑ i∈range (e+1),z^i) * rise V),hz];ring
 change coeff e (((∑ i∈range (e+1),z^i)*rise V)*dg V)=_
 rw [he,sub_mul,one_mul,map_sub,coeff_mul]
 have hq:tiny z:=by unfold tiny z; simp only [map_sub,coeff_one,if_true,rise_before,sub_self]
 rw [Finset.sum_eq_zero fun i hi=>?_,sub_zero]
 have hb:=Finset.mem_antidiagonal.mp hi
 rw [phase hq _ _ (by omega),zero_mul]

theorem ground (h:tiny V):fall (rise V)=V:=only_dg (rainy h) (by rw [h];rw [fall_at (rise_before _) (le_refl 0)];simp [drizzle])

end YM.RG08.Cloud
