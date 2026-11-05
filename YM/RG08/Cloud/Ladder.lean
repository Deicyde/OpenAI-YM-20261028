import YM.RG08.Cloud.Levels

/-!
# Positive formal g-graded algebra: exponential and differentiation by any derivation on
coefficient ring (fields, time, higher jets etc).
-/
noncomputable section
namespace YM.RG08.Cloud
open Finset PowerSeries
open scoped PowerSeries BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type*}[CommRing R][Algebra ℝ R][CommRing S][Algebra ℝ S]

def tiny (f:R⟦X⟧) := coeff 0 f=0

def rfactor (n:ℕ):ℝ:= (n.factorial:ℝ)⁻¹
lemma earns (n:ℕ) : (n+1:ℝ)*rfactor (n+1)=rfactor n:=by
 have h:(n+1:ℝ)≠0:=by positivity
 simp [rfactor,Nat.factorial_succ,h,mul_left_comm]

omit [Algebra ℝ R] in
lemma phase {f:R⟦X⟧}(h:tiny f)(n e:ℕ)(he:e<n):coeff e (f^n)=0:=by
 apply coeff_of_lt_order
 have hz:=PowerSeries.le_order_pow_of_constantCoeff_eq_zero n (φ:=f) (by rwa [← coeff_zero_eq_constantCoeff])
 exact lt_of_lt_of_le (by exact_mod_cast he) hz

def rise (f:R⟦X⟧):R⟦X⟧:= mk (fun e=>∑ n∈range (e+1),rfactor n • (coeff e (f^n)))

lemma rise_at (f:R⟦X⟧)(e:ℕ):coeff e (rise f)=∑ n∈range (e+1),rfactor n • coeff e (f^n):=coeff_mk ..
lemma rise_late {f:R⟦X⟧}(h:tiny f)(e n:ℕ)(he:e≤n):coeff e (rise f) = ∑ i∈range (n+1),rfactor i • coeff e (f^i):=by
 rw [rise_at];apply Finset.sum_subset (range_mono (by omega))
 intro i hi hx;rw [phase h i e (by simp only [mem_range] at *;omega),smul_zero]
lemma rise_before (f:R⟦X⟧):coeff 0 (rise f)=1:=by simp [rise_at,rfactor]

/-- Truncated sum for coefficient e, evaluated at arity e+1 ensures full value on all
factors inside coefficient e products. -/
def rpol (n:ℕ)(f:R⟦X⟧):R⟦X⟧:=∑ i∈range (n+1),rfactor i • f^i
lemma coeff_rpol {f:R⟦X⟧}(h:tiny f){n e:ℕ}(he:e≤n):coeff e (rpol n f) = coeff e (rise f):=by
 rw [rpol,map_sum,rise_late h e n he]; simp_rw [coeff_smul]
lemma coeff_rpol_mul {f:R⟦X⟧}(h:tiny f)(a:R⟦X⟧)(e:ℕ):coeff e (rpol e f*a)=coeff e (rise f*a):=by
 rw [coeff_mul,coeff_mul];apply Finset.sum_congr rfl
 intro j hj;rw [coeff_rpol h]
 have he:=Finset.mem_antidiagonal.mp hj; omega

private lemma leib (D:Derivation ℝ R R)(f:R⟦X⟧)(n:ℕ):flight D (rfactor (n+1) • f^(n+1))=rfactor n • (f^n * flight D f):=by
 rw [(flight D).map_smul, (flight D).leibniz_pow]
 rw [Nat.add_sub_cancel_right,smul_eq_mul, nsmul_eq_mul]
 -- nsmul and ℝ smul interact
 have hr (w:R⟦X⟧): (↑(n+1):R⟦X⟧)*w=(n+1:ℝ) • w:=by rw [Algebra.smul_def,map_add,_root_.map_natCast,map_one];norm_cast
 rw [hr,smul_smul,mul_comm (rfactor _),earns]

lemma lift_rpol (D:Derivation ℝ R R)(f:R⟦X⟧)(n:ℕ):flight D (rpol (n+1) f)= rpol n f*flight D f:=by
 unfold rpol;rw [map_sum,sum_range_succ'];simp_rw [leib]
 rw [Finset.sum_mul];simp

lemma lift_rise (D:Derivation ℝ R R){f:R⟦X⟧}(h:tiny f):flight D (rise f)=rise f*flight D f:=by
 ext e
 rw [flight_apply,←coeff_rpol h (Nat.le_succ e),←flight_apply,lift_rpol,coeff_rpol_mul h]

lemma rise_map (T:R→ₐ[ℝ] S)(f:R⟦X⟧):PowerSeries.map T.toRingHom (rise f)=rise (PowerSeries.map T.toRingHom f):=by
 ext e
 -- Ring hom coercions
 rw [coeff_map,rise_at,rise_at,map_sum]
 apply Finset.sum_congr rfl;intro j _
 rw [← _root_.map_pow,coeff_map]; exact _root_.map_smul T (rfactor j) (coeff e (f ^ j))

end YM.RG08.Cloud
