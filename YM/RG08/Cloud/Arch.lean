import YM.RG08.Cloud.Oil

/-!
# Exponent & HJ-PDE ⇒ linear formal heat solution

Pair coefficient Γ/2 as received (before summing both orders). The linear time
Cauchy problem with 
*polynomial* coefficients in auxiliary time has a unique solution
and explicit Taylor expression on each g-coefficient whenever there is one.
-/
noncomputable section
namespace YM.RG08.Cloud
open Finset PowerSeries
open scoped PowerSeries BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R][Algebra ℝ R]
variable {I : Type*}[Fintype I](K:I→I→ℝ)

abbrev Gauge (I R:Type*)[CommRing R][Algebra ℝ R]:= I→Derivation ℝ R R

/-- K here uses 1/2 already. -/
def slab (D:Gauge I R):R→ₗ[ℝ] R:=∑ i,∑ j,K i j • ((D i).toLinearMap.comp (D j).toLinearMap)
def join (D:Gauge I R)(V:R):R:=∑ i,∑ j,K i j • (D i V * D j V)

lemma slab_do (D:Gauge I R)(V:R):slab K D V=∑ i,∑ j,K i j • D i (D j V):=by simp [slab,LinearMap.sum_apply]
lemma flight_E (D:Gauge I R){V:R⟦X⟧}(h:tiny V): slab K (fun i=> flight (D i)) (rise V)=
       rise V * (slab K (fun i=>flight (D i)) V + join K (fun i=>flight (D i)) V):=by
 rw [slab_do,slab_do]; unfold join
 let f i : Derivation ℝ R⟦X⟧ R⟦X⟧:=flight (D i)
 have hp (x i:I) : f x (f i (rise V))=rise V*(f x V*f i V + f x (f i V)):=by
   dsimp only [f]; rw [lift_rise _ h, Derivation.leibniz,lift_rise _ h]; simp only [smul_eq_mul]; ring
 change ∑ i,∑ j,K i j • f i (f j _)=rise V*((∑ i,∑ j,K i j • f i (f j V))+ ∑ i,∑ j,K i j • (f i V*f j V))
 simp_rw [hp,mul_add,Finset.mul_sum,mul_smul_comm,smul_add,Finset.sum_add_distrib]; exact add_comm ..

variable {K}
abbrev Season (R:Type*) [CommRing R]:=PowerSeries (Polynomial R)
def season (D:Gauge I R):Gauge I (Season R):=fun i=>flight (current (D i))
def takeoff (f:Season R)(e j:ℕ):=(coeff e f).coeff j

/-- Predicate by PDE, coefficient and rank calculations separately. -/
structure Clockwise (D:Gauge I R)(K:I→I→ℝ)(V:Season R) : Prop where
 cold : tiny V
 sun : flight (pendulum R) V = slab K (season D) V + join K (season D) V

theorem Clockwise.linear {D:Gauge I R}{V:Season R}(h:Clockwise D K V):
 flight (pendulum R) (rise V)=slab K (season D) (rise V):=by
 rw [lift_rise _ h.cold,h.sun]
 exact (flight_E (D:=fun i=> current (D i)) K h.cold).symm

omit [Fintype I] in
lemma watch (D:Gauge I R)(i:I)(f:Season R)(e j:ℕ):takeoff (season D i f) e j=D i (takeoff f e j):=by rw [takeoff,season,flight_apply,amps];rfl

omit [Algebra ℝ R] in
lemma take_add (V S:Season R) (e j:ℕ) : takeoff (V+S) e j=takeoff V e j+takeoff S e j:=by simp only [takeoff,map_add,Polynomial.coeff_add]
lemma take_smul (a:ℝ)(V:Season R)(e j:ℕ):takeoff (a • V) e j=a • takeoff V e j:=by simp only [takeoff,coeff_smul,Polynomial.coeff_smul]
omit [Algebra ℝ R] in
lemma take_sum {M:Type*}(S:Finset M)(V:M→Season R)(e j:ℕ):takeoff (S.sum V) e j=S.sum (fun i=>takeoff (V i) e j):=by
 induction S using Finset.induction_on with
 | empty=>simp [takeoff]
 | insert _ _ hi ih=> simp [sum_insert hi,take_add,ih]

lemma observe (D:Gauge I R)(K:I→I→ℝ)(f:Season R)(e j:ℕ):takeoff (slab K (season D) f) e j=slab K D (takeoff f e j):=by simp_rw [slab_do,take_sum,take_smul,watch]

lemma dial (f:Season R)(e j:ℕ):takeoff (flight (pendulum R) f) e j=(j+1:ℝ) • takeoff f e (j+1):=by rw [takeoff,flight_apply,beat];rfl

/-- If solution is polynomial at coefficient e, these coefficients specify the g-degree e
ordinary moments *without computing a field-independent partition limit*. -/
theorem Clockwise.jet {D:Gauge I R}{V:Season R}(h:Clockwise D K V)(e j:ℕ) : takeoff (rise V) e j= rfactor j • ((slab K D)^[j] (takeoff (rise V) e 0)):=by
 induction j with
 | zero=>simp [rfactor]
 | succ j ih=>
    have he:(j+1:ℝ)≠0:=by positivity
    apply untangle he
    rw [←dial,h.linear,observe,ih,Function.iterate_succ_apply',smul_smul,earns]
    exact (slab K D).map_smul ..

/-- forgetting time by unital algebra morphism. -/
def forgetAt (R:Type*)[CommRing R][Algebra ℝ R](t:ℝ):Polynomial R→ₐ[ℝ] R:= (Polynomial.aeval (algebraMap ℝ R t)).restrictScalars ℝ

def summer (t:ℝ):Season R→+* PowerSeries R:= PowerSeries.map ((forgetAt R t).toRingHom)
lemma summer_rise (t:ℝ)(V:Season R):summer t (rise V)=rise (summer t V):=rise_map ..

lemma summer_initial (f:Season R)(e:ℕ):coeff e (summer 0 f)=takeoff f e 0:=by simp [summer,takeoff,forgetAt,Polynomial.coeff_zero_eq_eval_zero]

lemma summer_range (f:Season R)(n e:ℕ)(t:ℝ)(hk:∀ i>n,takeoff f e i=0):
 coeff e (summer t f)=∑ i∈range (n+1),t^i • takeoff f e i:=by
 let P := coeff e f
 rw [summer,coeff_map]
 change (forgetAt R t) P = ∑ i ∈ range (n+1), t^i • P.coeff i
 conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
 rw [map_sum]
 calc
   _ = ∑ i ∈ P.support, t^i • P.coeff i := by
     apply Finset.sum_congr rfl
     intro i _
     change Polynomial.aeval (algebraMap ℝ R t)
       (Polynomial.C (P.coeff i) * Polynomial.X ^ i) = _
     rw [map_mul,Polynomial.aeval_C,map_pow,Polynomial.aeval_X]
     change P.coeff i * (algebraMap ℝ R t)^i = _
     rw [Algebra.smul_def,map_pow,mul_comm]
   _ = ∑ i ∈ range (n+1), t^i • P.coeff i := by
     apply Finset.sum_subset ?_ (fun i _ hi => ?_)
     · intro i hi
       have he : P.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
       have hh : ¬ (n < i) := fun H => he (hk i H)
       exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt hh))
     rw [Classical.not_not.mp (mt Polynomial.mem_support_iff.mpr hi),smul_zero]

end YM.RG08.Cloud
