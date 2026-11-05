import YM.RG08.Room.Cable

/-! # Field pullbacks & Jacobian calculus on g-series. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Cloud Glyph Finset MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I J K : Type}

abbrev Port (I:Type):=Cab (Inn I)
def lug (x:I→Port J):Inn I→ₐ[ℝ] Port J:= MvPolynomial.aeval x
def belt (x:I→Port J):Port I→ₐ[ℝ] Port J:=tie (lug x)
abbrev liftInn {R:Type*}[CommRing R]:R→+*Cab R:=PowerSeries.C
abbrev rod (i:I):Port I:=liftInn (X i)

theorem belt_c (x:I→Port J)(p:Inn I):belt x (liftInn p)=lug x p:= tack_c (lug x).toRingHom _
theorem belt_x (x:I→Port J)(i:I):belt x (rod i)=x i:=by rw [belt_c];exact MvPolynomial.aeval_X ..
theorem belt_g (x:I→Port J):belt x PowerSeries.X=PowerSeries.X := tack_x ..
theorem belt_rose (x:I→Port J){f:Port I}(h:tiny f):belt x (rise f)=rise (belt x f):=tie_rise _ h

abbrev pin (i:I):Derivation ℝ (Port I) (Port I):=flight (pderiv i)

theorem pin_g (i:I):pin i (PowerSeries.X:Port I)=0:=by
 ext e :1; rw [flight_apply];simp only [PowerSeries.coeff_X, apply_ite, pderiv_one,map_zero,ite_self]
theorem pin_c (p:Inn I)(i:I):pin i (liftInn p)=liftInn (pderiv i p):=by
 ext e :1;rw [flight_apply,PowerSeries.coeff_C,PowerSeries.coeff_C];split_ifs <;> simp
 theorem pins (i j:I):pin i (rod j) = if i=j then 1 else 0:=by rw [pin_c];simp [pderiv_X,Pi.single_apply,eq_comm,apply_ite]

lemma pin_comm (i j:I)(f:Port I):pin i (pin j f)=pin j (pin i f):=by
 ext e :1;rw [flight_apply,flight_apply,flight_apply,flight_apply]
 generalize PowerSeries.coeff e f=p
 by_cases hij : i = j
 · subst j
   rfl
 ext m
 simp [coeff_pderiv, Finsupp.single_eq_of_ne, hij, Ne.symm hij, add_comm (Finsupp.single i 1),
   add_assoc, mul_comm, mul_left_comm, mul_assoc]

variable [Fintype I]
lemma lug_chain (x:I→Port J)(D:Derivation ℝ (Port J) (Port J))(p:Inn I):D (lug x p) = ∑ i,lug x (pderiv i p)* D (x i):=by
 induction p using MvPolynomial.induction_on with
 | C=>simp [lug]
 | add _ _ hi hj=>simp only [map_add,hi,hj,add_mul,Finset.sum_add_distrib]
 | mul_X p i h=>
    simp only [map_mul,Derivation.leibniz,lug, MvPolynomial.aeval_X, smul_eq_mul] at h ⊢
    rw [h]
    simp only [pderiv_X,Pi.single_apply,map_add,map_mul,MvPolynomial.aeval_X,apply_ite,map_zero,mul_one,mul_zero,ite_mul,zero_mul,add_mul,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_ite_eq,if_pos (mem_univ _)]
    simp only [mul_assoc]

theorem belt_chain (x:I→Port J)(j:J)(f:Port I): pin j (belt x f)= ∑ i,belt x (pin i f)*pin j (x i):=by
 -- compare with finite truncation at arbitrary e
 ext e :1
 let v : Port I:=tube (PowerSeries.C : Inn I→Cab (Inn I)) f e
 have he (i:ℕ)(hi:i≤e):tap i f=tap i v:=by
   unfold v;rw [←tubes _ _ _ _ hi,direct]
 have hh (i:ℕ)(hi:i≤e)(k:I): tap i (pin k f)=tap i (pin k v):=by
    change PowerSeries.coeff _ _=_; unfold tap at *;rw [flight_apply,flight_apply,he i hi]
 have hd: tap e (pin j (belt x f))=tap e (pin j (belt x v)):=by
    have h:tap e (belt x f)=tap e (belt x v):=rewire (lug x) e he; unfold tap at *;rw [flight_apply,flight_apply,h]
 have hr: tap e (∑ i,belt x (pin i f)*pin j (x i))=tap e (∑ i,belt x (pin i v)*pin j (x i)):=by
    unfold tap;rw [map_sum,map_sum];apply Finset.sum_congr rfl;intro i _;apply wired e _ (fun _ _=>rfl); intro k hk;exact rewire (lug x) k (fun l hl=> hh l (hl.trans hk) i)
 change tap e _=_; change _=tap e _;rw [hd,hr];congr 1
 have hp(i:J)(l:ℕ):pin i (PowerSeries.X^l)=0:=by induction l with
 | zero=>simp
 | succ l h=>rw [pow_succ,Derivation.leibniz,h,pin_g];simp
 have hp'(i:I)(l:ℕ):pin i (PowerSeries.X^l)=0:=by induction l with
 | zero=>simp
 | succ l h=>rw [pow_succ,Derivation.leibniz,h,pin_g];simp
 unfold v tube
 change pin j (belt x (∑ i∈_,liftInn (tap i f)*PowerSeries.X ^ i))=_
 simp_rw [map_sum, _root_.map_mul, Derivation.leibniz, _root_.map_pow,belt_g]
 simp_rw [belt_c,
    show (PowerSeries.C:Inn I→+*Cab (Inn I))=liftInn from rfl,pin_c,hp,hp',smul_zero,zero_add,smul_eq_mul,map_mul,belt_c,lug_chain,_root_.map_pow,belt_g,Finset.sum_mul,Finset.mul_sum]
 rw [Finset.sum_comm];apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl;intro k _;ring

section steady
/-! uniqueness of g-filtered homomorphisms by generators -/
variable [Fintype J]

def Steady (f:Port I→Port J):Prop:=∀ e a b,(∀ i≤e,tap i a=tap i b)→tap e (f a)=tap e (f b)

omit [Fintype I][Fintype J] in
lemma steady_belt (x:I→Port J):Steady (belt x):=fun _ _ _ h=>rewire _ _ h

omit [Fintype I][Fintype J] in
lemma steady_only (f g:Port I→ₐ[ℝ] Port J)(hf:Steady f)(hg:Steady g)(h:f PowerSeries.X=g PowerSeries.X)(hx:∀ i:I,f (rod i)=g (rod i)): f=g:=by
 apply AlgHom.ext;intro p;ext e :1
 let q:=tube (PowerSeries.C:Inn I→Cab (Inn I)) p e
 have he(i)(hi:i≤e):tap i p=tap i q:=by unfold q; rw [←tubes _ _ _ _ hi,direct]
 change tap e _=tap e _;rw [hf e _ _ he,hg e _ _ he];congr 1
 have ht (a:Inn I): f (liftInn a)=g (liftInn a):=by
   induction a using MvPolynomial.induction_on with
   | C a=>
     have he: liftInn (C a : Inn I)=algebraMap ℝ (Port I) a:=PowerSeries.algebraMap_apply.symm
     rw [he,f.commutes,g.commutes]
   | add _ _ hx hy=>rw [map_add,map_add,map_add,hx,hy]
   | mul_X p i ih=>
     rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,ih,hx i] -- defeq rod?
 unfold q tube;rw [map_sum,map_sum];apply Finset.sum_congr rfl;intro i _;rw [_root_.map_mul,_root_.map_mul,_root_.map_pow,_root_.map_pow,h,show PowerSeries.C (tap i p)=liftInn (tap i p) from rfl,ht]

omit [Fintype I][Fintype J] in
theorem switched (x:I→Port J)(y:J→Port K): (belt y).comp (belt x)=belt (fun i=>belt y (x i)):=by
 apply steady_only
 · intro e a b h;exact steady_belt y e _ _ (fun i hi=> steady_belt x i _ _ (fun l hl=>h l (hl.trans hi)))
 · apply steady_belt
 · change belt y (belt x PowerSeries.X)=_
   rw [belt_g,belt_g,belt_g]
 intro i;rw [AlgHom.comp_apply,belt_x,belt_x]

omit [Fintype I] in
theorem belt_id (f:Port I):belt rod f=f:=by
 have hh:belt (fun i:I=>rod i)=AlgHom.id ℝ (Port I):= steady_only _ _ (steady_belt _) (fun e a b h=>h e le_rfl) (belt_g _) (belt_x _)
 rw [hh];rfl

omit [Fintype I][Fintype J] in
lemma rim (x:I→Port J)(f:Port I):tap 0 (belt x f)=MvPolynomial.aeval (fun i=>tap 0 (x i)) (tap 0 f):=by
 change tap 0 (spool _ f)=_
 rw [ships]; simp only [zero_add,sum_range_one,Nat.sub_self,lug]
 generalize tap 0 f=p
 unfold tap
 simp_rw [PowerSeries.coeff_zero_eq_constantCoeff]
 induction p using MvPolynomial.induction_on with
 | C=>simp [PowerSeries.algebraMap_apply]
 | add _ _ ha hb=>simp only [map_add,ha,hb]
 | mul_X p i h=>
   change PowerSeries.constantCoeff (MvPolynomial.aeval x (p * X i)) = _
   change PowerSeries.constantCoeff (MvPolynomial.aeval x p) = _ at h
   simp only [map_mul,MvPolynomial.aeval_X,h]

end steady
end YM.RG08.Room
