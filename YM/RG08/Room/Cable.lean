import YM.RG08.Glyph.Mean

/-!
# Diagonal substitution of field polynomials into field-polynomial-valued series

Allows rescaled coordinate maps including nonlinear chart terms with nonzero g-order-zero
field linear map. Does NOT substitute g; keep adjacent change of coupling separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open scoped PowerSeries BigOperators Topology Classical
open Cloud

abbrev Cab (R:Type*)[CommRing R]:=PowerSeries R
abbrev tap {R : Type*}[CommRing R](e:ℕ)(v:Cab R):R:=PowerSeries.coeff e v

variable {R S T:Type*}[CommRing R][CommRing S][CommRing T]

def spool (b:R→S⟦X⟧) (f:R⟦X⟧):Cab S:= PowerSeries.mk (fun e=>∑ i∈Finset.range (e+1),tap (e-i) (b (tap i f)))

def tube (b:R→Cab S)(f:Cab R)(m:ℕ):Cab S:=∑ i∈Finset.range (m+1), b (tap i f)* PowerSeries.X ^ i

lemma ships (b:R→Cab S)(f:Cab R)(e:ℕ):tap e (spool b f)=∑ i∈Finset.range (e+1),tap (e-i) (b (tap i f)):=PowerSeries.coeff_mk ..

lemma tubes (b:R→Cab S)(f:Cab R)(e m:ℕ)(hm:e≤m):tap e (spool b f)=tap e (tube b f m):=by
 rw [ships,tube]; unfold tap;rw [map_sum]
 -- coeff_mul_X_pow'
 rw [← Finset.sum_subset (s₁:=Finset.range (e+1)) (s₂:=Finset.range (m+1)) (f:=fun i=> PowerSeries.coeff e (_ * PowerSeries.X ^ i)) (Finset.range_mono (by omega)) ?z]
 · apply Finset.sum_congr rfl; intro x hx; rw [PowerSeries.coeff_mul_X_pow', if_pos (by simpa using hx)]
 case z=>intro x _ hx;rw [PowerSeries.coeff_mul_X_pow',if_neg (by simp only [Finset.mem_range] at *;omega)]

lemma spool_zero (b:R→Cab S)(h:b 0=0):spool b 0=0:=by ext e :1; simp [tap,spool,h]
lemma spool_add (b:R→Cab S)(h:∀ x y,b (x+y)=b x+b y)(f g:Cab R):spool b (f+g)=spool b f+spool b g:=by ext e :1; simp only [spool,tap,PowerSeries.coeff_mk,map_add,h,Finset.sum_add_distrib]
lemma spool_sum {J:Type*}(s:Finset J)(b:R→Cab S)(hz:b 0=0)(h:∀ x y,b (x+y)=b x+b y)(f:J→Cab R):spool b (s.sum f)=s.sum (fun x=>spool b (f x)):=by
 induction s using Finset.induction_on with
 | empty=>rw [Finset.sum_empty,Finset.sum_empty,spool_zero _ hz]
 | insert i s hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi,spool_add b h,ih]
lemma spool_c (b:R→Cab S)(h:b 0=0)(x:R):spool b (PowerSeries.C x)=b x:=by
 ext e :1; change tap e (spool _ _)=_; rw [ships,Finset.sum_eq_single_of_mem 0 (by simp)]; · simp [tap];
 intro i _ hi; rw [show tap i (PowerSeries.C x)=0 by rw [tap,PowerSeries.coeff_C]; simp [hi]];simp [tap,h]

lemma spool_push (b:R→Cab S)(h:b 0=0)(f:Cab R)(n:ℕ):spool b (f* PowerSeries.X ^ n)=spool b f * PowerSeries.X ^ n:=by
 ext e :1;change tap e (spool _ _)=_;rw [ships,PowerSeries.coeff_mul_X_pow']
 by_cases hh:n≤e
 · rw [if_pos hh];change _=tap (e-n) (spool b f);rw [ships,←Nat.sub_add_cancel hh]
   have he:(e-n+n+1)=n+(e-n+1):=by omega
   rw [he,Finset.sum_range_add]
   simp only [Nat.add_sub_cancel_right]
   have hp(i:ℕ)(hi:i∈Finset.range n):tap (e-n+n-i) (b (tap i (f*PowerSeries.X^n)))=0:=by
      unfold tap;rw [PowerSeries.coeff_mul_X_pow',if_neg (Nat.not_le_of_gt (Finset.mem_range.mp hi)),h]; exact map_zero _
   rw [Finset.sum_eq_zero hp,zero_add];apply Finset.sum_congr rfl;intro i hi
   unfold tap;rw [PowerSeries.coeff_mul_X_pow',if_pos (by omega),Nat.add_sub_cancel_left,show e-n+n-(n+i)=e-n-i by omega]
 rw [if_neg hh]; apply Finset.sum_eq_zero; intro i hi; unfold tap; rw [PowerSeries.coeff_mul_X_pow',if_neg (by simp only [Finset.mem_range] at *;omega),h];exact map_zero _

lemma rewire (b:R→Cab S)(e:ℕ){f g:Cab R}(h:∀ i≤e,tap i f=tap i g):tap e (spool b f)=tap e (spool b g):=by
 rw [ships,ships]; apply Finset.sum_congr rfl; intro i hi; rw [h i (by simpa using hi)]

lemma wired {a b c d:Cab R}(e:ℕ)(h:∀ i≤e,tap i a=tap i b)(k:∀ i≤e,tap i c=tap i d):tap e (a*c)=tap e (b*d):=by
 unfold tap at *;rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul];exact Finset.sum_congr rfl (fun ⟨i,j⟩ hh=>by have hp:=Finset.mem_antidiagonal.mp hh; dsimp at *; rw [h i (by omega),k j (by omega)])

lemma direct (f:Cab R):spool (PowerSeries.C : R→Cab R) f=f:=by
 ext e :1;change tap e (spool _ _)=_;rw [ships,Finset.sum_eq_single_of_mem e (by simp)]; · simp [tap];
 intro i hi he; unfold tap; rw [PowerSeries.coeff_C]; rw [if_neg (by simp only [Finset.mem_range] at *;omega)]

-- finite polynomial input atoms & approximations
abbrev pump {R:Type*}[CommRing R](e:ℕ)(x:R):Cab R:=PowerSeries.C x * PowerSeries.X ^ e
lemma pump_times (e n:ℕ)(a c:R):pump e a*pump n c=pump (e+n) (a*c):=by unfold pump;rw [_root_.map_mul,pow_add];ring

lemma spool_mul (b:R→+*Cab S)(f g:Cab R):spool b (f*g)=spool b f*spool b g:=by
 ext e :1
 let v:=tube (PowerSeries.C : R→Cab R) f e
 let w:=tube (PowerSeries.C : R→Cab R) g e
 have he {f:Cab R}(i:ℕ)(hi:i≤e):tap i f=tap i (tube (PowerSeries.C : R→Cab R) f e):=by
   rw [←tubes _ _ _ _ hi,direct]
 have hu (i)(hi:i≤e):tap i f=tap i v:=he i hi;have hw (i)(hi:i≤e):tap i g=tap i w:=he i hi
 change tap e _=tap e _
 rw [rewire b e (fun i hi=>wired i (fun j hj=>hu j (hj.trans hi)) (fun j hj=>hw j (hj.trans hi))), wired (a:=spool b f) (c:=spool b g) e (fun i hi=>rewire b i (fun j hj=>hu j (hj.trans hi))) (fun i hi=>rewire b i (fun j hj=>hw j (hj.trans hi)))]
 change tap e (spool b ((∑ i∈Finset.range (e+1),pump i (tap i f))*(∑ i∈Finset.range (e+1),pump i (tap i g))))=tap e (spool b (∑ i∈Finset.range (e+1),pump i (tap i f)) *spool b (∑ i∈Finset.range (e+1),pump i (tap i g)))
 simp_rw [Finset.sum_mul,Finset.mul_sum,spool_sum _ b (map_zero _) (map_add _),Finset.sum_mul,Finset.mul_sum,pump_times]
 have hp {e:ℕ}{x:R} :spool b (pump e x)=b x*PowerSeries.X^e:=by rw [pump,spool_push _ (map_zero _),spool_c _ (map_zero _)]
 simp_rw [hp,_root_.map_mul,pow_add];congr 1; apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring

def tack (b:R→+*Cab S) : Cab R→+*Cab S where
 toFun:=spool b
 map_add':=spool_add _ (map_add _)
 map_mul':=spool_mul _
 map_one':=by simpa only [map_one] using spool_c b (map_zero _) (1:R)
 map_zero':= spool_zero _ (map_zero _)

lemma tack_x (b:R→+*Cab S) : tack b PowerSeries.X=PowerSeries.X:=by
 change spool b _=_
 simpa only [pow_one, one_mul, map_one,show spool b 1=1 from (tack b).map_one] using spool_push (S:=S) b (map_zero _) (1:Cab R) 1
lemma tack_c (b:R→+*Cab S)(a:R):tack b (PowerSeries.C a)=b a:=spool_c _ (map_zero _) _
lemma map_tack (b:S→+*T)(c:R→+*Cab S)(f:Cab R):PowerSeries.map b (tack c f)=tack ((PowerSeries.map b).comp c) f:=by
 ext e :1;rw [PowerSeries.coeff_map]; change b (tap e (spool c f))=tap e (spool _ f);rw [ships,ships,map_sum];congr! 4 with i _; -- maybe

section alg
variable [Algebra ℝ R][Algebra ℝ S]
def tie (b:R→ₐ[ℝ] Cab S):Cab R→ₐ[ℝ] Cab S:= AlgHom.mk' (show Cab R→+*Cab S from tack b.toRingHom) (fun r p=> by
 ext e :1;change tap e (spool b (r • p))=tap e (r • spool b p)
 rw [ships,show tap e (r • spool b p)=r • tap e (spool b p) from PowerSeries.coeff_smul ..,ships,Finset.smul_sum];apply Finset.sum_congr rfl; intro i hi
 unfold tap; rw [PowerSeries.coeff_smul,_root_.map_smul,PowerSeries.coeff_smul])

lemma tie_rise (b:R→ₐ[ℝ] Cab S){V:Cab R}(h:tiny V):tie b (rise V)=rise (tie b V):=by
 have hh:tiny (tie b V):=by
    unfold tiny at *; change tap 0 (spool b _)=_; simp [spool,tap,h]
 ext e :1
 have he:tap e (tie b (rise V))= tap e (tie b (rpol e V)):=rewire _ _ (fun i hi=>(coeff_rpol h hi).symm)
 change tap e _ = tap e _;rw [he]; unfold tap;rw [←coeff_rpol hh (le_refl e)]
 unfold rpol; simp_rw [map_sum,_root_.map_smul,_root_.map_pow]

end alg
end YM.RG08.Room
